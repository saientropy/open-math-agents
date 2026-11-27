import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_6

/-!
Proof of `Bugeaud06`'s ratio-floor sublacunary universal-density problem (Boshernitzan 1983,
Theorem 1.5, specialized to density modulo one via finite Hoeffding averaging + Fejér kernel).

Strategy:
1. Define the subexponential corridor `[nSeq k, nSeq k + k + 1)` with
   `nSeq (k + 1) = ⌈(1 + 2 / log (k + 2)) * (nSeq k + k + 1)⌉₊`.
   Every sequence `m` with `nSeq k ≤ m k < nSeq k + k + 1` is `StrictMono` and
   `IsGenuinelySublacunary` (with `c = 1`), while `nSeq (2 * K) + 2 * K ≤ C * exp (c * K)`
   for every `c > 0`.
2. On any block `B = [K, 2 * K)`, independent uniform averaging over the finite product
   `Fintype.piFinset` of corridors yields a finite Hoeffding bound `exp (-(ε^2 / 32) * K)`
   on deviations of `cos (2π h α p_k)` and `sin (2π h α p_k)` from their corridor means,
   while telescoping trig sums bound each corridor mean by `1 / (K * |sin (π h α)|)`.
3. Discretizing `α ∈ [0, 1]` at mesh `1 / N` (`N = O(nSeq (2 * K))`) beats the Hoeffding
   decay for large `K`, producing deterministic good blocks `B_j = [K_j, 2 * K_j)` indexed
   by `(H_j, D_j) = (Nat.unpair j) + (2, 2)`.
4. For any irrational `ξ`, target `x0`, and radius `r > 0`, evaluating the Fejér kernel
   `F_H(ξ * m k - x0)` on a sufficiently late block `B_j` forces its average `≥ 1 / 2 > 1 / 4`,
   yielding `k ∈ B_j` with `dist (↑(ξ * m k)) (↑x0) < r`.
-/

namespace OMABugeaud106

open Filter Finset

/- ### Part 1: Corridor sequence `nSeq` and its growth bounds -/

noncomputable def nSeq : ℕ → ℕ
  | 0 => 2
  | k + 1 => ⌈(1 + 2 / Real.log ((k + 2 : ℕ) : ℝ)) * ((nSeq k + k + 1 : ℕ) : ℝ)⌉₊

lemma log_add_two_pos (k : ℕ) : 0 < Real.log ((k + 2 : ℕ) : ℝ) := by
  apply Real.log_pos
  have : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ k + 2)
  linarith

lemma log_ge_one_of_ge_three {k : ℕ} (hk : 3 ≤ k) : (1 : ℝ) ≤ Real.log ((k + 2 : ℕ) : ℝ) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h5 : (5 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 5 ≤ k + 2)
  linarith [Real.exp_one_lt_d9]

lemma nSeq_succ_ge (k : ℕ) : nSeq k + k + 1 ≤ nSeq (k + 1) := by
  have hlog : 0 < Real.log ((k + 2 : ℕ) : ℝ) := log_add_two_pos k
  have h1 : ((nSeq k + k + 1 : ℕ) : ℝ) ≤
      (1 + 2 / Real.log ((k + 2 : ℕ) : ℝ)) * ((nSeq k + k + 1 : ℕ) : ℝ) := by
    have hdiv : 0 ≤ 2 / Real.log ((k + 2 : ℕ) : ℝ) := by positivity
    nlinarith
  have h2 : ((nSeq k + k + 1 : ℕ) : ℝ) ≤ (nSeq (k + 1) : ℝ) :=
    h1.trans (Nat.le_ceil _)
  exact_mod_cast h2

lemma nSeq_ge_two (k : ℕ) : 2 ≤ nSeq k := by
  induction k with
  | zero => simp [nSeq]
  | succ k ih => have := nSeq_succ_ge k; omega

lemma nSeq_mono : Monotone nSeq := by
  refine monotone_nat_of_le_succ fun k => ?_
  have := nSeq_succ_ge k; omega

lemma two_mul_nSeq_ge (k : ℕ) : k * (k + 1) + 4 ≤ 2 * nSeq k := by
  induction k with
  | zero => simp [nSeq]
  | succ k ih =>
    have h := nSeq_succ_ge k
    have hmul : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by ring
    omega

lemma strictMono_of_corridor {m : ℕ → ℕ} (hm : ∀ k, nSeq k ≤ m k ∧ m k < nSeq k + k + 1) :
    StrictMono m := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  have h1 := (hm k).2
  have h2 := nSeq_succ_ge k
  have h3 := (hm (k + 1)).1
  omega

lemma isGenuinelySublacunary_of_corridor {m : ℕ → ℕ}
    (hm : ∀ k, nSeq k ≤ m k ∧ m k < nSeq k + k + 1) :
    Bugeaud06.IsGenuinelySublacunary m := by
  refine ⟨1, one_pos, ?_⟩
  filter_upwards [eventually_ge_atTop 3] with k hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hlogk_pos : 0 < Real.log (k : ℝ) := by
    apply Real.log_pos
    have : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hlogk2_pos : 0 < Real.log ((k + 2 : ℕ) : ℝ) := log_add_two_pos k
  have hsq : ((k + 2 : ℕ) : ℝ) ≤ (k : ℝ) ^ 2 := by
    have : k + 2 ≤ k * k := by nlinarith
    have : ((k + 2 : ℕ) : ℝ) ≤ ((k * k : ℕ) : ℝ) := by exact_mod_cast this
    simpa [sq, Nat.cast_mul] using this
  have hlog_le : Real.log ((k + 2 : ℕ) : ℝ) ≤ 2 * Real.log (k : ℝ) := by
    calc Real.log ((k + 2 : ℕ) : ℝ) ≤ Real.log ((k : ℝ) ^ 2) :=
          Real.log_le_log (by positivity) hsq
      _ = 2 * Real.log (k : ℝ) := by rw [Real.log_pow]; ring
  have hdiv_le : 1 / Real.log (k : ℝ) ≤ 2 / Real.log ((k + 2 : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hlogk_pos hlogk2_pos]
    linarith
  have hmk_pos : (0 : ℝ) < (m k : ℝ) := by
    have := (hm k).1; have := nSeq_ge_two k; exact_mod_cast (by omega : 0 < m k)
  have hmk_le : (m k : ℝ) ≤ ((nSeq k + k + 1 : ℕ) : ℝ) := by
    have := (hm k).2; exact_mod_cast le_of_lt this
  have hmk1_ge : (nSeq (k + 1) : ℝ) ≤ (m (k + 1) : ℝ) := by
    exact_mod_cast (hm (k + 1)).1
  have hceil : (1 + 2 / Real.log ((k + 2 : ℕ) : ℝ)) * ((nSeq k + k + 1 : ℕ) : ℝ) ≤
      (nSeq (k + 1) : ℝ) := Nat.le_ceil _
  rw [le_div_iff₀ hmk_pos]
  calc (1 + 1 / Real.log (k : ℝ)) * (m k : ℝ)
      ≤ (1 + 2 / Real.log ((k + 2 : ℕ) : ℝ)) * ((nSeq k + k + 1 : ℕ) : ℝ) := by
        apply mul_le_mul (by linarith) hmk_le (le_of_lt hmk_pos) (by positivity)
    _ ≤ (nSeq (k + 1) : ℝ) := hceil
    _ ≤ (m (k + 1) : ℝ) := hmk1_ge

lemma nSeq_succ_le_exp {k : ℕ} (hk : 3 ≤ k) :
    (nSeq (k + 1) : ℝ) ≤ Real.exp (16 / Real.log ((k + 2 : ℕ) : ℝ)) * (nSeq k : ℝ) := by
  set L : ℝ := Real.log ((k + 2 : ℕ) : ℝ)
  have hL1 : 1 ≤ L := log_ge_one_of_ge_three hk
  have hLpos : 0 < L := by linarith
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hn_pos : (0 : ℝ) < (nSeq k : ℝ) := by
    have := nSeq_ge_two k; exact_mod_cast (by omega : 0 < nSeq k)
  have hL_le_2k : L ≤ 2 * (k : ℝ) := by
    have h1 : L ≤ ((k + 2 : ℕ) : ℝ) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((k + 2 : ℕ) : ℝ) by positivity)
      linarith
    have h2 : ((k + 2 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast (by omega : k + 2 ≤ 2 * k)
    linarith
  have hinvk : 1 / (k : ℝ) ≤ 2 / L := by
    rw [div_le_div_iff₀ hk_pos hLpos]; linarith
  have hk1_le : ((k + 1 : ℕ) : ℝ) ≤ (2 / (k : ℝ)) * (nSeq k : ℝ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hk_pos]
    have htri := two_mul_nSeq_ge k
    have htriR : ((k * (k + 1) : ℕ) : ℝ) ≤ ((2 * nSeq k : ℕ) : ℝ) := by
      exact_mod_cast (by omega : k * (k + 1) ≤ 2 * nSeq k)
    push_cast at htriR ⊢
    linarith
  have h4L : 2 / (k : ℝ) ≤ 4 / L := by
    rw [div_le_div_iff₀ hk_pos hLpos]; linarith
  have hone_le : (1 : ℝ) ≤ (2 / L) * (nSeq k : ℝ) := by
    have htri := two_mul_nSeq_ge k
    have hnk : (k : ℝ) ≤ (nSeq k : ℝ) := by
      have : k ≤ nSeq k := by nlinarith
      exact_mod_cast this
    have h2k : (1 : ℝ) ≤ (2 / L) * (k : ℝ) := by
      rw [div_mul_eq_mul_div, one_le_div hLpos]; linarith
    nlinarith
  have hceil_lt : (nSeq (k + 1) : ℝ) ≤
      (1 + 2 / L) * ((nSeq k + k + 1 : ℕ) : ℝ) + 1 := by
    have hnonneg : 0 ≤ (1 + 2 / L) * ((nSeq k + k + 1 : ℕ) : ℝ) := by positivity
    exact le_of_lt (Nat.ceil_lt_add_one hnonneg)
  have hsum_le : ((nSeq k + k + 1 : ℕ) : ℝ) ≤ (1 + 4 / L) * (nSeq k : ℝ) := by
    have hsplit : ((nSeq k + k + 1 : ℕ) : ℝ) = (nSeq k : ℝ) + ((k + 1 : ℕ) : ℝ) := by
      push_cast; ring
    rw [hsplit]
    nlinarith
  have hinvL2 : 1 / L ^ 2 ≤ 1 / L := by
    rw [div_le_div_iff₀ (by positivity) hLpos]
    nlinarith
  have hprod : (1 + 2 / L) * (1 + 4 / L) + 2 / L ≤ 1 + 16 / L := by
    have hexp : (1 + 2 / L) * (1 + 4 / L) + 2 / L = 1 + 8 / L + 8 * (1 / L ^ 2) := by
      field_simp; ring
    have hsum16 : 1 + 8 / L + 8 * (1 / L) = 1 + 16 / L := by ring
    rw [hexp]
    linarith
  calc (nSeq (k + 1) : ℝ)
      ≤ (1 + 2 / L) * ((nSeq k + k + 1 : ℕ) : ℝ) + 1 := hceil_lt
    _ ≤ (1 + 2 / L) * ((1 + 4 / L) * (nSeq k : ℝ)) + (2 / L) * (nSeq k : ℝ) := by
        have h12 : 0 ≤ 1 + 2 / L := by positivity
        nlinarith
    _ = ((1 + 2 / L) * (1 + 4 / L) + 2 / L) * (nSeq k : ℝ) := by ring
    _ ≤ (1 + 16 / L) * (nSeq k : ℝ) := mul_le_mul_of_nonneg_right hprod (le_of_lt hn_pos)
    _ ≤ Real.exp (16 / L) * (nSeq k : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (16 / L)]) (le_of_lt hn_pos)

lemma nSeq_subexp {c : ℝ} (hc : 0 < c) :
    ∃ C > 0, ∀ K : ℕ, ((nSeq (2 * K) + 2 * K : ℕ) : ℝ) ≤ C * Real.exp (c * (K : ℝ)) := by
  let M : ℕ := max 3 ⌈Real.exp (32 / c)⌉₊
  have hM3 : 3 ≤ M := le_max_left _ _
  have hMlog : 32 / c ≤ Real.log ((M + 2 : ℕ) : ℝ) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h1 : Real.exp (32 / c) ≤ (⌈Real.exp (32 / c)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp (32 / c)⌉₊ : ℝ) ≤ (M : ℝ) := by exact_mod_cast le_max_right 3 _
    have h3 : (M : ℝ) ≤ ((M + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : M ≤ M + 2)
    linarith
  have hstep : ∀ j : ℕ, (nSeq (M + j) : ℝ) ≤ (nSeq M : ℝ) * Real.exp ((c / 2) * (j : ℝ)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hge3 : 3 ≤ M + j := by omega
      have h1 := nSeq_succ_le_exp hge3
      have hlog_ge : Real.log ((M + 2 : ℕ) : ℝ) ≤ Real.log ((M + j + 2 : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast (by omega : M + 2 ≤ M + j + 2))
      have h16 : 16 / Real.log ((M + j + 2 : ℕ) : ℝ) ≤ c / 2 := by
        have hpos : 0 < Real.log ((M + j + 2 : ℕ) : ℝ) := log_add_two_pos (M + j)
        rw [div_le_div_iff₀ hpos two_pos]
        have h32 : 32 / c ≤ Real.log ((M + j + 2 : ℕ) : ℝ) := hMlog.trans hlog_ge
        rw [div_le_iff₀ hc] at h32
        linarith
      have hmul : (nSeq (M + (j + 1)) : ℝ) ≤
          Real.exp (c / 2) * (nSeq (M + j) : ℝ) := by
        have : M + (j + 1) = M + j + 1 := by omega
        rw [this]
        exact h1.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h16) (by positivity))
      calc (nSeq (M + (j + 1)) : ℝ)
          ≤ Real.exp (c / 2) * ((nSeq M : ℝ) * Real.exp ((c / 2) * (j : ℝ))) :=
            hmul.trans (mul_le_mul_of_nonneg_left ih (Real.exp_nonneg _))
        _ = (nSeq M : ℝ) * (Real.exp (c / 2) * Real.exp ((c / 2) * (j : ℝ))) := by ring
        _ = (nSeq M : ℝ) * Real.exp ((c / 2) * ((j + 1 : ℕ) : ℝ)) := by
            rw [← Real.exp_add]; congr 2; push_cast; ring
  let C : ℝ := 2 * ((nSeq (2 * M) + 2 * M : ℕ) : ℝ)
  have hCpos : 0 < C := by
    have := nSeq_ge_two (2 * M)
    have : (0 : ℝ) < ((nSeq (2 * M) + 2 * M : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < nSeq (2 * M) + 2 * M)
    linarith
  refine ⟨C, hCpos, fun K => ?_⟩
  by_cases hKM : K ≤ M
  · have h1 : nSeq (2 * K) + 2 * K ≤ nSeq (2 * M) + 2 * M := by
      have := nSeq_mono (show 2 * K ≤ 2 * M by omega); omega
    have h1R : ((nSeq (2 * K) + 2 * K : ℕ) : ℝ) ≤ ((nSeq (2 * M) + 2 * M : ℕ) : ℝ) := by
      exact_mod_cast h1
    have hexp1 : (1 : ℝ) ≤ Real.exp (c * (K : ℝ)) := Real.one_le_exp (by positivity)
    have : ((nSeq (2 * M) + 2 * M : ℕ) : ℝ) ≤ C := by dsimp [C]; linarith
    nlinarith
  · have hKM' : M ≤ 2 * K := by omega
    have h2K_le : 2 * K ≤ nSeq (2 * K) := by
      have htri := two_mul_nSeq_ge (2 * K)
      have : 2 * K ≥ 2 := by omega
      nlinarith
    have h1 : ((nSeq (2 * K) + 2 * K : ℕ) : ℝ) ≤ 2 * (nSeq (2 * K) : ℝ) := by
      exact_mod_cast (by omega : nSeq (2 * K) + 2 * K ≤ 2 * nSeq (2 * K))
    have h2 : (nSeq (2 * K) : ℝ) ≤ (nSeq M : ℝ) * Real.exp ((c / 2) * ((2 * K - M : ℕ) : ℝ)) := by
      have heq : M + (2 * K - M) = 2 * K := by omega
      simpa [heq] using hstep (2 * K - M)
    have hexp_le : Real.exp ((c / 2) * ((2 * K - M : ℕ) : ℝ)) ≤ Real.exp (c * (K : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hsub : ((2 * K - M : ℕ) : ℝ) ≤ 2 * (K : ℝ) := by
        exact_mod_cast (by omega : 2 * K - M ≤ 2 * K)
      nlinarith
    have hM_le_C : 2 * (nSeq M : ℝ) ≤ C := by
      dsimp [C]
      have : nSeq M ≤ nSeq (2 * M) + 2 * M := by
        have := nSeq_mono (show M ≤ 2 * M by omega); omega
      have : (nSeq M : ℝ) ≤ ((nSeq (2 * M) + 2 * M : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    calc ((nSeq (2 * K) + 2 * K : ℕ) : ℝ)
        ≤ 2 * (nSeq (2 * K) : ℝ) := h1
      _ ≤ 2 * ((nSeq M : ℝ) * Real.exp ((c / 2) * ((2 * K - M : ℕ) : ℝ))) := by linarith
      _ = (2 * (nSeq M : ℝ)) * Real.exp ((c / 2) * ((2 * K - M : ℕ) : ℝ)) := by ring
      _ ≤ C * Real.exp (c * (K : ℝ)) :=
          mul_le_mul hM_le_C hexp_le (Real.exp_nonneg _) (le_of_lt hCpos)

/- ### Part 2: Elementary exponential, telescoping trig, and Fejér kernel -/

lemma exp_le_quad {u : ℝ} (hu : |u| ≤ 1 / 2) : Real.exp u ≤ 1 + u + 2 * u ^ 2 := by
  have hu1 : -(1 / 2) ≤ u ∧ u ≤ 1 / 2 := abs_le.mp hu
  have h1u : 0 < 1 - u := by linarith
  have hle : 1 - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
  rw [Real.exp_neg] at hle
  have hinv : Real.exp u ≤ 1 / (1 - u) := by
    rw [le_div_iff₀ h1u]
    have hmul := mul_le_mul_of_nonneg_left hle (Real.exp_nonneg u)
    rw [mul_inv_cancel₀ (Real.exp_ne_zero u)] at hmul
    linarith
  have hpoly : 1 / (1 - u) ≤ 1 + u + 2 * u ^ 2 := by
    rw [div_le_iff₀ h1u]
    nlinarith [sq_nonneg u]
  exact hinv.trans hpoly

lemma two_sin_mul_cos_eq (a b : ℝ) :
    2 * Real.sin a * Real.cos b = Real.sin (b + a) - Real.sin (b - a) := by
  rw [Real.sin_add, Real.sin_sub]; ring

lemma two_sin_mul_sin_eq (a b : ℝ) :
    2 * Real.sin a * Real.sin b = Real.cos (b - a) - Real.cos (b + a) := by
  rw [Real.cos_sub, Real.cos_add]; ring

lemma cos_range_sum_bound (n W : ℕ) (θ : ℝ) (hsin : Real.sin (Real.pi * θ) ≠ 0) :
    |∑ j ∈ Finset.range W, Real.cos (2 * Real.pi * θ * ((n + j : ℕ) : ℝ))| ≤
      1 / |Real.sin (Real.pi * θ)| := by
  have hpos : 0 < |Real.sin (Real.pi * θ)| := abs_pos.mpr hsin
  rw [le_div_iff₀ hpos, ← abs_mul]
  have htel : 2 * Real.sin (Real.pi * θ) *
      ∑ j ∈ Finset.range W, Real.cos (2 * Real.pi * θ * ((n + j : ℕ) : ℝ)) =
      Real.sin (Real.pi * θ * (2 * ((n + W : ℕ) : ℝ) - 1)) -
      Real.sin (Real.pi * θ * (2 * (n : ℝ) - 1)) := by
    rw [Finset.mul_sum]
    have hterm : ∀ j : ℕ,
        2 * Real.sin (Real.pi * θ) * Real.cos (2 * Real.pi * θ * ((n + j : ℕ) : ℝ)) =
        Real.sin (Real.pi * θ * (2 * ((n + (j + 1) : ℕ) : ℝ) - 1)) -
        Real.sin (Real.pi * θ * (2 * ((n + j : ℕ) : ℝ) - 1)) := by
      intro j
      rw [two_sin_mul_cos_eq]
      congr 1 <;> (congr 1; push_cast; ring)
    simp_rw [hterm]
    rw [Finset.sum_range_sub (fun j => Real.sin (Real.pi * θ * (2 * ((n + j : ℕ) : ℝ) - 1))) W]
    simp
  have habs : |2 * Real.sin (Real.pi * θ) *
      ∑ j ∈ Finset.range W, Real.cos (2 * Real.pi * θ * ((n + j : ℕ) : ℝ))| ≤ 2 := by
    rw [htel]
    calc |Real.sin _ - Real.sin _| ≤ |Real.sin _| + |Real.sin _| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
      _ = 2 := by norm_num
  have h2 : |2 * Real.sin (Real.pi * θ) *
      ∑ j ∈ Finset.range W, Real.cos (2 * Real.pi * θ * ((n + j : ℕ) : ℝ))| =
      2 * |(∑ j ∈ Finset.range W, Real.cos (2 * Real.pi * θ * ((n + j : ℕ) : ℝ))) *
      Real.sin (Real.pi * θ)| := by
    rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm (Real.sin _)]
  linarith

lemma sin_range_sum_bound (n W : ℕ) (θ : ℝ) (hsin : Real.sin (Real.pi * θ) ≠ 0) :
    |∑ j ∈ Finset.range W, Real.sin (2 * Real.pi * θ * ((n + j : ℕ) : ℝ))| ≤
      1 / |Real.sin (Real.pi * θ)| := by
  have hpos : 0 < |Real.sin (Real.pi * θ)| := abs_pos.mpr hsin
  rw [le_div_iff₀ hpos, ← abs_mul]
  have htel : 2 * Real.sin (Real.pi * θ) *
      ∑ j ∈ Finset.range W, Real.sin (2 * Real.pi * θ * ((n + j : ℕ) : ℝ)) =
      -(Real.cos (Real.pi * θ * (2 * ((n + W : ℕ) : ℝ) - 1)) -
        Real.cos (Real.pi * θ * (2 * (n : ℝ) - 1))) := by
    rw [Finset.mul_sum]
    have hterm : ∀ j : ℕ,
        2 * Real.sin (Real.pi * θ) * Real.sin (2 * Real.pi * θ * ((n + j : ℕ) : ℝ)) =
        -(Real.cos (Real.pi * θ * (2 * ((n + (j + 1) : ℕ) : ℝ) - 1)) -
          Real.cos (Real.pi * θ * (2 * ((n + j : ℕ) : ℝ) - 1))) := by
      intro j
      rw [two_sin_mul_sin_eq]
      have h1 : 2 * Real.pi * θ * ((n + j : ℕ) : ℝ) - Real.pi * θ =
          Real.pi * θ * (2 * ((n + j : ℕ) : ℝ) - 1) := by ring
      have h2 : 2 * Real.pi * θ * ((n + j : ℕ) : ℝ) + Real.pi * θ =
          Real.pi * θ * (2 * ((n + (j + 1) : ℕ) : ℝ) - 1) := by push_cast; ring
      rw [h1, h2]; ring
    simp_rw [hterm, Finset.sum_neg_distrib]
    congr 1
    rw [Finset.sum_range_sub (fun j => Real.cos (Real.pi * θ * (2 * ((n + j : ℕ) : ℝ) - 1))) W]
    simp
  have habs : |2 * Real.sin (Real.pi * θ) *
      ∑ j ∈ Finset.range W, Real.sin (2 * Real.pi * θ * ((n + j : ℕ) : ℝ))| ≤ 2 := by
    rw [htel, abs_neg]
    calc |Real.cos _ - Real.cos _| ≤ |Real.cos _| + |Real.cos _| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
      _ = 2 := by norm_num
  have h2 : |2 * Real.sin (Real.pi * θ) *
      ∑ j ∈ Finset.range W, Real.sin (2 * Real.pi * θ * ((n + j : ℕ) : ℝ))| =
      2 * |(∑ j ∈ Finset.range W, Real.sin (2 * Real.pi * θ * ((n + j : ℕ) : ℝ))) *
      Real.sin (Real.pi * θ)| := by
    rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm (Real.sin _)]
  linarith

noncomputable def fejer (H : ℕ) (t : ℝ) : ℝ :=
  1 + 2 * ∑ h ∈ Finset.Ico 1 H, (1 - (h : ℝ) / (H : ℝ)) * Real.cos (2 * Real.pi * (h : ℝ) * t)

lemma dirichlet_trig_id (H : ℕ) (t : ℝ) :
    (1 - Real.cos (2 * Real.pi * t)) *
      (1 + 2 * ∑ h ∈ Finset.Ico 1 (H + 1), Real.cos (2 * Real.pi * (h : ℝ) * t)) =
      Real.cos (2 * Real.pi * (H : ℝ) * t) - Real.cos (2 * Real.pi * ((H + 1 : ℕ) : ℝ) * t) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ H + 1)]
    have hsplit : (1 - Real.cos (2 * Real.pi * t)) *
        (1 + 2 * (∑ h ∈ Finset.Ico 1 (H + 1), Real.cos (2 * Real.pi * (h : ℝ) * t) +
          Real.cos (2 * Real.pi * ((H + 1 : ℕ) : ℝ) * t))) =
        (1 - Real.cos (2 * Real.pi * t)) *
          (1 + 2 * ∑ h ∈ Finset.Ico 1 (H + 1), Real.cos (2 * Real.pi * (h : ℝ) * t)) +
        (1 - Real.cos (2 * Real.pi * t)) * (2 * Real.cos (2 * Real.pi * ((H + 1 : ℕ) : ℝ) * t)) := by
      ring
    rw [hsplit, ih]
    have hcos : 2 * Real.cos (2 * Real.pi * t) * Real.cos (2 * Real.pi * ((H + 1 : ℕ) : ℝ) * t) =
        Real.cos (2 * Real.pi * ((H + 2 : ℕ) : ℝ) * t) +
        Real.cos (2 * Real.pi * (H : ℝ) * t) := by
      have h1 : Real.cos (2 * Real.pi * ((H + 1 : ℕ) : ℝ) * t + 2 * Real.pi * t) +
          Real.cos (2 * Real.pi * ((H + 1 : ℕ) : ℝ) * t - 2 * Real.pi * t) =
          2 * Real.cos (2 * Real.pi * t) * Real.cos (2 * Real.pi * ((H + 1 : ℕ) : ℝ) * t) := by
        rw [Real.cos_add, Real.cos_sub]; ring
      rw [← h1]
      congr 1 <;> (congr 1; push_cast; ring)
    have hcast : ((H + 1 + 1 : ℕ) : ℝ) = ((H + 2 : ℕ) : ℝ) := by norm_cast
    rw [hcast]
    linarith

lemma fejer_scaled_id (H : ℕ) (t : ℝ) :
    (1 - Real.cos (2 * Real.pi * t)) *
      ((H : ℝ) + 2 * ∑ h ∈ Finset.Ico 1 H, ((H : ℝ) - (h : ℝ)) * Real.cos (2 * Real.pi * (h : ℝ) * t)) =
      1 - Real.cos (2 * Real.pi * (H : ℝ) * t) := by
  induction H with
  | zero => simp
  | succ H ih =>
    have hdiff : ((H + 1 : ℕ) : ℝ) +
        2 * ∑ h ∈ Finset.Ico 1 (H + 1), (((H + 1 : ℕ) : ℝ) - (h : ℝ)) * Real.cos (2 * Real.pi * (h : ℝ) * t) =
        ((H : ℝ) + 2 * ∑ h ∈ Finset.Ico 1 H, ((H : ℝ) - (h : ℝ)) * Real.cos (2 * Real.pi * (h : ℝ) * t)) +
        (1 + 2 * ∑ h ∈ Finset.Ico 1 (H + 1), Real.cos (2 * Real.pi * (h : ℝ) * t)) := by
      cases H with
      | zero => simp
      | succ m =>
        rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ m + 1)]
        have htop : (((m + 1 + 1 : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ)) = 1 := by push_cast; ring
        rw [htop, one_mul]
        rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ m + 1)]
        have hsum : ∑ h ∈ Finset.Ico 1 (m + 1),
            (((m + 1 + 1 : ℕ) : ℝ) - (h : ℝ)) * Real.cos (2 * Real.pi * (h : ℝ) * t) =
            (∑ h ∈ Finset.Ico 1 (m + 1), (((m + 1 : ℕ) : ℝ) - (h : ℝ)) * Real.cos (2 * Real.pi * (h : ℝ) * t)) +
            (∑ h ∈ Finset.Ico 1 (m + 1), Real.cos (2 * Real.pi * (h : ℝ) * t)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun h _ => ?_
          push_cast; ring
        rw [hsum]
        push_cast; ring
    rw [hdiff, mul_add, ih, dirichlet_trig_id]
    ring

lemma fejer_identity {H : ℕ} (hH : 1 ≤ H) (t : ℝ) :
    (H : ℝ) * (Real.sin (Real.pi * t)) ^ 2 * fejer H t = (Real.sin (Real.pi * (H : ℝ) * t)) ^ 2 := by
  have hHpos : (H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : (H : ℝ) * fejer H t =
      (H : ℝ) + 2 * ∑ h ∈ Finset.Ico 1 H, ((H : ℝ) - (h : ℝ)) * Real.cos (2 * Real.pi * (h : ℝ) * t) := by
    simp only [fejer, mul_add, mul_one]
    congr 1
    rw [← mul_assoc, mul_comm (H : ℝ) 2, mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    field_simp
  have hsin1 : 2 * (Real.sin (Real.pi * t)) ^ 2 = 1 - Real.cos (2 * Real.pi * t) := by
    have := Real.cos_two_mul (Real.pi * t)
    have hsq := Real.sin_sq_add_cos_sq (Real.pi * t)
    have heq : 2 * (Real.pi * t) = 2 * Real.pi * t := by ring
    rw [heq] at this
    linarith
  have hsin2 : 2 * (Real.sin (Real.pi * (H : ℝ) * t)) ^ 2 = 1 - Real.cos (2 * Real.pi * (H : ℝ) * t) := by
    have := Real.cos_two_mul (Real.pi * (H : ℝ) * t)
    have hsq := Real.sin_sq_add_cos_sq (Real.pi * (H : ℝ) * t)
    have heq : 2 * (Real.pi * (H : ℝ) * t) = 2 * Real.pi * (H : ℝ) * t := by ring
    rw [heq] at this
    linarith
  have hid := fejer_scaled_id H t
  rw [← h1, ← hsin1, ← hsin2] at hid
  linarith

lemma fejer_le_of_sin_ge {H : ℕ} (hH : 1 ≤ H) {t δ : ℝ} (hδ : 0 < δ)
    (hsin : 2 * δ ≤ |Real.sin (Real.pi * t)|) :
    fejer H t ≤ 1 / (4 * (H : ℝ) * δ ^ 2) := by
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have hsin_sq : 4 * δ ^ 2 ≤ (Real.sin (Real.pi * t)) ^ 2 := by
    have hsq := sq_le_sq.mpr (show |2 * δ| ≤ |Real.sin (Real.pi * t)| by
      rwa [abs_of_pos (by linarith)])
    nlinarith
  have hden_pos : 0 < (H : ℝ) * (Real.sin (Real.pi * t)) ^ 2 := by nlinarith [sq_pos_of_pos hδ]
  have hid := fejer_identity hH t
  have hfeq : fejer H t = (Real.sin (Real.pi * (H : ℝ) * t)) ^ 2 /
      ((H : ℝ) * (Real.sin (Real.pi * t)) ^ 2) := by
    rw [eq_div_iff (ne_of_gt hden_pos)]
    linarith
  rw [hfeq]
  calc (Real.sin (Real.pi * (H : ℝ) * t)) ^ 2 / ((H : ℝ) * (Real.sin (Real.pi * t)) ^ 2)
      ≤ 1 / ((H : ℝ) * (Real.sin (Real.pi * t)) ^ 2) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hden_pos)
        exact Real.sin_sq_le_one _
    _ ≤ 1 / (4 * (H : ℝ) * δ ^ 2) := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith

lemma abs_sub_round_lt_of_sin_lt {t δ : ℝ} (_hδ : 0 < δ)
    (hsin : |Real.sin (Real.pi * t)| < 2 * δ) :
    |t - round t| < δ := by
  set u : ℝ := t - round t
  have hu : |u| ≤ 1 / 2 := abs_sub_round t
  have hsin_eq : |Real.sin (Real.pi * u)| = |Real.sin (Real.pi * t)| := by
    have harg : Real.pi * t = Real.pi * u + (round t : ℤ) * Real.pi := by
      dsimp [u]; ring
    rw [harg, Real.sin_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  have hsin_abs : |Real.sin (Real.pi * u)| = Real.sin (Real.pi * |u|) := by
    by_cases h0 : 0 ≤ u
    · rw [abs_of_nonneg h0, abs_of_nonneg]
      apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      have : u ≤ 1 / 2 := (abs_le.mp hu).2
      nlinarith [Real.pi_pos]
    · have h0' : u < 0 := lt_of_not_ge h0
      have hneg : Real.sin (Real.pi * |u|) = -Real.sin (Real.pi * u) := by
        rw [abs_of_neg h0', mul_neg, Real.sin_neg]
      have hnonneg : 0 ≤ Real.sin (Real.pi * |u|) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        have : |u| ≤ 1 / 2 := hu
        nlinarith [Real.pi_pos]
      rw [hneg, abs_of_nonpos (by linarith)]
  have hmul := Real.mul_le_sin (x := Real.pi * |u|) (by positivity) (by nlinarith [Real.pi_pos])
  have h2u : 2 / Real.pi * (Real.pi * |u|) = 2 * |u| := by
    field_simp [ne_of_gt Real.pi_pos]
  rw [h2u] at hmul
  linarith

/- ### Part 3: Finite Hoeffding bound on `Fintype.piFinset` -/

lemma finite_hoeffding_upper {K : ℕ} (_hK : 0 < K)
    (S : Fin K → Finset ℕ) (hS : ∀ k, (S k).Nonempty)
    (f : Fin K → ℕ → ℝ) (hf : ∀ k x, |f k x| ≤ 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    let μ : Fin K → ℝ := fun k => (∑ x ∈ S k, f k x) / ((S k).card : ℝ)
    let Ω : Finset (Fin K → ℕ) := Fintype.piFinset S
    ((Ω.filter (fun p => ε * (K : ℝ) ≤ ∑ k : Fin K, (f k (p k) - μ k))).card : ℝ) ≤
      (Ω.card : ℝ) * Real.exp (-(ε ^ 2 / 32) * (K : ℝ)) := by
  intro μ Ω
  let lam : ℝ := ε / 16
  have hlam0 : 0 < lam := by dsimp [lam]; linarith
  have hlam14 : lam ≤ 1 / 4 := by dsimp [lam]; linarith
  have hSpos : ∀ k, (0 : ℝ) < ((S k).card : ℝ) := fun k =>
    Nat.cast_pos.mpr (Finset.card_pos.mpr (hS k))
  have hμ_abs : ∀ k, |μ k| ≤ 1 := by
    intro k
    dsimp [μ]
    rw [abs_div, abs_of_pos (hSpos k), div_le_one (hSpos k)]
    calc |∑ x ∈ S k, f k x| ≤ ∑ x ∈ S k, |f k x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ S k, (1 : ℝ) := Finset.sum_le_sum (fun x _ => hf k x)
      _ = ((S k).card : ℝ) := by simp
  have hone_coord : ∀ k : Fin K,
      ∑ x ∈ S k, Real.exp (lam * (f k x - μ k)) ≤
        ((S k).card : ℝ) * Real.exp (8 * lam ^ 2) := by
    intro k
    have hpt : ∀ x ∈ S k, Real.exp (lam * (f k x - μ k)) ≤
        1 + lam * (f k x - μ k) + 8 * lam ^ 2 := by
      intro x _
      have hdiff : |f k x - μ k| ≤ 2 := by
        calc |f k x - μ k| ≤ |f k x| + |μ k| := abs_sub _ _
          _ ≤ 1 + 1 := add_le_add (hf k x) (hμ_abs k)
          _ = 2 := by norm_num
      have harg : |lam * (f k x - μ k)| ≤ 1 / 2 := by
        rw [abs_mul, abs_of_pos hlam0]
        nlinarith
      have hq := exp_le_quad harg
      have hsq : (lam * (f k x - μ k)) ^ 2 ≤ 4 * lam ^ 2 := by
        have h1 : (f k x - μ k) ^ 2 ≤ 4 := by
          have := sq_le_sq.mpr (show |f k x - μ k| ≤ |2| by simpa using hdiff)
          nlinarith
        nlinarith [sq_nonneg lam]
      linarith
    have hsum_zero : ∑ x ∈ S k, (f k x - μ k) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      dsimp [μ]
      rw [mul_div_cancel₀ _ (ne_of_gt (hSpos k)), sub_self]
    calc ∑ x ∈ S k, Real.exp (lam * (f k x - μ k))
        ≤ ∑ x ∈ S k, (1 + lam * (f k x - μ k) + 8 * lam ^ 2) := Finset.sum_le_sum hpt
      _ = ((S k).card : ℝ) * (1 + 8 * lam ^ 2) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum_zero, mul_zero,
            Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ ((S k).card : ℝ) * Real.exp (8 * lam ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (8 * lam ^ 2)]) (le_of_lt (hSpos k))
  have hmgf : ∑ p ∈ Ω, Real.exp (lam * ∑ k : Fin K, (f k (p k) - μ k)) ≤
      (Ω.card : ℝ) * Real.exp (8 * lam ^ 2 * (K : ℝ)) := by
    have hrew : ∑ p ∈ Ω, Real.exp (lam * ∑ k : Fin K, (f k (p k) - μ k)) =
        ∏ k : Fin K, ∑ x ∈ S k, Real.exp (lam * (f k x - μ k)) := by
      rw [Finset.prod_univ_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum, Real.exp_sum]
    rw [hrew]
    calc ∏ k : Fin K, ∑ x ∈ S k, Real.exp (lam * (f k x - μ k))
        ≤ ∏ k : Fin K, (((S k).card : ℝ) * Real.exp (8 * lam ^ 2)) :=
          Finset.prod_le_prod (fun k _ => Finset.sum_nonneg fun _ _ => Real.exp_nonneg _)
            (fun k _ => hone_coord k)
      _ = (∏ k : Fin K, ((S k).card : ℝ)) * (∏ _k : Fin K, Real.exp (8 * lam ^ 2)) :=
          Finset.prod_mul_distrib
      _ = (Ω.card : ℝ) * Real.exp (8 * lam ^ 2 * (K : ℝ)) := by
          rw [Fintype.card_piFinset, Nat.cast_prod, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin, ← Real.exp_nat_mul]
          congr 2; ring
  let Bad := Ω.filter (fun p => ε * (K : ℝ) ≤ ∑ k : Fin K, (f k (p k) - μ k))
  have hmarkov : (Bad.card : ℝ) * Real.exp (lam * (ε * (K : ℝ))) ≤
      ∑ p ∈ Ω, Real.exp (lam * ∑ k : Fin K, (f k (p k) - μ k)) := by
    calc (Bad.card : ℝ) * Real.exp (lam * (ε * (K : ℝ)))
        = ∑ _p ∈ Bad, Real.exp (lam * (ε * (K : ℝ))) := by simp
      _ ≤ ∑ p ∈ Bad, Real.exp (lam * ∑ k : Fin K, (f k (p k) - μ k)) := by
          refine Finset.sum_le_sum fun p hp => Real.exp_le_exp.mpr ?_
          have hp' := (Finset.mem_filter.mp hp).2
          exact mul_le_mul_of_nonneg_left hp' (le_of_lt hlam0)
      _ ≤ ∑ p ∈ Ω, Real.exp (lam * ∑ k : Fin K, (f k (p k) - μ k)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Real.exp_nonneg _)
  have hcomb : (Bad.card : ℝ) * Real.exp (lam * (ε * (K : ℝ))) ≤
      (Ω.card : ℝ) * Real.exp (8 * lam ^ 2 * (K : ℝ)) := hmarkov.trans hmgf
  have hexp_eq : Real.exp (8 * lam ^ 2 * (K : ℝ)) / Real.exp (lam * (ε * (K : ℝ))) =
      Real.exp (-(ε ^ 2 / 32) * (K : ℝ)) := by
    rw [← Real.exp_sub]
    congr 1
    dsimp [lam]; ring
  rw [← hexp_eq, mul_div_assoc', le_div_iff₀ (Real.exp_pos _)]
  exact hcomb

lemma finite_hoeffding_abs {K : ℕ} (hK : 0 < K)
    (S : Fin K → Finset ℕ) (hS : ∀ k, (S k).Nonempty)
    (f : Fin K → ℕ → ℝ) (hf : ∀ k x, |f k x| ≤ 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    let μ : Fin K → ℝ := fun k => (∑ x ∈ S k, f k x) / ((S k).card : ℝ)
    let Ω : Finset (Fin K → ℕ) := Fintype.piFinset S
    ((Ω.filter (fun p => ε * (K : ℝ) ≤ |∑ k : Fin K, (f k (p k) - μ k)|)).card : ℝ) ≤
      2 * (Ω.card : ℝ) * Real.exp (-(ε ^ 2 / 32) * (K : ℝ)) := by
  intro μ Ω
  let B1 := Ω.filter (fun p => ε * (K : ℝ) ≤ ∑ k : Fin K, (f k (p k) - μ k))
  let B2 := Ω.filter (fun p => ε * (K : ℝ) ≤ ∑ k : Fin K, (-f k (p k) - (-μ k)))
  have hsub : Ω.filter (fun p => ε * (K : ℝ) ≤ |∑ k : Fin K, (f k (p k) - μ k)|) ⊆ B1 ∪ B2 := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases le_abs.mp hp.2 with h1 | h2
    · exact Or.inl ⟨hp.1, h1⟩
    · refine Or.inr ⟨hp.1, ?_⟩
      have hneg : ∑ k : Fin K, (-f k (p k) - -μ k) = -(∑ k : Fin K, (f k (p k) - μ k)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      linarith
  have h1 := finite_hoeffding_upper hK S hS f hf hε0 hε1
  have h2 := finite_hoeffding_upper hK S hS (fun k x => -f k x) (fun k x => by simpa using hf k x) hε0 hε1
  have hμneg : (fun k => (∑ x ∈ S k, -f k x) / ((S k).card : ℝ)) = fun k => -μ k := by
    ext k; dsimp [μ]; rw [Finset.sum_neg_distrib, neg_div]
  rw [hμneg] at h2
  have hcard : ((Ω.filter (fun p => ε * (K : ℝ) ≤ |∑ k : Fin K, (f k (p k) - μ k)|)).card : ℝ) ≤
      (B1.card : ℝ) + (B2.card : ℝ) := by
    have : (Ω.filter (fun p => ε * (K : ℝ) ≤ |∑ k : Fin K, (f k (p k) - μ k)|)).card ≤
        B1.card + B2.card := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    exact_mod_cast this
  linarith

/- ### Part 4: Existence of a uniformly good deterministic block -/

lemma trig_sum_triangle_bound {K : ℕ} {ε B : ℝ}
    (g1 g2 μ : Fin K → ℝ)
    (hlip : ∀ k : Fin K, |g1 k - g2 k| ≤ ε)
    (hdev : |∑ k : Fin K, (g2 k - μ k)| < ε * (K : ℝ))
    (hmean : ∀ k : Fin K, |μ k| ≤ ε)
    (h3ε : 3 * ε * (K : ℝ) ≤ B) :
    |∑ k : Fin K, g1 k| ≤ B := by
  have hsum_lip : |∑ k : Fin K, (g1 k - g2 k)| ≤ ε * (K : ℝ) := by
    calc |∑ k : Fin K, (g1 k - g2 k)|
        ≤ ∑ k : Fin K, |g1 k - g2 k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin K, ε := Finset.sum_le_sum fun k _ => hlip k
      _ = ε * (K : ℝ) := by simp [mul_comm]
  have hsum_mean : |∑ k : Fin K, μ k| ≤ ε * (K : ℝ) := by
    calc |∑ k : Fin K, μ k| ≤ ∑ k : Fin K, |μ k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin K, ε := Finset.sum_le_sum fun k _ => hmean k
      _ = ε * (K : ℝ) := by simp [mul_comm]
  have hsplit : ∑ k : Fin K, g1 k =
      (∑ k : Fin K, (g1 k - g2 k)) + (∑ k : Fin K, (g2 k - μ k)) + (∑ k : Fin K, μ k) := by
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit]
  have h1 := abs_add_le
    ((∑ k : Fin K, (g1 k - g2 k)) + (∑ k : Fin K, (g2 k - μ k))) (∑ k : Fin K, μ k)
  have h2 := abs_add_le (∑ k : Fin K, (g1 k - g2 k)) (∑ k : Fin K, (g2 k - μ k))
  linarith

set_option maxHeartbeats 400000 in
lemma exists_good_block (H : ℕ) (hH : 1 ≤ H) (δ : ℝ) (hδ : 0 < δ) (K0 : ℕ) :
    ∃ (K : ℕ) (p : Fin K → ℕ),
      max K0 1 ≤ K ∧
      (∀ k : Fin K, nSeq (K + k.1) ≤ p k ∧ p k < nSeq (K + k.1) + (K + k.1) + 1) ∧
      (∀ ξ : ℝ, (∀ h ∈ Finset.Ico 1 H, δ ≤ |Real.sin (Real.pi * (h : ℝ) * ξ)|) →
        ∀ h ∈ Finset.Ico 1 H,
          |∑ k : Fin K, Real.cos (2 * Real.pi * (h : ℝ) * ξ * (p k : ℝ))| ≤ (K : ℝ) / (8 * (H : ℝ)) ∧
          |∑ k : Fin K, Real.sin (2 * Real.pi * (h : ℝ) * ξ * (p k : ℝ))| ≤ (K : ℝ) / (8 * (H : ℝ))) := by
  let ε : ℝ := 1 / (32 * (H : ℝ))
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have hε0 : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    linarith
  let c : ℝ := ε ^ 2 / 64
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨C, hCpos, hCsub⟩ := nSeq_subexp hc
  -- Pick `K` large enough for both the mean bound and the union bound!
  let A1 : ℝ := 2 / (δ * ε)
  let B0 : ℝ := max (2 * Real.pi * (H : ℝ) * C / ε) (4 * Real.pi * (H : ℝ) / δ)
  let A2 : ℝ := 4 * (H : ℝ) * (B0 + 3)
  let K : ℕ := max (max K0 1) (max (⌈A1⌉₊ + 1) (⌈A2 / c⌉₊ + 1))
  have hK_ge : max K0 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := lt_of_lt_of_le (by omega : 0 < max K0 1) hK_ge
  have hKR_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hKpos
  have hK_mean : 1 / ((K : ℝ) * (δ / 2)) ≤ ε := by
    have hKA1 : A1 ≤ (K : ℝ) := by
      have h1 : A1 ≤ (⌈A1⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ⌈A1⌉₊ + 1 ≤ K := (le_max_left _ _).trans (le_max_right _ _)
      have h2R : ((⌈A1⌉₊ + 1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast h2
      push_cast at h2R; linarith
    dsimp [A1] at hKA1
    rw [div_le_iff₀ (mul_pos hδ hε0)] at hKA1
    rw [div_le_iff₀ (mul_pos hKR_pos (by linarith))]
    linarith
  let M : ℕ := nSeq (2 * K) + 2 * K
  have hM_le : (M : ℝ) ≤ C * Real.exp (c * (K : ℝ)) := hCsub K
  let N : ℕ := ⌈max (2 * Real.pi * (H : ℝ) * (M : ℝ) / ε) (4 * Real.pi * (H : ℝ) / δ)⌉₊ + 1
  have hN_pos : 0 < N := by dsimp [N]; omega
  have hNR_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos
  have hN_lip1 : 2 * Real.pi * (H : ℝ) * (M : ℝ) / (N : ℝ) ≤ ε := by
    have h1 : 2 * Real.pi * (H : ℝ) * (M : ℝ) / ε ≤ (N : ℝ) := by
      have ha : 2 * Real.pi * (H : ℝ) * (M : ℝ) / ε ≤
          max (2 * Real.pi * (H : ℝ) * (M : ℝ) / ε) (4 * Real.pi * (H : ℝ) / δ) := le_max_left _ _
      have hb : max (2 * Real.pi * (H : ℝ) * (M : ℝ) / ε) (4 * Real.pi * (H : ℝ) / δ) ≤
          (⌈max (2 * Real.pi * (H : ℝ) * (M : ℝ) / ε) (4 * Real.pi * (H : ℝ) / δ)⌉₊ : ℝ) := Nat.le_ceil _
      dsimp [N]; push_cast; linarith
    rw [div_le_iff₀ hε0] at h1
    rw [div_le_iff₀ hNR_pos]; linarith
  have hN_lip2 : 2 * Real.pi * (H : ℝ) / (N : ℝ) ≤ δ / 2 := by
    have h1 : 4 * Real.pi * (H : ℝ) / δ ≤ (N : ℝ) := by
      have ha : 4 * Real.pi * (H : ℝ) / δ ≤
          max (2 * Real.pi * (H : ℝ) * (M : ℝ) / ε) (4 * Real.pi * (H : ℝ) / δ) := le_max_right _ _
      have hb := Nat.le_ceil (max (2 * Real.pi * (H : ℝ) * (M : ℝ) / ε) (4 * Real.pi * (H : ℝ) / δ))
      dsimp [N]; push_cast; linarith
    rw [div_le_iff₀ hδ] at h1
    rw [div_le_iff₀ hNR_pos]; linarith
  have hN1_le : ((N + 1 : ℕ) : ℝ) ≤ (B0 + 3) * Real.exp (c * (K : ℝ)) := by
    have hexp1 : 1 ≤ Real.exp (c * (K : ℝ)) := Real.one_le_exp (by positivity)
    have hmax_le : max (2 * Real.pi * (H : ℝ) * (M : ℝ) / ε) (4 * Real.pi * (H : ℝ) / δ) ≤
        B0 * Real.exp (c * (K : ℝ)) := by
      apply max_le
      · have h1 : 2 * Real.pi * (H : ℝ) * (M : ℝ) / ε ≤
            (2 * Real.pi * (H : ℝ) * C / ε) * Real.exp (c * (K : ℝ)) := by
          have : (2 * Real.pi * (H : ℝ) * C / ε) * Real.exp (c * (K : ℝ)) =
              2 * Real.pi * (H : ℝ) * (C * Real.exp (c * (K : ℝ))) / ε := by ring
          rw [this]
          apply div_le_div_of_nonneg_right _ (le_of_lt hε0)
          exact mul_le_mul_of_nonneg_left hM_le (by positivity)
        have h2 : 2 * Real.pi * (H : ℝ) * C / ε ≤ B0 := le_max_left _ _
        exact h1.trans (mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _))
      · have h2 : 4 * Real.pi * (H : ℝ) / δ ≤ B0 := le_max_right _ _
        have hB0_nonneg : 0 ≤ B0 := le_trans (by positivity) h2
        calc 4 * Real.pi * (H : ℝ) / δ ≤ B0 := h2
          _ ≤ B0 * Real.exp (c * (K : ℝ)) := le_mul_of_one_le_right hB0_nonneg hexp1
    have hceil_lt : (⌈max (2 * Real.pi * (H : ℝ) * (M : ℝ) / ε) (4 * Real.pi * (H : ℝ) / δ)⌉₊ : ℝ) ≤
        max (2 * Real.pi * (H : ℝ) * (M : ℝ) / ε) (4 * Real.pi * (H : ℝ) / δ) + 1 :=
      le_of_lt (Nat.ceil_lt_add_one (le_trans (by positivity) (le_max_right _ _)))
    have hN1R : ((N + 1 : ℕ) : ℝ) =
        (⌈max (2 * Real.pi * (H : ℝ) * (M : ℝ) / ε) (4 * Real.pi * (H : ℝ) / δ)⌉₊ : ℝ) + 2 := by
      dsimp [N]; push_cast; ring
    rw [hN1R]
    nlinarith
  have hunion_lt_one :
      4 * (H : ℝ) * ((N + 1 : ℕ) : ℝ) * Real.exp (-(ε ^ 2 / 32) * (K : ℝ)) < 1 := by
    have hKA2 : A2 / c < (K : ℝ) := by
      have h1 : A2 / c ≤ (⌈A2 / c⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ⌈A2 / c⌉₊ + 1 ≤ K := (le_max_right _ _).trans (le_max_right _ _)
      have h2R : ((⌈A2 / c⌉₊ + 1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast h2
      push_cast at h2R; linarith
    have hA2_lt : A2 < Real.exp (c * (K : ℝ)) := by
      rw [div_lt_iff₀ hc] at hKA2
      linarith [Real.add_one_le_exp (c * (K : ℝ))]
    have hexp_split : Real.exp (c * (K : ℝ)) * Real.exp (-(ε ^ 2 / 32) * (K : ℝ)) =
        (Real.exp (c * (K : ℝ)))⁻¹ := by
      rw [← Real.exp_add, ← Real.exp_neg]
      congr 1; dsimp [c]; ring
    calc 4 * (H : ℝ) * ((N + 1 : ℕ) : ℝ) * Real.exp (-(ε ^ 2 / 32) * (K : ℝ))
        ≤ 4 * (H : ℝ) * ((B0 + 3) * Real.exp (c * (K : ℝ))) * Real.exp (-(ε ^ 2 / 32) * (K : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          exact mul_le_mul_of_nonneg_left hN1_le (by positivity)
      _ = A2 * (Real.exp (c * (K : ℝ)) * Real.exp (-(ε ^ 2 / 32) * (K : ℝ))) := by
          dsimp [A2]; ring
      _ = A2 * (Real.exp (c * (K : ℝ)))⁻¹ := by rw [hexp_split]
      _ < Real.exp (c * (K : ℝ)) * (Real.exp (c * (K : ℝ)))⁻¹ :=
          mul_lt_mul_of_pos_right hA2_lt (inv_pos.mpr (Real.exp_pos _))
      _ = 1 := mul_inv_cancel₀ (Real.exp_ne_zero _)
  -- Define finite product space `Ω` of corridors on `[K, 2*K)`
  let S : Fin K → Finset ℕ := fun k => Finset.Ico (nSeq (K + k.1)) (nSeq (K + k.1) + (K + k.1) + 1)
  have hS_ne : ∀ k : Fin K, (S k).Nonempty := fun k =>
    Finset.nonempty_Ico.mpr (by omega)
  let Ω : Finset (Fin K → ℕ) := Fintype.piFinset S
  have hΩ_pos : 0 < Ω.card := by
    rw [Fintype.card_piFinset]
    exact Finset.prod_pos fun k _ => Finset.card_pos.mpr (hS_ne k)
  let αNet : ℕ → ℝ := fun m => (m : ℝ) / (N : ℝ)
  let badCos (h m : ℕ) : Finset (Fin K → ℕ) :=
    let f : Fin K → ℕ → ℝ := fun _ x => Real.cos (2 * Real.pi * (h : ℝ) * αNet m * (x : ℝ))
    let μ : Fin K → ℝ := fun k => (∑ x ∈ S k, f k x) / ((S k).card : ℝ)
    Ω.filter (fun p => ε * (K : ℝ) ≤ |∑ k : Fin K, (f k (p k) - μ k)|)
  let badSin (h m : ℕ) : Finset (Fin K → ℕ) :=
    let f : Fin K → ℕ → ℝ := fun _ x => Real.sin (2 * Real.pi * (h : ℝ) * αNet m * (x : ℝ))
    let μ : Fin K → ℝ := fun k => (∑ x ∈ S k, f k x) / ((S k).card : ℝ)
    Ω.filter (fun p => ε * (K : ℝ) ≤ |∑ k : Fin K, (f k (p k) - μ k)|)
  let BadAll : Finset (Fin K → ℕ) :=
    ((Finset.Ico 1 H).product (Finset.range (N + 1))).biUnion (fun hm => badCos hm.1 hm.2 ∪ badSin hm.1 hm.2)
  have hBad_lt : BadAll.card < Ω.card := by
    have h1 : (BadAll.card : ℝ) ≤
        ∑ hm ∈ (Finset.Ico 1 H).product (Finset.range (N + 1)),
          ((badCos hm.1 hm.2).card + (badSin hm.1 hm.2).card : ℝ) := by
      have hc1 : BadAll.card ≤
          ∑ hm ∈ (Finset.Ico 1 H).product (Finset.range (N + 1)),
            (badCos hm.1 hm.2 ∪ badSin hm.1 hm.2).card := Finset.card_biUnion_le
      have hc2 : ∑ hm ∈ (Finset.Ico 1 H).product (Finset.range (N + 1)),
            (badCos hm.1 hm.2 ∪ badSin hm.1 hm.2).card ≤
          ∑ hm ∈ (Finset.Ico 1 H).product (Finset.range (N + 1)),
            ((badCos hm.1 hm.2).card + (badSin hm.1 hm.2).card) :=
        Finset.sum_le_sum fun hm _ => Finset.card_union_le _ _
      exact_mod_cast (hc1.trans hc2)
    have h2 : ∀ hm ∈ (Finset.Ico 1 H).product (Finset.range (N + 1)),
        ((badCos hm.1 hm.2).card + (badSin hm.1 hm.2).card : ℝ) ≤
          4 * (Ω.card : ℝ) * Real.exp (-(ε ^ 2 / 32) * (K : ℝ)) := by
      intro hm _
      have hc := finite_hoeffding_abs hKpos S hS_ne
        (fun _ x => Real.cos (2 * Real.pi * (hm.1 : ℝ) * αNet hm.2 * (x : ℝ)))
        (fun _ _ => Real.abs_cos_le_one _) hε0 hε1
      have hs := finite_hoeffding_abs hKpos S hS_ne
        (fun _ x => Real.sin (2 * Real.pi * (hm.1 : ℝ) * αNet hm.2 * (x : ℝ)))
        (fun _ _ => Real.abs_sin_le_one _) hε0 hε1
      dsimp only [badCos, badSin]
      linarith
    have hcard_prod : (((Finset.Ico 1 H).product (Finset.range (N + 1))).card : ℝ) ≤
        (H : ℝ) * ((N + 1 : ℕ) : ℝ) := by
      change (((Finset.Ico 1 H ×ˢ Finset.range (N + 1)).card : ℕ) : ℝ) ≤ _
      rw [Finset.card_product, Nat.card_Ico, Finset.card_range, Nat.cast_mul]
      have : ((H - 1 : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast Nat.sub_le H 1
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have hltR : (BadAll.card : ℝ) < (Ω.card : ℝ) := by
      calc (BadAll.card : ℝ)
          ≤ ∑ _hm ∈ (Finset.Ico 1 H).product (Finset.range (N + 1)),
              (4 * (Ω.card : ℝ) * Real.exp (-(ε ^ 2 / 32) * (K : ℝ))) :=
            h1.trans (Finset.sum_le_sum h2)
        _ = (((Finset.Ico 1 H).product (Finset.range (N + 1))).card : ℝ) *
              (4 * (Ω.card : ℝ) * Real.exp (-(ε ^ 2 / 32) * (K : ℝ))) := by simp
        _ ≤ ((H : ℝ) * ((N + 1 : ℕ) : ℝ)) *
              (4 * (Ω.card : ℝ) * Real.exp (-(ε ^ 2 / 32) * (K : ℝ))) :=
            mul_le_mul_of_nonneg_right hcard_prod (by positivity)
        _ = (Ω.card : ℝ) * (4 * (H : ℝ) * ((N + 1 : ℕ) : ℝ) * Real.exp (-(ε ^ 2 / 32) * (K : ℝ))) := by ring
        _ < (Ω.card : ℝ) * 1 :=
            mul_lt_mul_of_pos_left hunion_lt_one (Nat.cast_pos.mpr hΩ_pos)
        _ = (Ω.card : ℝ) := mul_one _
    exact_mod_cast hltR
  have hex : (Ω \ BadAll).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : Ω ⊆ BadAll := Finset.sdiff_eq_empty_iff_subset.mp hemp
    exact absurd (Finset.card_le_card hsub) (not_le_of_gt hBad_lt)
  obtain ⟨p, hp⟩ := hex
  rw [Finset.mem_sdiff] at hp
  have hp_mem : ∀ k : Fin K, nSeq (K + k.1) ≤ p k ∧ p k < nSeq (K + k.1) + (K + k.1) + 1 := by
    intro k
    have := (Fintype.mem_piFinset.mp hp.1) k
    exact Finset.mem_Ico.mp this
  refine ⟨K, p, hK_ge, hp_mem, ?_⟩
  intro ξ hξ h hh
  have hh_lt : h < H := (Finset.mem_Ico.mp hh).2
  let α : ℝ := Int.fract ξ
  have hα0 : 0 ≤ α := Int.fract_nonneg ξ
  have hα1 : α < 1 := Int.fract_lt_one ξ
  let m : ℕ := ⌊α * (N : ℝ)⌋₊
  have hm_lt : m < N := by
    rw [Nat.floor_lt (by positivity)]
    nlinarith
  have hα_dist : |α - αNet m| ≤ 1 / (N : ℝ) := by
    dsimp [αNet, m]
    have h1 : (⌊α * (N : ℝ)⌋₊ : ℝ) ≤ α * (N : ℝ) := Nat.floor_le (by positivity)
    have h2 : α * (N : ℝ) < (⌊α * (N : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [abs_le]
    constructor
    · rw [le_sub_iff_add_le]
      have hdiv : (⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ) ≤ α := (div_le_iff₀ hNR_pos).mpr h1
      have hinvpos : (0 : ℝ) < 1 / (N : ℝ) := by positivity
      linarith
    · rw [sub_le_iff_le_add]
      have : α ≤ ((⌊α * (N : ℝ)⌋₊ : ℝ) + 1) / (N : ℝ) := (le_div_iff₀ hNR_pos).mpr (le_of_lt h2)
      rw [add_div] at this
      linarith
  have hsin_α : |Real.sin (Real.pi * (h : ℝ) * α)| = |Real.sin (Real.pi * (h : ℝ) * ξ)| := by
    have harg : Real.pi * (h : ℝ) * ξ =
        Real.pi * (h : ℝ) * α + ((h : ℤ) * Int.floor ξ : ℤ) * Real.pi := by
      dsimp [α]; rw [Int.fract]; push_cast; ring
    rw [harg, Real.sin_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  have hsin_m : δ / 2 ≤ |Real.sin (Real.pi * (h : ℝ) * αNet m)| := by
    have h1 : δ ≤ |Real.sin (Real.pi * (h : ℝ) * α)| := hsin_α.symm ▸ hξ h hh
    have h2 : |Real.sin (Real.pi * (h : ℝ) * α) - Real.sin (Real.pi * (h : ℝ) * αNet m)| ≤ δ / 2 := by
      calc |Real.sin (Real.pi * (h : ℝ) * α) - Real.sin (Real.pi * (h : ℝ) * αNet m)|
          ≤ |Real.pi * (h : ℝ) * α - Real.pi * (h : ℝ) * αNet m| := Real.abs_sin_sub_sin_le _ _
        _ = Real.pi * (h : ℝ) * |α - αNet m| := by
            rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
        _ ≤ Real.pi * (H : ℝ) * (1 / (N : ℝ)) := by
            have hhH : (h : ℝ) ≤ (H : ℝ) := by exact_mod_cast le_of_lt hh_lt
            exact mul_le_mul (by nlinarith [Real.pi_pos]) hα_dist (abs_nonneg _) (by positivity)
        _ ≤ δ / 2 := by
            have hhalf : Real.pi * (H : ℝ) * (1 / (N : ℝ)) = (2 * Real.pi * (H : ℝ) / (N : ℝ)) / 2 := by
              ring
            linarith
    have htri := abs_sub_abs_le_abs_sub (Real.sin (Real.pi * (h : ℝ) * α))
      (Real.sin (Real.pi * (h : ℝ) * αNet m))
    linarith
  have hsin_m_ne : Real.sin (Real.pi * ((h : ℝ) * αNet m)) ≠ 0 := by
    intro hz
    have : Real.pi * (h : ℝ) * αNet m = Real.pi * ((h : ℝ) * αNet m) := by ring
    rw [this, hz, abs_zero] at hsin_m
    linarith
  have hp_not_bad : p ∉ badCos h m ∧ p ∉ badSin h m := by
    have hmem_hm : (h, m) ∈ (Finset.Ico 1 H).product (Finset.range (N + 1)) :=
      Finset.mem_product.mpr ⟨hh, Finset.mem_range.mpr (by omega)⟩
    constructor
    · intro hbc
      exact hp.2 (Finset.mem_biUnion.mpr ⟨(h, m), hmem_hm, Finset.mem_union_left _ hbc⟩)
    · intro hbs
      exact hp.2 (Finset.mem_biUnion.mpr ⟨(h, m), hmem_hm, Finset.mem_union_right _ hbs⟩)
  have hp_le_M : ∀ k : Fin K, (p k : ℝ) ≤ (M : ℝ) := by
    intro k
    have h1 : p k < nSeq (K + k.1) + (K + k.1) + 1 := (hp_mem k).2
    have h2 : nSeq (K + k.1) ≤ nSeq (2 * K) := nSeq_mono (by omega)
    have h3 : p k ≤ M := by dsimp [M]; omega
    exact_mod_cast h3
  have hS_sum_eq : ∀ (k : Fin K) (g : ℕ → ℝ),
      ∑ x ∈ S k, g x = ∑ j ∈ Finset.range (K + k.1 + 1), g (nSeq (K + k.1) + j) := by
    intro k g
    dsimp [S]
    rw [Finset.sum_Ico_eq_sum_range]
    have : nSeq (K + k.1) + (K + k.1) + 1 - nSeq (K + k.1) = K + k.1 + 1 := by omega
    rw [this]
  have hS_card : ∀ k : Fin K, ((S k).card : ℝ) = ((K + k.1 + 1 : ℕ) : ℝ) := by
    intro k; dsimp [S]; rw [Nat.card_Ico]
    have : nSeq (K + k.1) + (K + k.1) + 1 - nSeq (K + k.1) = K + k.1 + 1 := by omega
    rw [this]
  have hK_le_Scard : ∀ k : Fin K, (K : ℝ) ≤ ((S k).card : ℝ) := by
    intro k; rw [hS_card]; exact_mod_cast (by omega : K ≤ K + k.1 + 1)
  have hcos_ξ_eq : ∀ k : Fin K,
      Real.cos (2 * Real.pi * (h : ℝ) * ξ * (p k : ℝ)) =
      Real.cos (2 * Real.pi * (h : ℝ) * α * (p k : ℝ)) := by
    intro k
    have harg : 2 * Real.pi * (h : ℝ) * ξ * (p k : ℝ) =
        2 * Real.pi * (h : ℝ) * α * (p k : ℝ) +
        (((h * p k : ℕ) : ℤ) * Int.floor ξ : ℤ) * (2 * Real.pi) := by
      dsimp [α]; rw [Int.fract]; push_cast; ring
    rw [harg, Real.cos_add_int_mul_two_pi]
  have hsin_ξ_eq : ∀ k : Fin K,
      Real.sin (2 * Real.pi * (h : ℝ) * ξ * (p k : ℝ)) =
      Real.sin (2 * Real.pi * (h : ℝ) * α * (p k : ℝ)) := by
    intro k
    have harg : 2 * Real.pi * (h : ℝ) * ξ * (p k : ℝ) =
        2 * Real.pi * (h : ℝ) * α * (p k : ℝ) +
        (((h * p k : ℕ) : ℤ) * Int.floor ξ : ℤ) * (2 * Real.pi) := by
      dsimp [α]; rw [Int.fract]; push_cast; ring
    rw [harg, Real.sin_add_int_mul_two_pi]
  have h3ε : 3 * ε * (K : ℝ) ≤ (K : ℝ) / (8 * (H : ℝ)) := by
    dsimp [ε]
    have heq : 3 * (1 / (32 * (H : ℝ))) * (K : ℝ) = (3 / 4) * ((K : ℝ) / (8 * (H : ℝ))) := by ring
    rw [heq]
    have hnonneg : (0 : ℝ) ≤ (K : ℝ) / (8 * (H : ℝ)) := by positivity
    linarith
  have h1_div_sin : 1 / |Real.sin (Real.pi * ((h : ℝ) * αNet m))| ≤ ε * (K : ℝ) := by
    have hsin_m' : δ / 2 ≤ |Real.sin (Real.pi * ((h : ℝ) * αNet m))| := by
      simpa [mul_assoc] using hsin_m
    have hinv : 1 / |Real.sin (Real.pi * ((h : ℝ) * αNet m))| ≤ 1 / (δ / 2) :=
      one_div_le_one_div_of_le (by linarith) hsin_m'
    have hK_mul : 1 / (δ / 2) ≤ ε * (K : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      have := hK_mean
      rw [div_le_iff₀ (mul_pos hKR_pos (by linarith))] at this
      linarith
    exact hinv.trans hK_mul
  have harg_lip : ∀ k : Fin K,
      |2 * Real.pi * (h : ℝ) * α * (p k : ℝ) - 2 * Real.pi * (h : ℝ) * αNet m * (p k : ℝ)| ≤ ε := by
    intro k
    calc |2 * Real.pi * (h : ℝ) * α * (p k : ℝ) - 2 * Real.pi * (h : ℝ) * αNet m * (p k : ℝ)|
        = 2 * Real.pi * (h : ℝ) * (p k : ℝ) * |α - αNet m| := by
            have heq : 2 * Real.pi * (h : ℝ) * α * (p k : ℝ) -
                2 * Real.pi * (h : ℝ) * αNet m * (p k : ℝ) =
                (2 * Real.pi * (h : ℝ) * (p k : ℝ)) * (α - αNet m) := by ring
            rw [heq, abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (2 * Real.pi * (H : ℝ) * (M : ℝ)) * (1 / (N : ℝ)) := by
            have hhH : (h : ℝ) ≤ (H : ℝ) := by exact_mod_cast le_of_lt hh_lt
            have h1 : 2 * Real.pi * (h : ℝ) * (p k : ℝ) ≤ 2 * Real.pi * (H : ℝ) * (M : ℝ) := by
              have hpM := hp_le_M k
              have h2h : 2 * Real.pi * (h : ℝ) ≤ 2 * Real.pi * (H : ℝ) := by nlinarith [Real.pi_pos]
              exact mul_le_mul h2h hpM (by positivity) (by positivity)
            exact mul_le_mul h1 hα_dist (abs_nonneg _) (by positivity)
      _ = 2 * Real.pi * (H : ℝ) * (M : ℝ) / (N : ℝ) := by ring
      _ ≤ ε := hN_lip1
  constructor
  · -- Cosine bound
    let f : Fin K → ℕ → ℝ := fun _ x => Real.cos (2 * Real.pi * (h : ℝ) * αNet m * (x : ℝ))
    let μ : Fin K → ℝ := fun k => (∑ x ∈ S k, f k x) / ((S k).card : ℝ)
    have hdev : |∑ k : Fin K, (f k (p k) - μ k)| < ε * (K : ℝ) := by
      have hnb := hp_not_bad.1
      dsimp [badCos] at hnb
      rw [Finset.mem_filter] at hnb
      push Not at hnb
      exact hnb hp.1
    have hmean_le : ∀ k : Fin K, |μ k| ≤ ε := by
      intro k
      have hSc : (0 : ℝ) < ((S k).card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr (hS_ne k))
      dsimp [μ, f]
      rw [abs_div, abs_of_pos (a := ((S k).card : ℝ)) hSc, div_le_iff₀ hSc, hS_sum_eq]
      have harg : ∀ j : ℕ, 2 * Real.pi * (h : ℝ) * αNet m * ((nSeq (K + k.1) + j : ℕ) : ℝ) =
          2 * Real.pi * ((h : ℝ) * αNet m) * ((nSeq (K + k.1) + j : ℕ) : ℝ) := fun _ => by ring
      simp_rw [harg]
      have hb := cos_range_sum_bound (nSeq (K + k.1)) (K + k.1 + 1) ((h : ℝ) * αNet m) hsin_m_ne
      exact hb.trans (h1_div_sin.trans (mul_le_mul_of_nonneg_left (hK_le_Scard k) (le_of_lt hε0)))
    simp_rw [hcos_ξ_eq]
    exact trig_sum_triangle_bound
      (fun k => Real.cos (2 * Real.pi * (h : ℝ) * α * (p k : ℝ)))
      (fun k => f k (p k)) μ
      (fun k => (Real.abs_cos_sub_cos_le _ _).trans (harg_lip k))
      hdev hmean_le h3ε
  · -- Sine bound
    let f : Fin K → ℕ → ℝ := fun _ x => Real.sin (2 * Real.pi * (h : ℝ) * αNet m * (x : ℝ))
    let μ : Fin K → ℝ := fun k => (∑ x ∈ S k, f k x) / ((S k).card : ℝ)
    have hdev : |∑ k : Fin K, (f k (p k) - μ k)| < ε * (K : ℝ) := by
      have hnb := hp_not_bad.2
      dsimp [badSin] at hnb
      rw [Finset.mem_filter] at hnb
      push Not at hnb
      exact hnb hp.1
    have hmean_le : ∀ k : Fin K, |μ k| ≤ ε := by
      intro k
      have hSc : (0 : ℝ) < ((S k).card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr (hS_ne k))
      dsimp [μ, f]
      rw [abs_div, abs_of_pos (a := ((S k).card : ℝ)) hSc, div_le_iff₀ hSc, hS_sum_eq]
      have harg : ∀ j : ℕ, 2 * Real.pi * (h : ℝ) * αNet m * ((nSeq (K + k.1) + j : ℕ) : ℝ) =
          2 * Real.pi * ((h : ℝ) * αNet m) * ((nSeq (K + k.1) + j : ℕ) : ℝ) := fun _ => by ring
      simp_rw [harg]
      have hb := sin_range_sum_bound (nSeq (K + k.1)) (K + k.1 + 1) ((h : ℝ) * αNet m) hsin_m_ne
      exact hb.trans (h1_div_sin.trans (mul_le_mul_of_nonneg_left (hK_le_Scard k) (le_of_lt hε0)))
    simp_rw [hsin_ξ_eq]
    exact trig_sum_triangle_bound
      (fun k => Real.sin (2 * Real.pi * (h : ℝ) * α * (p k : ℝ)))
      (fun k => f k (p k)) μ
      (fun k => (Real.abs_sin_sub_sin_le _ _).trans (harg_lip k))
      hdev hmean_le h3ε

/- ### Part 5: Stitching disjoint blocks and concluding density modulo one -/

def blockH (j : ℕ) : ℕ := (Nat.unpair j).1 + 2

def blockD (j : ℕ) : ℕ := (Nat.unpair j).2 + 2

structure BlockData (j : ℕ) where
  K : ℕ
  p : Fin K → ℕ
  hKpos : 1 ≤ K
  hmem : ∀ k : Fin K, nSeq (K + k.1) ≤ p k ∧ p k < nSeq (K + k.1) + (K + k.1) + 1
  hgood : ∀ ξ : ℝ,
    (∀ h ∈ Finset.Ico 1 (blockH j), 1 / (blockD j : ℝ) ≤ |Real.sin (Real.pi * (h : ℝ) * ξ)|) →
    ∀ h ∈ Finset.Ico 1 (blockH j),
      |∑ k : Fin K, Real.cos (2 * Real.pi * (h : ℝ) * ξ * (p k : ℝ))| ≤
        (K : ℝ) / (8 * (blockH j : ℝ)) ∧
      |∑ k : Fin K, Real.sin (2 * Real.pi * (h : ℝ) * ξ * (p k : ℝ))| ≤
        (K : ℝ) / (8 * (blockH j : ℝ))

noncomputable def buildBlock (j : ℕ) (K0 : ℕ) : { b : BlockData j // K0 ≤ b.K } := by
  have hH1 : 1 ≤ blockH j := by dsimp [blockH]; omega
  have hDpos : (0 : ℝ) < (blockD j : ℝ) := by
    dsimp [blockD]; exact_mod_cast (by omega : 0 < (Nat.unpair j).2 + 2)
  have hex := exists_good_block (blockH j) hH1 (1 / (blockD j : ℝ)) (by positivity) K0
  exact ⟨⟨Classical.choose hex, Classical.choose (Classical.choose_spec hex),
      le_trans (le_max_right K0 1) (Classical.choose_spec (Classical.choose_spec hex)).1,
      (Classical.choose_spec (Classical.choose_spec hex)).2.1,
      (Classical.choose_spec (Classical.choose_spec hex)).2.2⟩,
    le_trans (le_max_left K0 1) (Classical.choose_spec (Classical.choose_spec hex)).1⟩

noncomputable def blocks : (j : ℕ) → BlockData j
  | 0 => (buildBlock 0 1).1
  | j + 1 => (buildBlock (j + 1) (2 * (blocks j).K)).1

lemma blocks_K_step (j : ℕ) : 2 * (blocks j).K ≤ (blocks (j + 1)).K :=
  (buildBlock (j + 1) (2 * (blocks j).K)).2

lemma blocks_K_lt_of_lt {i j : ℕ} (hij : i < j) : 2 * (blocks i).K ≤ (blocks j).K := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hij) with hlt | rfl
    · have h1 := ih hlt
      have h2 := blocks_K_step j
      omega
    · exact blocks_K_step i

lemma blocks_disjoint {i j n : ℕ}
    (hi : (blocks i).K ≤ n ∧ n < 2 * (blocks i).K)
    (hj : (blocks j).K ≤ n ∧ n < 2 * (blocks j).K) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := blocks_K_lt_of_lt hlt; omega
  · have := blocks_K_lt_of_lt hgt; omega

lemma blocks_p_congr {i j a b : ℕ} (hij : i = j) (hab : a = b)
    (ha : a < (blocks i).K) (hb : b < (blocks j).K) :
    (blocks i).p ⟨a, ha⟩ = (blocks j).p ⟨b, hb⟩ := by
  subst hij
  subst hab
  rfl

open Classical in
noncomputable def mSeq (n : ℕ) : ℕ :=
  if h : ∃ j : ℕ, (blocks j).K ≤ n ∧ n < 2 * (blocks j).K then
    (blocks h.choose).p ⟨n - (blocks h.choose).K, by have hj := h.choose_spec; omega⟩
  else
    nSeq n

open Classical in
lemma mSeq_in_corridor (n : ℕ) : nSeq n ≤ mSeq n ∧ mSeq n < nSeq n + n + 1 := by
  unfold mSeq
  split_ifs with h
  · have hj := h.choose_spec
    have hmem := (blocks h.choose).hmem ⟨n - (blocks h.choose).K, by omega⟩
    have heq : (blocks h.choose).K + (n - (blocks h.choose).K) = n := by omega
    simpa [heq] using hmem
  · exact ⟨le_refl _, by omega⟩

open Classical in
lemma mSeq_on_block (j : ℕ) (k : Fin (blocks j).K) :
    mSeq ((blocks j).K + k.1) = (blocks j).p k := by
  have hex : ∃ i : ℕ, (blocks i).K ≤ (blocks j).K + k.1 ∧
      (blocks j).K + k.1 < 2 * (blocks i).K := ⟨j, by omega, by omega⟩
  unfold mSeq
  rw [dif_pos hex]
  have hij : hex.choose = j := blocks_disjoint hex.choose_spec ⟨by omega, by omega⟩
  exact blocks_p_congr hij (by rw [hij]; omega) _ k.2

lemma sin_pi_mul_ne_zero_of_irrational {ξ : ℝ} (hξ : Irrational ξ) {h : ℕ} (hh : 1 ≤ h) :
    Real.sin (Real.pi * (h : ℝ) * ξ) ≠ 0 := by
  intro hz
  rw [Real.sin_eq_zero_iff] at hz
  rcases hz with ⟨k, hk⟩
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hh0 : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmul : ξ * (h : ℝ) = (k : ℝ) := by
    have : Real.pi * (ξ * (h : ℝ)) = Real.pi * (k : ℝ) := by linarith
    exact mul_left_cancel₀ hpi this
  have hξ_eq : (((k : ℚ) / (h : ℚ) : ℚ) : ℝ) = ξ := by
    push_cast
    rw [div_eq_iff hh0]
    exact hmul.symm
  exact hξ ⟨(k : ℚ) / (h : ℚ), hξ_eq⟩

theorem main :
    ∃ m : ℕ → ℕ,
      StrictMono m ∧
      Bugeaud06.IsGenuinelySublacunary m ∧
      ∀ ξ : ℝ, Irrational ξ →
        Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) := by
  refine ⟨mSeq, strictMono_of_corridor mSeq_in_corridor,
    isGenuinelySublacunary_of_corridor mSeq_in_corridor, ?_⟩
  intro ξ hξ
  rw [Metric.dense_iff]
  intro y r hr
  obtain ⟨x0, rfl⟩ := QuotientAddGroup.mk_surjective y
  let δ : ℝ := min (r / 2) (1 / 4)
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδr : δ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let H : ℕ := ⌈1 / δ ^ 2⌉₊ + 2
  have hH2 : 2 ≤ H := by dsimp [H]; omega
  have hH1 : 1 ≤ H := by omega
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have hH_fejer : 1 / (4 * (H : ℝ) * δ ^ 2) ≤ 1 / 4 := by
    have h1 : 1 / δ ^ 2 ≤ (H : ℝ) := by
      have := Nat.le_ceil (1 / δ ^ 2)
      dsimp [H]; push_cast; linarith
    have h2 : 1 ≤ (H : ℝ) * δ ^ 2 := by
      rwa [div_le_iff₀ (sq_pos_of_pos hδpos)] at h1
    rw [one_div_le_one_div (by positivity) (by norm_num)]
    linarith
  have hIco_ne : (Finset.Ico 1 H).Nonempty := Finset.nonempty_Ico.mpr (by omega)
  let vals : Finset ℝ := (Finset.Ico 1 H).image (fun h : ℕ => |Real.sin (Real.pi * (h : ℝ) * ξ)|)
  have hvals_ne : vals.Nonempty := hIco_ne.image _
  let dmin : ℝ := vals.min' hvals_ne
  have hdmin_pos : 0 < dmin := by
    have hmem := Finset.min'_mem vals hvals_ne
    rw [Finset.mem_image] at hmem
    rcases hmem with ⟨h, hh, heq⟩
    dsimp [dmin]
    rw [← heq]
    exact abs_pos.mpr (sin_pi_mul_ne_zero_of_irrational hξ (Finset.mem_Ico.mp hh).1)
  have hdmin_le : ∀ h ∈ Finset.Ico 1 H, dmin ≤ |Real.sin (Real.pi * (h : ℝ) * ξ)| := fun h hh =>
    Finset.min'_le vals _ (Finset.mem_image.mpr ⟨h, hh, rfl⟩)
  let D : ℕ := ⌈1 / dmin⌉₊
  let j : ℕ := Nat.pair (H - 2) D
  have hblockH : blockH j = H := by
    dsimp [blockH, j]
    rw [Nat.unpair_pair]
    omega
  have hblockD : 1 / (blockD j : ℝ) ≤ dmin := by
    have h1 : 1 / dmin ≤ (blockD j : ℝ) := by
      have hc : 1 / dmin ≤ (D : ℝ) := Nat.le_ceil _
      have hDj : blockD j = D + 2 := by dsimp [blockD, j]; rw [Nat.unpair_pair]
      rw [hDj]; push_cast; linarith
    have hDpos : (0 : ℝ) < (blockD j : ℝ) := lt_of_lt_of_le (by positivity) h1
    rw [div_le_iff₀ hDpos]
    rw [div_le_iff₀ hdmin_pos] at h1
    linarith
  have hgood := (blocks j).hgood ξ (fun h hh => by
    rw [hblockH] at hh
    exact hblockD.trans (hdmin_le h hh))
  let K : ℕ := (blocks j).K
  let p : Fin K → ℕ := (blocks j).p
  have hKpos : 1 ≤ K := (blocks j).hKpos
  have hKR_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hterm_bound : ∀ h ∈ Finset.Ico 1 H,
      |(1 - (h : ℝ) / (H : ℝ)) * ∑ k : Fin K, Real.cos (2 * Real.pi * (h : ℝ) * (ξ * (p k : ℝ) - x0))| ≤
        (K : ℝ) / (4 * (H : ℝ)) := by
    intro h hh
    have hh' : h ∈ Finset.Ico 1 (blockH j) := by rwa [hblockH]
    have hgh := hgood h hh'
    rw [hblockH] at hgh
    have hhh : 1 ≤ h ∧ h < H := Finset.mem_Ico.mp hh
    have hw0 : 0 ≤ 1 - (h : ℝ) / (H : ℝ) := by
      have hhH : (h : ℝ) ≤ (H : ℝ) := by exact_mod_cast le_of_lt hhh.2
      rw [sub_nonneg, div_le_one hHpos]
      exact hhH
    have hw1 : 1 - (h : ℝ) / (H : ℝ) ≤ 1 := by
      have : 0 ≤ (h : ℝ) / (H : ℝ) := by positivity
      linarith
    have hcos_exp : ∑ k : Fin K, Real.cos (2 * Real.pi * (h : ℝ) * (ξ * (p k : ℝ) - x0)) =
        (∑ k : Fin K, Real.cos (2 * Real.pi * (h : ℝ) * ξ * (p k : ℝ))) * Real.cos (2 * Real.pi * (h : ℝ) * x0) +
        (∑ k : Fin K, Real.sin (2 * Real.pi * (h : ℝ) * ξ * (p k : ℝ))) * Real.sin (2 * Real.pi * (h : ℝ) * x0) := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have harg : 2 * Real.pi * (h : ℝ) * (ξ * (p k : ℝ) - x0) =
          2 * Real.pi * (h : ℝ) * ξ * (p k : ℝ) - 2 * Real.pi * (h : ℝ) * x0 := by ring
      rw [harg, Real.cos_sub]
    have hsum_abs : |∑ k : Fin K, Real.cos (2 * Real.pi * (h : ℝ) * (ξ * (p k : ℝ) - x0))| ≤
        (K : ℝ) / (4 * (H : ℝ)) := by
      rw [hcos_exp]
      have hc1 : |(∑ k : Fin K, Real.cos (2 * Real.pi * (h : ℝ) * ξ * (p k : ℝ))) *
          Real.cos (2 * Real.pi * (h : ℝ) * x0)| ≤ (K : ℝ) / (8 * (H : ℝ)) := by
        rw [abs_mul]
        calc |∑ k : Fin K, Real.cos (2 * Real.pi * (h : ℝ) * ξ * (p k : ℝ))| *
                |Real.cos (2 * Real.pi * (h : ℝ) * x0)|
            ≤ ((K : ℝ) / (8 * (H : ℝ))) * 1 :=
              mul_le_mul hgh.1 (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
          _ = (K : ℝ) / (8 * (H : ℝ)) := mul_one _
      have hs1 : |(∑ k : Fin K, Real.sin (2 * Real.pi * (h : ℝ) * ξ * (p k : ℝ))) *
          Real.sin (2 * Real.pi * (h : ℝ) * x0)| ≤ (K : ℝ) / (8 * (H : ℝ)) := by
        rw [abs_mul]
        calc |∑ k : Fin K, Real.sin (2 * Real.pi * (h : ℝ) * ξ * (p k : ℝ))| *
                |Real.sin (2 * Real.pi * (h : ℝ) * x0)|
            ≤ ((K : ℝ) / (8 * (H : ℝ))) * 1 :=
              mul_le_mul hgh.2 (Real.abs_sin_le_one _) (abs_nonneg _) (by positivity)
          _ = (K : ℝ) / (8 * (H : ℝ)) := mul_one _
      have htri := abs_add_le
        ((∑ k : Fin K, Real.cos (2 * Real.pi * (h : ℝ) * ξ * (p k : ℝ))) * Real.cos (2 * Real.pi * (h : ℝ) * x0))
        ((∑ k : Fin K, Real.sin (2 * Real.pi * (h : ℝ) * ξ * (p k : ℝ))) * Real.sin (2 * Real.pi * (h : ℝ) * x0))
      have hadd : (K : ℝ) / (8 * (H : ℝ)) + (K : ℝ) / (8 * (H : ℝ)) = (K : ℝ) / (4 * (H : ℝ)) := by ring
      linarith
    rw [abs_mul, abs_of_nonneg hw0]
    calc (1 - (h : ℝ) / (H : ℝ)) * |∑ k : Fin K, Real.cos (2 * Real.pi * (h : ℝ) * (ξ * (p k : ℝ) - x0))|
        ≤ 1 * ((K : ℝ) / (4 * (H : ℝ))) := mul_le_mul hw1 hsum_abs (abs_nonneg _) zero_le_one
      _ = (K : ℝ) / (4 * (H : ℝ)) := one_mul _
  have hfejer_sum : (K : ℝ) / 2 ≤ ∑ k : Fin K, fejer H (ξ * (p k : ℝ) - x0) := by
    have hexpand : ∑ k : Fin K, fejer H (ξ * (p k : ℝ) - x0) =
        (K : ℝ) + 2 * ∑ h ∈ Finset.Ico 1 H,
          (1 - (h : ℝ) / (H : ℝ)) * ∑ k : Fin K, Real.cos (2 * Real.pi * (h : ℝ) * (ξ * (p k : ℝ) - x0)) := by
      simp only [fejer, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, ← Finset.mul_sum]
      congr 2
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.mul_sum]
    have hosc : |∑ h ∈ Finset.Ico 1 H,
        (1 - (h : ℝ) / (H : ℝ)) * ∑ k : Fin K, Real.cos (2 * Real.pi * (h : ℝ) * (ξ * (p k : ℝ) - x0))| ≤
        (K : ℝ) / 4 := by
      calc |∑ h ∈ Finset.Ico 1 H,
              (1 - (h : ℝ) / (H : ℝ)) * ∑ k : Fin K, Real.cos (2 * Real.pi * (h : ℝ) * (ξ * (p k : ℝ) - x0))|
          ≤ ∑ h ∈ Finset.Ico 1 H,
              |(1 - (h : ℝ) / (H : ℝ)) * ∑ k : Fin K, Real.cos (2 * Real.pi * (h : ℝ) * (ξ * (p k : ℝ) - x0))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _h ∈ Finset.Ico 1 H, ((K : ℝ) / (4 * (H : ℝ))) := Finset.sum_le_sum hterm_bound
        _ = ((Finset.Ico 1 H).card : ℝ) * ((K : ℝ) / (4 * (H : ℝ))) := by simp
        _ ≤ (H : ℝ) * ((K : ℝ) / (4 * (H : ℝ))) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [Nat.card_Ico]
            exact_mod_cast Nat.sub_le H 1
        _ = (K : ℝ) / 4 := by field_simp [ne_of_gt hHpos]
    rw [hexpand]
    have := (abs_le.mp hosc).1
    linarith
  have hsum_lt : ∑ _k : Fin K, (1 / 4 : ℝ) < ∑ k : Fin K, fejer H (ξ * (p k : ℝ) - x0) := by
    have hconst : ∑ _k : Fin K, (1 / 4 : ℝ) = (K : ℝ) / 4 := by
      simp [Finset.sum_const, nsmul_eq_mul]; ring
    rw [hconst]
    linarith
  obtain ⟨k, _, hk_gt⟩ := Finset.exists_lt_of_sum_lt hsum_lt
  have hsin_lt : |Real.sin (Real.pi * (ξ * (p k : ℝ) - x0))| < 2 * δ := by
    by_contra hge
    have hfe := fejer_le_of_sin_ge hH1 hδpos (not_lt.mp hge)
    linarith
  have hround_lt : |(ξ * (p k : ℝ) - x0) - round (ξ * (p k : ℝ) - x0)| < δ :=
    abs_sub_round_lt_of_sin_lt hδpos hsin_lt
  refine ⟨↑(ξ * (mSeq (K + k.1) : ℝ)), ?_, ⟨K + k.1, rfl⟩⟩
  rw [Metric.mem_ball, dist_eq_norm, mSeq_on_block j k]
  change ‖((ξ * (p k : ℝ) : ℝ) : AddCircle (1 : ℝ)) - ((x0 : ℝ) : AddCircle (1 : ℝ))‖ < r
  rw [← QuotientAddGroup.mk_sub]
  have hnorm : ‖((ξ * (p k : ℝ) - x0 : ℝ) : AddCircle (1 : ℝ))‖ =
      |(ξ * (p k : ℝ) - x0) - round (ξ * (p k : ℝ) - x0)| := by
    rw [AddCircle.norm_eq]
    simp
  rw [hnorm]
  exact hround_lt.trans hδr

end OMABugeaud106

theorem OMA.solution : type_of% @Bugeaud06.problem_10_6_variant_1 :=
  OMABugeaud106.main
