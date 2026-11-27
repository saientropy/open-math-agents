import FormalConjectures.Other.VCDimConvex

/-!
# Proof of `VCDimConvex.exists_exponential_bound_hasAddVCNDimAtMost_n_of_convex_rn_add_one`

For every `n ≥ 1` and every convex set `C ⊆ ℝ^{n+1}`, we prove `HasAddVCNDimAtMost C n (65536 ^ n)`,
improving the previously known double-exponential bound `2^{8(n+2)^n} - 1` to single-exponential
`c ^ n` with `c = 65536`.

## Proof outline
1. **Elementary combinatorics & arithmetic**:
   - Binomial tail bound `∑ j < n, (n * m).choose j ≤ 3 ^ n * m ^ (n - 1)` via `(1 + 1/m)^m ≤ e < 3`.
   - Arrangement polynomial bound `∑_{j ≤ D} 2^j * M.choose j ≤ (2*M + 1)^D` and exponential margin
     inequality for `c = 65536`, `m = 65536 ^ n`, `t = 36 * n * (n + 1)`.
2. **Hyperplane avoidance & sign-vector arrangement bound**:
   - Polynomial moment-curve lemma avoiding any finite collection of proper affine hyperplanes
     inside any `(-η, η)^D` box.
   - Elementary Zaslavsky sign-vector bound: `M` linear functionals on a `D`-dimensional subspace
     produce at most `∑_{j ≤ D} 2^j * M.choose j ≤ (2*M + 1)^D` sign patterns in `{-1, 0, 1}^M`.
3. **Seidel's Upper Bound Theorem & Minkowski-sum vertex bound**:
   - For any bounded simple polytope `P = {x ∈ ℝ^D | ∀ a, ⟨A a, x⟩ ≤ b a}` with `N` facets,
     a generic functional `φ` gives an injection from basis vertices to subsets of size `≤ D / 2`
     (either via unique `φ`-max or unique `φ`-min on the face of outgoing/incoming tight facets),
     yielding at most `2 * ∑_{j ≤ D/2} N.choose j` basis vertices.
   - Applying this to the perturbed Cayley-dual polytope `P_ε ⊆ ℝ^{r' + n - 1}` (`r' ≤ n`,
     `D ≤ 2n - 1`, `N = n * m`) shows that any Minkowski sum `Q₁ + ⋯ + Qₙ ⊆ ℝ^r` (`r ≤ n`,
     `|Q_k| = m ≥ 2`) has at most `12 ^ n * m ^ (n - 1)` strict extreme grid tuples.
4. **Balanced alternating partitions, deterministic Clarkson-Shor, & Master Dual Separation**:
   - For each coordinate `k`, a finite counting argument over the `≤ (2*m^2 + 1)^{n+1}` sign-determined
     top-`t` sets yields a balanced partition `Fin m = E_k ⊔ O_k` (`|E_k| = |O_k| = m/2`) such that for
     every direction `u ∈ ℝ^{n+1}`, fewer than `t` elements of `E_k` strictly beat all of `O_k`.
   - Deterministic Clarkson-Shor subsampling over `s = m / (2t)` lifts the Minkowski-sum bound to at
     most `4 * t * 36 ^ n * m ^ (n - 1)` `t`-shallow grid tuples in `ℝ^n`.
   - On `A = E_0 × ⋯ × E_{n-1}` (`|A| = (m/2)^n`), Master Dual Separation applied to `S_B = G \ B` and
     `T_B = G \ (A \ B)` with shift `v_B = y(T_B) - y(S_B) ≠ 0` gives `B ⊆ I⁻(v_B)` and
     `A \ B ⊆ I⁺(v_B)` for cones `K_i` defined against `O_k`.
   - Compact-slice extreme-ray reduction shows `(I⁻(v), I⁺(v))` is determined by `signMap R v` on at
     most `(n * m^2)^n` normal rays `R`, while every `i ∈ I⁻(v) ∩ I⁺(v)` has a normal in `K_i ∩ v⊥`
     and is therefore a `t`-shallow tuple in `v⊥ ≃ ℝ^n`, giving
     `2^{(m/2)^n} ≤ (2*(n*m^2)^n + 1)^{n+1} * 2^{4 * t * 36^n * m^{n-1}}`, contradicting `final_exp_ineq`.
-/

open scoped BigOperators

namespace VCDimConvexExpProof

/-- Standard inner product on `Fin D → ℝ`. -/
private def dot {D : ℕ} (u v : Fin D → ℝ) : ℝ := ∑ k : Fin D, u k * v k

private lemma dot_comm {D : ℕ} (u v : Fin D → ℝ) : dot u v = dot v u := by
  simp only [dot, mul_comm]

private lemma dot_add_left {D : ℕ} (u v w : Fin D → ℝ) : dot (u + v) w = dot u w + dot v w := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma dot_add_right {D : ℕ} (u v w : Fin D → ℝ) : dot u (v + w) = dot u v + dot u w := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma dot_sub_left {D : ℕ} (u v w : Fin D → ℝ) : dot (u - v) w = dot u w - dot v w := by
  simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma dot_sub_right {D : ℕ} (u v w : Fin D → ℝ) : dot u (v - w) = dot u v - dot u w := by
  simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private lemma dot_smul_left {D : ℕ} (c : ℝ) (u v : Fin D → ℝ) : dot (c • u) v = c * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

private lemma dot_smul_right {D : ℕ} (c : ℝ) (u v : Fin D → ℝ) : dot u (c • v) = c * dot u v := by
  rw [dot_comm, dot_smul_left, dot_comm]

private lemma dot_zero_left {D : ℕ} (v : Fin D → ℝ) : dot 0 v = 0 := by simp [dot]

private lemma dot_zero_right {D : ℕ} (u : Fin D → ℝ) : dot u 0 = 0 := by simp [dot]

private lemma dot_neg_left {D : ℕ} (u v : Fin D → ℝ) : dot (-u) v = -dot u v := by
  simp only [dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

private lemma dot_neg_right {D : ℕ} (u v : Fin D → ℝ) : dot u (-v) = -dot u v := by
  rw [dot_comm, dot_neg_left, dot_comm]

private lemma dot_sum_left {D : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin D → ℝ)
    (v : Fin D → ℝ) : dot (∑ i ∈ s, f i) v = ∑ i ∈ s, dot (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dot_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, dot_add_left, ih, Finset.sum_insert ha]

private lemma dot_sum_right {D : ℕ} {ι : Type*} (s : Finset ι) (u : Fin D → ℝ)
    (f : ι → Fin D → ℝ) : dot u (∑ i ∈ s, f i) = ∑ i ∈ s, dot u (f i) := by
  rw [dot_comm, dot_sum_left]
  exact Finset.sum_congr rfl fun i _ => dot_comm (f i) u

private lemma dot_self_nonneg {D : ℕ} (u : Fin D → ℝ) : 0 ≤ dot u u :=
  Finset.sum_nonneg fun k _ => mul_self_nonneg (u k)

private lemma dot_self_eq_zero {D : ℕ} {u : Fin D → ℝ} (h : dot u u = 0) : u = 0 := by
  ext k
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin D)), 0 ≤ u j * u j := fun j _ => mul_self_nonneg _
  have hk := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h k (Finset.mem_univ k)
  exact mul_self_eq_zero.mp hk

private lemma dot_linear_rep {D : ℕ} (f : (Fin D → ℝ) →ₗ[ℝ] ℝ) :
    ∃ u : Fin D → ℝ, ∀ v : Fin D → ℝ, f v = dot u v := by
  refine ⟨fun k => f (Pi.single k 1), fun v => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  simp only [dot]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : Pi.single k (v k) = (v k) • Pi.single k (1 : ℝ) := by
    ext j
    by_cases hj : j = k <;> simp [hj]
  rw [h1, map_smul, smul_eq_mul, mul_comm]

private lemma dot_continuous {D : ℕ} (u : Fin D → ℝ) : Continuous (fun v : Fin D → ℝ => dot u v) := by
  unfold dot
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_apply k)

/- ### Module 1: Elementary Combinatorics & Arithmetic -/

private lemma sum_choose_le (n m : ℕ) (hm : 1 ≤ m) :
    ∑ j ∈ Finset.range n, (n * m).choose j ≤ 3 ^ n * m ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  suffices hR : ((∑ j ∈ Finset.range n, (n * m).choose j : ℕ) : ℝ) ≤
      (3 : ℝ) ^ n * (m : ℝ) ^ (n - 1) by
    exact_mod_cast hR
  have h1 : (1 / (m : ℝ)) ^ (n - 1) * ((∑ j ∈ Finset.range n, (n * m).choose j : ℕ) : ℝ) ≤
      ∑ j ∈ Finset.range n, ((n * m).choose j : ℝ) * (1 / (m : ℝ)) ^ j := by
    rw [Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [mul_comm]
    have hle : (1 / (m : ℝ)) ^ (n - 1) ≤ (1 / (m : ℝ)) ^ j := by
      have h01 : (1 / (m : ℝ)) ≤ 1 := by
        rw [div_le_one hmR]; exact_mod_cast hm
      exact pow_le_pow_of_le_one (by positivity) h01 (by omega)
    exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
  have h2 : ∑ j ∈ Finset.range n, ((n * m).choose j : ℝ) * (1 / (m : ℝ)) ^ j ≤
      (1 + 1 / (m : ℝ)) ^ (n * m) := by
    rw [add_comm (1 : ℝ), add_pow]
    have hsub : Finset.range n ⊆ Finset.range (n * m + 1) := by
      intro j hj
      rw [Finset.mem_range] at hj ⊢
      have : n ≤ n * m := Nat.le_mul_of_pos_right n hm
      omega
    calc ∑ j ∈ Finset.range n, ((n * m).choose j : ℝ) * (1 / (m : ℝ)) ^ j
        = ∑ j ∈ Finset.range n, (1 / (m : ℝ)) ^ j * (1 : ℝ) ^ (n * m - j) * ((n * m).choose j : ℝ) := by
          refine Finset.sum_congr rfl fun j _ => by ring
      _ ≤ ∑ j ∈ Finset.range (n * m + 1),
            (1 / (m : ℝ)) ^ j * (1 : ℝ) ^ (n * m - j) * ((n * m).choose j : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have h3 : (1 + 1 / (m : ℝ)) ^ (n * m) ≤ (3 : ℝ) ^ n := by
    rw [mul_comm n m, pow_mul]
    have hbase : (1 + 1 / (m : ℝ)) ^ m ≤ 3 := by
      have hexp : 1 + 1 / (m : ℝ) ≤ Real.exp (1 / (m : ℝ)) := by
        linarith [Real.add_one_le_exp (1 / (m : ℝ))]
      calc (1 + 1 / (m : ℝ)) ^ m
          ≤ (Real.exp (1 / (m : ℝ))) ^ m := pow_le_pow_left₀ (by positivity) hexp m
        _ = Real.exp ((m : ℝ) * (1 / (m : ℝ))) := (Real.exp_nat_mul _ m).symm
        _ = Real.exp 1 := by congr 1; field_simp
        _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
    exact pow_le_pow_left₀ (by positivity) hbase n
  have hcomb := le_trans (le_trans h1 h2) h3
  have hpow_pos : (0 : ℝ) < (m : ℝ) ^ (n - 1) := pow_pos hmR (n - 1)
  have hinv : (1 / (m : ℝ)) ^ (n - 1) = ((m : ℝ) ^ (n - 1))⁻¹ := by
    rw [one_div, inv_pow]
  rw [hinv] at hcomb
  have := mul_le_mul_of_nonneg_left hcomb hpow_pos.le
  rw [← mul_assoc, mul_inv_cancel₀ hpow_pos.ne', one_mul, mul_comm ((m : ℝ) ^ (n - 1))] at this
  exact this

private lemma choose_le_pow (M j : ℕ) : M.choose j ≤ M ^ j := by
  have h2 : M.descFactorial j ≤ M ^ j := by
    induction j with
    | zero => simp
    | succ k ih =>
      rw [Nat.descFactorial_succ, pow_succ']
      exact Nat.mul_le_mul (Nat.sub_le M k) ih
  have h1 : M.choose j ≤ M.descFactorial j := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.le_mul_of_pos_left _ (Nat.factorial_pos j)
  exact le_trans h1 h2

private lemma succ_mul_choose_succ (n k : ℕ) :
    (k + 1) * (n + 1).choose (k + 1) = (n + 1) * n.choose k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp
    | succ j => simp [Nat.choose_eq_zero_of_lt]
  | succ n ih =>
    cases k with
    | zero => simp
    | succ j =>
      have h1 := ih j
      have h2 := ih (j + 1)
      rw [Nat.choose_succ_succ (n + 1) (j + 1)]
      have h4 : (j + 1 + 1) * ((n + 1).choose (j + 1) + (n + 1).choose (j + 1).succ) =
          (j + 1) * (n + 1).choose (j + 1) + (n + 1).choose (j + 1) +
            (j + 1 + 1) * (n + 1).choose (j + 1 + 1) := by
        change (j + 1 + 1) * ((n + 1).choose (j + 1) + (n + 1).choose (j + 1 + 1)) = _
        ring
      rw [h4, h1, h2, Nat.choose_succ_succ n j]
      ring

private lemma card_filter_add_not {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter fun x => ¬ p x).card = s.card := by
  have hdisj : Disjoint (s.filter p) (s.filter fun x => ¬ p x) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_filter.mp hx2).2 (Finset.mem_filter.mp hx1).2
  have hunion : s.filter p ∪ s.filter (fun x => ¬ p x) = s := by
    ext x
    by_cases hp : p x <;> simp [hp]
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

private lemma continuous_sup' {α β : Type*} [TopologicalSpace α] {s : Finset β}
    (hs : s.Nonempty) (f : β → α → ℝ) (hf : ∀ b ∈ s, Continuous (f b)) :
    Continuous (fun a => s.sup' hs (fun b => f b a)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton b => simpa using hf b (Finset.mem_singleton_self b)
  | cons b s hb hs ih =>
    have hfun : (fun a => (s.cons b hb).sup' ⟨b, Finset.mem_cons_self b s⟩ (fun x => f x a)) =
        (fun a => max (f b a) (s.sup' hs (fun x => f x a))) := by
      ext a
      rw [Finset.sup'_cons (H := hs)]
    rw [hfun]
    exact (hf b (Finset.mem_cons_self b s)).max
      (ih fun x hx => hf x (Finset.mem_cons_of_mem hx))

private lemma sum_neg_of_nonpos {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (hle : ∀ i ∈ s, f i ≤ 0) (hex : ∃ i ∈ s, f i < 0) : ∑ i ∈ s, f i < 0 := by
  simpa using Finset.sum_lt_sum (f := f) (g := fun _ => (0 : ℝ)) hle hex

private lemma two_pow_mul_choose_half (q t : ℕ) (ht : t ≤ q) :
    2 ^ t * (2 * q - t).choose (q - t) ≤ (2 * q).choose q := by
  induction t with
  | zero => simp
  | succ k ih =>
    have hk : k ≤ q := by omega
    have hih := ih hk
    have hstep : 2 * (2 * q - (k + 1)).choose (q - (k + 1)) ≤ (2 * q - k).choose (q - k) := by
      have h1 : (2 * q - k) * (2 * q - k - 1).choose (q - k - 1) =
          (q - k) * (2 * q - k).choose (q - k) := by
        have ha : 2 * q - k = (2 * q - k - 1) + 1 := by omega
        have hb : q - k = (q - k - 1) + 1 := by omega
        conv_lhs => rw [ha]
        conv_rhs => rw [ha, hb]
        exact (succ_mul_choose_succ (2 * q - k - 1) (q - k - 1)).symm
      have hsub1 : 2 * q - (k + 1) = 2 * q - k - 1 := by omega
      have hsub2 : q - (k + 1) = q - k - 1 := by omega
      rw [hsub1, hsub2]
      have hle2 : 2 * (q - k) ≤ 2 * q - k := by omega
      have hmul : (2 * q - k) * (2 * (2 * q - k - 1).choose (q - k - 1)) ≤
          (2 * q - k) * (2 * q - k).choose (q - k) := by
        have : (2 * q - k) * (2 * (2 * q - k - 1).choose (q - k - 1)) =
            2 * ((2 * q - k) * (2 * q - k - 1).choose (q - k - 1)) := by ring
        rw [this, h1]
        nlinarith
      exact Nat.le_of_mul_le_mul_left hmul (by omega)
    calc 2 ^ (k + 1) * (2 * q - (k + 1)).choose (q - (k + 1))
        = 2 ^ k * (2 * (2 * q - (k + 1)).choose (q - (k + 1))) := by rw [pow_succ]; ring
      _ ≤ 2 ^ k * (2 * q - k).choose (q - k) := Nat.mul_le_mul_left _ hstep
      _ ≤ (2 * q).choose q := hih

private lemma four_mul_t_le (n : ℕ) (hn : 1 ≤ n) : 144 * n * (n + 1) ≤ 65536 ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · have hih := ih hk
      have hstep : 144 * (k + 1) * (k + 1 + 1) ≤ 3 * (144 * k * (k + 1)) := by nlinarith
      calc 144 * (k + 1) * (k + 1 + 1)
          ≤ 3 * (144 * k * (k + 1)) := hstep
        _ ≤ 3 * 65536 ^ k := Nat.mul_le_mul_left 3 hih
        _ ≤ 65536 * 65536 ^ k := Nat.mul_le_mul_right _ (by norm_num)
        _ = 65536 ^ (k + 1) := (pow_succ' 65536 k).symm

private lemma sum_two_pow_mul_choose_le (M D : ℕ) :
    ∑ j ∈ Finset.range (D + 1), 2 ^ j * M.choose j ≤ (2 * M + 1) ^ D := by
  have h1 : ∀ j ∈ Finset.range (D + 1), 2 ^ j * M.choose j ≤ D.choose j * (2 * M) ^ j := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hpos : 1 ≤ D.choose j := Nat.choose_pos (by omega)
    have hcm : M.choose j ≤ M ^ j := choose_le_pow M j
    calc 2 ^ j * M.choose j
        ≤ 2 ^ j * M ^ j := Nat.mul_le_mul_left _ hcm
      _ = (2 * M) ^ j := (Nat.mul_pow 2 M j).symm
      _ = 1 * (2 * M) ^ j := (one_mul _).symm
      _ ≤ D.choose j * (2 * M) ^ j := Nat.mul_le_mul_right _ hpos
  calc ∑ j ∈ Finset.range (D + 1), 2 ^ j * M.choose j
      ≤ ∑ j ∈ Finset.range (D + 1), D.choose j * (2 * M) ^ j := Finset.sum_le_sum h1
    _ = ∑ j ∈ Finset.range (D + 1), (2 * M) ^ j * 1 ^ (D - j) * D.choose j := by
        refine Finset.sum_congr rfl fun j _ => by ring
    _ = (2 * M + 1) ^ D := (add_pow (2 * M) 1 D).symm

private lemma three_mul_le_four_pow (n : ℕ) (hn : 1 ≤ n) : 3 * n ≤ 4 ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · have := ih hk
      calc 3 * (k + 1) ≤ 4 * (3 * k) := by omega
        _ ≤ 4 * 4 ^ k := Nat.mul_le_mul_left 4 this
        _ = 4 ^ (k + 1) := by ring

private lemma poly_lt_exp_base (n : ℕ) (hn : 1 ≤ n) :
    34 * n ^ 2 * (n + 1) < 16384 * 32768 ^ (n - 1) := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · have hih := ih hk
      have hstep : 34 * (k + 1) ^ 2 * (k + 1 + 1) ≤ 6 * (34 * k ^ 2 * (k + 1)) := by nlinarith
      have hpow : 32768 ^ k = 32768 * 32768 ^ (k - 1) := by
        cases k with
        | zero => omega
        | succ j => simp [pow_succ, mul_comm]
      simp only [Nat.add_sub_cancel]
      rw [hpow]
      omega

private lemma shallow_term_lt (n : ℕ) (hn : 1 ≤ n) :
    288 * n * (n + 1) * 36 ^ n < 32768 ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · have hih := ih hk
      have h1 : 288 * (k + 1) * (k + 1 + 1) ≤ 3 * (288 * k * (k + 1)) := by nlinarith
      have hmul : 288 * (k + 1) * (k + 1 + 1) * 36 ^ (k + 1) ≤
          108 * (288 * k * (k + 1) * 36 ^ k) := by
        calc 288 * (k + 1) * (k + 1 + 1) * 36 ^ (k + 1)
            = (288 * (k + 1) * (k + 1 + 1)) * (36 * 36 ^ k) := by rw [pow_succ']
          _ ≤ (3 * (288 * k * (k + 1))) * (36 * 36 ^ k) := Nat.mul_le_mul_right _ h1
          _ = 108 * (288 * k * (k + 1) * 36 ^ k) := by ring
      calc 288 * (k + 1) * (k + 1 + 1) * 36 ^ (k + 1)
          ≤ 108 * (288 * k * (k + 1) * 36 ^ k) := hmul
        _ < 108 * 32768 ^ k := Nat.mul_lt_mul_of_pos_left hih (by norm_num)
        _ ≤ 32768 * 32768 ^ k := Nat.mul_le_mul_right _ (by norm_num)
        _ = 32768 ^ (k + 1) := (pow_succ' 32768 k).symm

private lemma final_exp_ineq (n : ℕ) (hn : 1 ≤ n) :
    (2 * (n * (65536 ^ n) ^ 2) ^ n + 1) ^ (n + 1) *
      2 ^ (4 * (36 * n * (n + 1)) * 36 ^ n * (65536 ^ n) ^ (n - 1)) <
      2 ^ ((65536 ^ n / 2) ^ n) := by
  set m := 65536 ^ n
  have hm_pos : 1 ≤ m := Nat.one_le_pow n 65536 (by norm_num)
  have hm_half : m / 2 = 32768 * 65536 ^ (n - 1) := by
    cases n with
    | zero => omega
    | succ k =>
      simp only [m, Nat.add_sub_cancel, pow_succ]
      have : 65536 ^ k * 65536 = 2 * (32768 * 65536 ^ k) := by ring
      rw [this, Nat.mul_div_right _ (by norm_num)]
  have hhalf_pow : (m / 2) ^ n = 32768 ^ n * m ^ (n - 1) := by
    have h2 : m = 2 * (m / 2) := by
      cases n with
      | zero => omega
      | succ k =>
        simp only [m, pow_succ]
        have : 65536 ^ k * 65536 = 2 * (32768 * 65536 ^ k) := by ring
        rw [this, Nat.mul_div_right _ (by norm_num)]
    have hmn : m ^ n = 2 ^ n * (m / 2) ^ n := by
      conv_lhs => rw [h2]
      rw [Nat.mul_pow]
    have hmn2 : m ^ n = m * m ^ (n - 1) := by
      cases n with
      | zero => omega
      | succ k => simp [pow_succ, mul_comm]
    have h2n : m = 2 ^ n * 32768 ^ n := by
      dsimp [m]; rw [← Nat.mul_pow]
    have hmul : 2 ^ n * (m / 2) ^ n = 2 ^ n * (32768 ^ n * m ^ (n - 1)) := by
      calc 2 ^ n * (m / 2) ^ n = m ^ n := hmn.symm
        _ = m * m ^ (n - 1) := hmn2
        _ = (2 ^ n * 32768 ^ n) * m ^ (n - 1) := by rw [h2n]
        _ = 2 ^ n * (32768 ^ n * m ^ (n - 1)) := by ring
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) n) hmul
  have h1 : 2 * (n * m ^ 2) ^ n + 1 ≤ (3 * n * m ^ 2) ^ n := by
    have hpos : 1 ≤ (n * m ^ 2) ^ n := Nat.one_le_pow n _ (Nat.mul_pos hn (pow_pos hm_pos 2))
    have h3 : 3 ≤ 3 ^ n := by
      calc 3 = 3 ^ 1 := by ring
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    calc 2 * (n * m ^ 2) ^ n + 1
        ≤ 3 * (n * m ^ 2) ^ n := by omega
      _ ≤ 3 ^ n * (n * m ^ 2) ^ n := Nat.mul_le_mul_right _ h3
      _ = (3 * (n * m ^ 2)) ^ n := (Nat.mul_pow 3 (n * m ^ 2) n).symm
      _ = (3 * n * m ^ 2) ^ n := by ring_nf
  have h2 : 3 * n * m ^ 2 ≤ 2 ^ (34 * n) := by
    have h3n := three_mul_le_four_pow n hn
    have h4 : 4 ^ n = 2 ^ (2 * n) := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    have hm2 : m ^ 2 = 2 ^ (32 * n) := by
      dsimp [m]; rw [show (65536 : ℕ) = 2 ^ 16 by norm_num, ← pow_mul, ← pow_mul]; ring_nf
    calc 3 * n * m ^ 2 ≤ 4 ^ n * m ^ 2 := Nat.mul_le_mul_right _ h3n
      _ = 2 ^ (2 * n) * 2 ^ (32 * n) := by rw [h4, hm2]
      _ = 2 ^ (34 * n) := by rw [← pow_add]; ring_nf
  have h3 : (2 * (n * m ^ 2) ^ n + 1) ^ (n + 1) ≤ 2 ^ (34 * n ^ 2 * (n + 1)) := by
    calc (2 * (n * m ^ 2) ^ n + 1) ^ (n + 1)
        ≤ ((3 * n * m ^ 2) ^ n) ^ (n + 1) := Nat.pow_le_pow_left h1 (n + 1)
      _ ≤ ((2 ^ (34 * n)) ^ n) ^ (n + 1) :=
          Nat.pow_le_pow_left (Nat.pow_le_pow_left h2 n) (n + 1)
      _ = 2 ^ (34 * n ^ 2 * (n + 1)) := by rw [← pow_mul, ← pow_mul]; congr 1; ring
  have h4 : 34 * n ^ 2 * (n + 1) + 4 * (36 * n * (n + 1)) * 36 ^ n * m ^ (n - 1) < (m / 2) ^ n := by
    rw [hhalf_pow]
    have hmp : 1 ≤ m ^ (n - 1) := Nat.one_le_pow _ _ hm_pos
    have h32 : 32768 ^ n = 2 * (16384 * 32768 ^ (n - 1)) := by
      cases n with
      | zero => omega
      | succ k => simp [pow_succ]; ring
    have hpart1 : 34 * n ^ 2 * (n + 1) < 16384 * 32768 ^ (n - 1) * m ^ (n - 1) :=
      lt_of_lt_of_le (poly_lt_exp_base n hn) (Nat.le_mul_of_pos_right _ hmp)
    have hpart2 : 4 * (36 * n * (n + 1)) * 36 ^ n < 16384 * 32768 ^ (n - 1) := by
      have hs := shallow_term_lt n hn
      have h2eq : 2 * (4 * (36 * n * (n + 1)) * 36 ^ n) = 288 * n * (n + 1) * 36 ^ n := by ring
      rw [h32, ← h2eq] at hs
      exact Nat.lt_of_mul_lt_mul_left hs
    have hpart2' : 4 * (36 * n * (n + 1)) * 36 ^ n * m ^ (n - 1) ≤
        16384 * 32768 ^ (n - 1) * m ^ (n - 1) := Nat.mul_le_mul_right _ hpart2.le
    have htot : 32768 ^ n * m ^ (n - 1) =
        16384 * 32768 ^ (n - 1) * m ^ (n - 1) + 16384 * 32768 ^ (n - 1) * m ^ (n - 1) := by
      rw [h32]; ring
    omega
  calc (2 * (n * m ^ 2) ^ n + 1) ^ (n + 1) * 2 ^ (4 * (36 * n * (n + 1)) * 36 ^ n * m ^ (n - 1))
      ≤ 2 ^ (34 * n ^ 2 * (n + 1)) * 2 ^ (4 * (36 * n * (n + 1)) * 36 ^ n * m ^ (n - 1)) :=
        Nat.mul_le_mul_right _ h3
    _ = 2 ^ (34 * n ^ 2 * (n + 1) + 4 * (36 * n * (n + 1)) * 36 ^ n * m ^ (n - 1)) :=
        (pow_add 2 _ _).symm
    _ < 2 ^ ((m / 2) ^ n) := Nat.pow_lt_pow_right (by norm_num) h4

/- ### Module 2: Polynomial-Curve Hyperplane Avoidance -/

private lemma exists_avoid_hyperplanes {D : ℕ} (L : Finset ((Fin D → ℝ) × ℝ))
    (hL : ∀ p ∈ L, p.1 ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ v : Fin D → ℝ, (∀ k : Fin D, |v k| < η) ∧ ∀ p ∈ L, dot p.1 v ≠ p.2 := by
  classical
  let polyOf : (Fin D → ℝ) × ℝ → Polynomial ℝ := fun p =>
    (∑ k : Fin D, Polynomial.C (p.1 k) * Polynomial.X ^ (k.1 + 1)) - Polynomial.C p.2
  have hpoly_ne : ∀ p ∈ L, polyOf p ≠ 0 := by
    intro p hp h0
    have hne : p.1 ≠ 0 := hL p hp
    have hex : ∃ k : Fin D, p.1 k ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (funext hall)
    obtain ⟨k0, hk0⟩ := hex
    have hcoeff := congrArg (fun P => Polynomial.coeff P (k0.1 + 1)) h0
    simp only [polyOf, Polynomial.coeff_zero, Polynomial.coeff_sub, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero] at hcoeff
    have hcC : Polynomial.coeff (Polynomial.C p.2) (k0.1 + 1) = 0 := by
      rw [Polynomial.coeff_C]; simp
    have hsum : ∑ k : Fin D, (if k0.1 + 1 = k.1 + 1 then p.1 k else 0) = p.1 k0 := by
      rw [Finset.sum_eq_single k0]
      · simp
      · intro k _ hkne
        have hne_idx : k0.1 + 1 ≠ k.1 + 1 := fun h => hkne (Fin.ext (by omega : k.1 = k0.1))
        rw [if_neg hne_idx]
      · intro h; exact (h (Finset.mem_univ k0)).elim
    rw [hsum, hcC, sub_zero] at hcoeff
    exact hk0 hcoeff
  let bad : Finset ℝ := L.biUnion fun p => (polyOf p).roots.toFinset
  have hinf : (Set.Ioo (0 : ℝ) (min 1 η)).Infinite :=
    Set.Ioo_infinite (lt_min zero_lt_one hη)
  obtain ⟨t, ht_mem, ht_not⟩ := hinf.exists_notMem_finset bad
  have ht0 : 0 < t := ht_mem.1
  have ht1 : t < 1 := lt_of_lt_of_le ht_mem.2 (min_le_left 1 η)
  have htη : t < η := lt_of_lt_of_le ht_mem.2 (min_le_right 1 η)
  refine ⟨fun k => t ^ (k.1 + 1), ?_, ?_⟩
  · intro k
    rw [abs_of_pos (pow_pos ht0 _)]
    have hle : t ^ (k.1 + 1) ≤ t ^ 1 := pow_le_pow_of_le_one ht0.le ht1.le (Nat.succ_le_succ (Nat.zero_le _))
    rw [pow_one] at hle
    exact lt_of_le_of_lt hle htη
  · intro p hp heq
    apply ht_not
    rw [Finset.mem_biUnion]
    refine ⟨p, hp, ?_⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (hpoly_ne p hp), Polynomial.IsRoot]
    simp only [polyOf, Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact sub_eq_zero.mpr heq

private lemma exists_generic_functional {D : ℕ} (W : Finset (Fin D → ℝ))
    (hW : ∀ w ∈ W, w ≠ 0) :
    ∃ φ : Fin D → ℝ, ∀ w ∈ W, dot φ w ≠ 0 := by
  classical
  let L : Finset ((Fin D → ℝ) × ℝ) := W.image fun w => (w, 0)
  have hL : ∀ p ∈ L, p.1 ≠ 0 := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨w, hw, rfl⟩
    exact hW w hw
  obtain ⟨φ, _, hφ⟩ := exists_avoid_hyperplanes L hL zero_lt_one
  refine ⟨φ, fun w hw => ?_⟩
  rw [dot_comm]
  exact hφ (w, 0) (Finset.mem_image.mpr ⟨w, hw, rfl⟩)

/- ### Module 3: Sign-Vector Hyperplane Arrangement Bound -/

private noncomputable def signOf (x : ℝ) : ℤ :=
  if 0 < x then 1 else if x < 0 then -1 else 0

private noncomputable def signMap {D : ℕ} (R : Finset (Fin D → ℝ)) (v : Fin D → ℝ) :
    (Fin D → ℝ) → ℤ :=
  fun r => if r ∈ R then signOf (dot r v) else 0

private lemma signOf_pos_comb {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : signOf x = signOf y) : signOf (a * x + b * y) = signOf x := by
  simp only [signOf] at h ⊢
  split_ifs at h ⊢ <;> nlinarith

private lemma card_sign_patterns_le {D : ℕ} (V : Submodule ℝ (Fin D → ℝ))
    (R : Finset (Fin D → ℝ)) :
    ∃ S : Finset ((Fin D → ℝ) → ℤ),
      (∀ v ∈ V, signMap R v ∈ S) ∧
      S.card ≤ ∑ j ∈ Finset.range (Module.finrank ℝ V + 1), 2 ^ j * R.card.choose j := by
  classical
  induction R using Finset.induction_on generalizing V with
  | empty =>
    refine ⟨{fun _ => 0}, ?_, ?_⟩
    · intro v _
      rw [Finset.mem_singleton]
      ext x
      simp [signMap]
    · rw [Finset.card_singleton]
      have h0 : 0 ∈ Finset.range (Module.finrank ℝ V + 1) := Finset.mem_range.mpr (Nat.succ_pos _)
      exact le_trans (by simp) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) h0)
  | insert r R hr ih =>
    obtain ⟨S1, hS1_mem, hS1_card⟩ := ih V
    let f_r : V →ₗ[ℝ] ℝ :=
      { toFun := fun v => dot r v.1
        map_add' := fun u v => dot_add_right r u.1 v.1
        map_smul' := fun c v => by simp [dot_smul_right] }
    by_cases hfr : f_r = 0
    · refine ⟨S1.image (fun g => Function.update g r 0), ?_, ?_⟩
      · intro v hv
        rw [Finset.mem_image]
        refine ⟨signMap R v, hS1_mem v hv, ?_⟩
        ext x
        have hdot0 : dot r v = 0 := congrArg (fun g => g ⟨v, hv⟩) hfr
        by_cases hx : x = r
        · subst hx; simp [signMap, signOf, hdot0]
        · simp [signMap, hx]
      · calc (S1.image _).card ≤ S1.card := Finset.card_image_le
          _ ≤ ∑ j ∈ Finset.range (Module.finrank ℝ V + 1), 2 ^ j * R.card.choose j := hS1_card
          _ ≤ ∑ j ∈ Finset.range (Module.finrank ℝ V + 1),
                2 ^ j * (insert r R).card.choose j := by
              rw [Finset.card_insert_of_notMem hr]
              exact Finset.sum_le_sum fun j _ =>
                Nat.mul_le_mul_left _ (Nat.choose_le_choose j (Nat.le_succ _))
    · let K : Submodule ℝ (Fin D → ℝ) := (LinearMap.ker f_r).map V.subtype
      have hK_le : K ≤ V := by
        rintro x ⟨v, _, rfl⟩; exact v.2
      have hK_rank : Module.finrank ℝ K + 1 = Module.finrank ℝ V := by
        have hker_iso : Module.finrank ℝ K = Module.finrank ℝ (LinearMap.ker f_r) :=
          LinearEquiv.finrank_eq (Submodule.equivMapOfInjective V.subtype Subtype.val_injective _).symm
        have hrange_ne : LinearMap.range f_r ≠ ⊥ := by
          intro hbot
          apply hfr
          ext v
          have : f_r v ∈ (⊥ : Submodule ℝ ℝ) := hbot ▸ LinearMap.mem_range_self f_r v
          simpa using this
        have hrange_top : LinearMap.range f_r = ⊤ := by
          have hle : Module.finrank ℝ (LinearMap.range f_r) ≤ 1 := by
            simpa using Submodule.finrank_le (LinearMap.range f_r)
          have hpos : 0 < Module.finrank ℝ (LinearMap.range f_r) :=
            Nat.pos_of_ne_zero fun h0 => hrange_ne (Submodule.finrank_eq_zero.mp h0)
          exact Submodule.eq_top_of_finrank_eq (by simp; omega)
        have hrk := LinearMap.finrank_range_add_finrank_ker f_r
        rw [hrange_top, finrank_top] at hrk
        simp only [Module.finrank_self] at hrk
        omega
      obtain ⟨S0, hS0_mem, hS0_card⟩ := ih K
      let S0' : Finset ((Fin D → ℝ) → ℤ) := S0 ∩ S1
      let pickVal : ((Fin D → ℝ) → ℤ) → ℤ := fun g =>
        if h : ∃ v ∈ V, signMap R v = g then signOf (dot r h.choose) else 0
      let S_all : Finset ((Fin D → ℝ) → ℤ) :=
        ((S1 \ S0').image (fun g => Function.update g r (pickVal g))) ∪
        ((S0'.image (fun g => Function.update g r 1)) ∪
         (S0'.image (fun g => Function.update g r (-1))) ∪
         (S0'.image (fun g => Function.update g r 0)))
      refine ⟨S_all, ?_, ?_⟩
      · intro v hv
        set g := signMap R v
        have hg1 : g ∈ S1 := hS1_mem v hv
        have heq_upd : signMap (insert r R) v = Function.update g r (signOf (dot r v)) := by
          ext x
          by_cases hx : x = r
          · subst hx; simp [signMap]
          · simp [signMap, g, hx]
        rw [heq_upd]
        by_cases hg0 : g ∈ S0'
        · apply Finset.mem_union_right
          have hsign_cases : signOf (dot r v) = 1 ∨ signOf (dot r v) = -1 ∨ signOf (dot r v) = 0 := by
            simp only [signOf]; split_ifs <;> simp
          rcases hsign_cases with h | h | h
          · rw [h]; exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨g, hg0, rfl⟩))
          · rw [h]; exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g, hg0, rfl⟩))
          · rw [h]; exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g, hg0, rfl⟩)
        · apply Finset.mem_union_left
          rw [Finset.mem_image]
          refine ⟨g, Finset.mem_sdiff.mpr ⟨hg1, hg0⟩, ?_⟩
          congr 1
          have hex : ∃ w ∈ V, signMap R w = g := ⟨v, hv, rfl⟩
          simp only [pickVal, dif_pos hex]
          set w := hex.choose
          have hwV : w ∈ V := hex.choose_spec.1
          have hwg : signMap R w = g := hex.choose_spec.2
          by_contra hne
          have hv0_ex : ∃ v0 ∈ K, signMap R v0 = g := by
            by_cases hdw : dot r w = 0
            · refine ⟨w, ⟨⟨w, hwV⟩, hdw, rfl⟩, hwg⟩
            · by_cases hdv : dot r v = 0
              · refine ⟨v, ⟨⟨v, hv⟩, hdv, rfl⟩, rfl⟩
              · have hopp : (dot r w < 0 ∧ 0 < dot r v) ∨ (0 < dot r w ∧ dot r v < 0) := by
                  simp only [signOf] at hne
                  rcases lt_trichotomy (dot r w) 0 with h1 | h1 | h1 <;>
                    rcases lt_trichotomy (dot r v) 0 with h2 | h2 | h2
                  · exfalso; apply hne; simp [not_lt_of_gt h1, h1, not_lt_of_gt h2, h2]
                  · exact (hdv h2).elim
                  · exact .inl ⟨h1, h2⟩
                  · exact (hdw h1).elim
                  · exact (hdw h1).elim
                  · exact (hdw h1).elim
                  · exact .inr ⟨h1, h2⟩
                  · exact (hdv h2).elim
                  · exfalso; apply hne; simp [h1, h2]
                rcases hopp with ⟨hw_neg, hv_pos⟩ | ⟨hw_pos, hv_neg⟩
                · let v0 := (dot r v) • w + (-dot r w) • v
                  have hv0V : v0 ∈ V := V.add_mem (V.smul_mem _ hwV) (V.smul_mem _ hv)
                  have hv0_dot : dot r v0 = 0 := by
                    simp only [v0, dot_add_right, dot_smul_right]; ring
                  refine ⟨v0, ⟨⟨v0, hv0V⟩, hv0_dot, rfl⟩, ?_⟩
                  ext x
                  by_cases hx : x ∈ R
                  · simp only [signMap, if_pos hx, v0, dot_add_right, dot_smul_right]
                    have hsame : signOf (dot x w) = signOf (dot x v) := by
                      have := congrFun hwg x
                      simpa [signMap, g, hx] using this
                    rw [signOf_pos_comb hv_pos (by linarith) hsame]
                    have := congrFun hwg x
                    simpa [signMap, g, hx] using this
                  · simp [signMap, g, hx]
                · let v0 := (-dot r v) • w + (dot r w) • v
                  have hv0V : v0 ∈ V := V.add_mem (V.smul_mem _ hwV) (V.smul_mem _ hv)
                  have hv0_dot : dot r v0 = 0 := by
                    simp only [v0, dot_add_right, dot_smul_right]; ring
                  refine ⟨v0, ⟨⟨v0, hv0V⟩, hv0_dot, rfl⟩, ?_⟩
                  ext x
                  by_cases hx : x ∈ R
                  · simp only [signMap, if_pos hx, v0, dot_add_right, dot_smul_right]
                    have hsame : signOf (dot x w) = signOf (dot x v) := by
                      have := congrFun hwg x
                      simpa [signMap, g, hx] using this
                    rw [signOf_pos_comb (by linarith) hw_pos hsame]
                    have := congrFun hwg x
                    simpa [signMap, g, hx] using this
                  · simp [signMap, g, hx]
          obtain ⟨v0, hv0K, hv0g⟩ := hv0_ex
          exact hg0 (Finset.mem_inter.mpr ⟨hv0g ▸ hS0_mem v0 hv0K, hg1⟩)
      · have hS0'_sub : S0' ⊆ S1 := Finset.inter_subset_right
        have hS0'_le : S0'.card ≤ S0.card := Finset.card_le_card Finset.inter_subset_left
        have hcard_sdiff : (S1 \ S0').card + S0'.card = S1.card := Finset.card_sdiff_add_card_eq_card hS0'_sub
        have hcard_Sall : S_all.card ≤ S1.card + 2 * S0.card := by
          have ha : ((S1 \ S0').image (fun g => Function.update g r (pickVal g))).card ≤ (S1 \ S0').card :=
            Finset.card_image_le
          have hb1 : (S0'.image (fun g => Function.update g r 1)).card ≤ S0'.card := Finset.card_image_le
          have hb2 : (S0'.image (fun g => Function.update g r (-1))).card ≤ S0'.card := Finset.card_image_le
          have hb3 : (S0'.image (fun g => Function.update g r 0)).card ≤ S0'.card := Finset.card_image_le
          have hu1 := Finset.card_union_le
            ((S1 \ S0').image (fun g => Function.update g r (pickVal g)))
            (((S0'.image (fun g => Function.update g r 1)) ∪ (S0'.image (fun g => Function.update g r (-1)))) ∪
              (S0'.image (fun g => Function.update g r 0)))
          have hu2 := Finset.card_union_le
            ((S0'.image (fun g => Function.update g r 1)) ∪ (S0'.image (fun g => Function.update g r (-1))))
            (S0'.image (fun g => Function.update g r 0))
          have hu3 := Finset.card_union_le
            (S0'.image (fun g => Function.update g r 1))
            (S0'.image (fun g => Function.update g r (-1)))
          dsimp [S_all]
          omega
        rw [Finset.card_insert_of_notMem hr]
        have hpascal :
            (∑ j ∈ Finset.range (Module.finrank ℝ V + 1), 2 ^ j * R.card.choose j) +
              2 * (∑ j ∈ Finset.range (Module.finrank ℝ K + 1), 2 ^ j * R.card.choose j) =
            ∑ j ∈ Finset.range (Module.finrank ℝ V + 1), 2 ^ j * (R.card + 1).choose j := by
          set d := Module.finrank ℝ K
          have hd : Module.finrank ℝ V = d + 1 := hK_rank.symm
          rw [hd]
          rw [Finset.sum_range_succ' _ (d + 1), Finset.sum_range_succ' _ (d + 1)]
          rw [Finset.mul_sum]
          have hsum_add :
              (∑ k ∈ Finset.range (d + 1), 2 ^ (k + 1) * R.card.choose (k + 1)) +
              (∑ k ∈ Finset.range (d + 1), 2 * (2 ^ k * R.card.choose k)) =
              ∑ k ∈ Finset.range (d + 1), 2 ^ (k + 1) * (R.card + 1).choose (k + 1) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Nat.choose_succ_succ, pow_succ']
            ring
          simp only [pow_zero, Nat.choose_zero_right, mul_one]
          omega
        omega

/- ### Module 4: Seidel's Upper Bound Theorem & Minkowski Sum Vertex Bound -/

/-- For a subspace `U ≠ ⊤` in `Fin D → ℝ`, there exists a nonzero vector orthogonal to `U`. -/
private lemma exists_orth_ne_zero {D : ℕ} {U : Submodule ℝ (Fin D → ℝ)} (hU : U ≠ ⊤) :
    ∃ h : Fin D → ℝ, h ≠ 0 ∧ ∀ u ∈ U, dot u h = 0 := by
  classical
  have hlt : Module.finrank ℝ U < D := by
    have hle : Module.finrank ℝ U ≤ D := by
      simpa using Submodule.finrank_le U
    have hne : Module.finrank ℝ U ≠ D := by
      intro heq
      apply hU
      exact Submodule.eq_top_of_finrank_eq (by simpa using heq)
    omega
  let B := Module.finBasis ℝ U
  let L : (Fin D → ℝ) →ₗ[ℝ] (Fin (Module.finrank ℝ U) → ℝ) :=
    { toFun := fun h j => dot (B j).1 h
      map_add' := fun h1 h2 => by ext j; exact dot_add_right _ h1 h2
      map_smul' := fun c h => by ext j; simp [dot_smul_right] }
  have hker_ne : LinearMap.ker L ≠ ⊥ := by
    intro hbot
    have hrk := LinearMap.finrank_range_add_finrank_ker L
    rw [hbot, finrank_bot, add_zero] at hrk
    have hle : Module.finrank ℝ (LinearMap.range L) ≤ Module.finrank ℝ U := by
      simpa using Submodule.finrank_le (LinearMap.range L)
    simp only [Module.finrank_pi, Fintype.card_fin] at hrk
    omega
  obtain ⟨h, hh_ker, hh_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  refine ⟨h, hh_ne, fun u hu => ?_⟩
  have hrep : (⟨u, hu⟩ : U) = ∑ j, B.repr ⟨u, hu⟩ j • B j := (B.sum_repr ⟨u, hu⟩).symm
  have hu_eq : u = ∑ j, B.repr ⟨u, hu⟩ j • (B j).1 := by
    calc u = (⟨u, hu⟩ : U).1 := rfl
      _ = (∑ j, B.repr ⟨u, hu⟩ j • B j).1 := congrArg Subtype.val hrep
      _ = ∑ j, B.repr ⟨u, hu⟩ j • (B j).1 := by rw [AddSubmonoidClass.coe_finsetSum]; rfl
  rw [hu_eq, dot_sum_left]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [dot_smul_left]
  have hj : dot (B j).1 h = 0 := congrFun hh_ker j
  rw [hj, mul_zero]

/-- Negative dual basis for a `D`-element linearly independent subset of `A : Fin N → Fin D → ℝ`. -/
private lemma exists_neg_dual_basis {D N : ℕ} (A : Fin N → Fin D → ℝ) (S : Finset (Fin N))
    (hcard : S.card = D) (hli : LinearIndependent ℝ (fun a : S => A a.1)) :
    ∃ d : S → (Fin D → ℝ),
      (∀ a b : S, dot (A b.1) (d a) = if b = a then -1 else 0) ∧
      (∀ a : S, d a ≠ 0) := by
  classical
  rcases Nat.eq_zero_or_pos D with rfl | hD_pos
  · have hSe : S = ∅ := Finset.card_eq_zero.mp hcard
    refine ⟨fun a => 0, fun a => (Finset.notMem_empty a.1 (hSe ▸ a.2)).elim,
      fun a => (Finset.notMem_empty a.1 (hSe ▸ a.2)).elim⟩
  have : Nonempty S := Finset.Nonempty.coe_sort (Finset.card_pos.mp (by omega))
  have hfr : Fintype.card S = Module.finrank ℝ (Fin D → ℝ) := by simp [hcard]
  let B : Module.Basis S ℝ (Fin D → ℝ) := basisOfLinearIndependentOfCardEqFinrank hli hfr
  have hB : ∀ b : S, B b = A b.1 := fun b => by simp [B]
  have hex : ∀ a : S, ∃ v : Fin D → ℝ, ∀ b : S, dot (A b.1) v = if b = a then -1 else 0 := by
    intro a
    let f : (Fin D → ℝ) →ₗ[ℝ] ℝ := B.constr ℝ (fun b => if b = a then (-1 : ℝ) else 0)
    obtain ⟨v, hv⟩ := dot_linear_rep f
    refine ⟨v, fun b => ?_⟩
    rw [dot_comm, ← hv (A b.1), ← hB b]
    by_cases hba : b = a <;> simp [f, hba]
  choose d hd using hex
  refine ⟨d, hd, fun a h0 => ?_⟩
  have := hd a a
  rw [h0, dot_zero_right] at this
  simp at this

/-- Expansion of any vector in the negative dual basis of a `D`-element basis `S`. -/
private lemma neg_dual_basis_expand {D N : ℕ} (A : Fin N → Fin D → ℝ) (S : Finset (Fin N))
    (hcard : S.card = D) (hli : LinearIndependent ℝ (fun a : S => A a.1))
    (d : S → (Fin D → ℝ)) (hd : ∀ a b : S, dot (A b.1) (d a) = if b = a then -1 else 0)
    (v : Fin D → ℝ) :
    v = ∑ a : S, (-dot (A a.1) v) • d a := by
  classical
  rcases Nat.eq_zero_or_pos D with rfl | hD_pos
  · ext k; exact Fin.elim0 k
  have : Nonempty S := Finset.Nonempty.coe_sort (Finset.card_pos.mp (by omega))
  have hfr : Fintype.card S = Module.finrank ℝ (Fin D → ℝ) := by simp [hcard]
  let B : Module.Basis S ℝ (Fin D → ℝ) := basisOfLinearIndependentOfCardEqFinrank hli hfr
  set diff := v - ∑ a : S, (-dot (A a.1) v) • d a
  have hdot_basis : ∀ b : S, dot (A b.1) diff = 0 := by
    intro b
    simp only [diff, dot_sub_right, dot_sum_right, dot_smul_right, hd]
    have hsum : ∑ a : S, (-dot (A a.1) v) * (if b = a then -1 else 0) = dot (A b.1) v := by
      rw [Finset.sum_eq_single b]
      · simp
      · intro a _ hab; simp [hab.symm]
      · intro h; exact (h (Finset.mem_univ b)).elim
    linarith
  have hdot_all : ∀ w : Fin D → ℝ, dot w diff = 0 := by
    intro w
    rw [← B.sum_repr w, dot_sum_left]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [dot_smul_left, show B b = A b.1 by simp [B], hdot_basis b, mul_zero]
  have h0 : diff = 0 := dot_self_eq_zero (hdot_all diff)
  exact sub_eq_zero.mp h0

/-- For a bounded simple polytope `P` in `ℝ^D` with `N` facets:
(1) every nonempty face `F(E)` contains a basis vertex `w` with `E ⊆ tight w`, and
(2) the number of tight-constraint sets of basis vertices is at most
`2 * ∑ j ∈ Finset.range (D / 2 + 1), N.choose j`. -/
private lemma simple_polytope_faces_bound {D N : ℕ} (A : Fin N → Fin D → ℝ) (b : Fin N → ℝ)
    (hbdd : ∃ R : ℝ, ∀ x : Fin D → ℝ, (∀ a, dot (A a) x ≤ b a) → ∀ k, |x k| ≤ R)
    (hsimple : ∀ x : Fin D → ℝ, (∀ a, dot (A a) x ≤ b a) →
      (Finset.univ.filter (fun a => dot (A a) x = b a)).card ≤ D) :
    ∃ VertSets : Finset (Finset (Fin N)),
      VertSets.card ≤ 2 * ∑ j ∈ Finset.range (D / 2 + 1), N.choose j ∧
      (∀ S ∈ VertSets, S.card = D) ∧
      (∀ E : Finset (Fin N),
        (∃ x : Fin D → ℝ, (∀ a, dot (A a) x ≤ b a) ∧ (∀ a ∈ E, dot (A a) x = b a)) →
        ∃ S ∈ VertSets, E ⊆ S) := by
  classical
  let Poly : Set (Fin D → ℝ) := { x | ∀ a : Fin N, dot (A a) x ≤ b a }
  let tight : (Fin D → ℝ) → Finset (Fin N) := fun x =>
    Finset.univ.filter (fun a => dot (A a) x = b a)
  let IsBasisVert : (Fin D → ℝ) → Prop := fun x =>
    x ∈ Poly ∧ (tight x).card = D ∧ LinearIndependent ℝ (fun a : tight x => A a.1)
  -- Collect all D-element linearly independent subsets of Fin N and pick one negative dual basis per S
  let Bases : Finset (Finset (Fin N)) :=
    Finset.univ.filter (fun S : Finset (Fin N) => S.card = D ∧ LinearIndependent ℝ (fun a : S => A a.1))
  have hex_dual : ∀ S : Finset (Fin N), S ∈ Bases →
      ∃ d : S → (Fin D → ℝ),
        (∀ a b : S, dot (A b.1) (d a) = if b = a then -1 else 0) ∧ (∀ a : S, d a ≠ 0) := by
    intro S hS
    simp only [Bases, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact exists_neg_dual_basis A S hS.1 hS.2
  let dualOf : ∀ S : Finset (Fin N), S ∈ Bases → (S → (Fin D → ℝ)) := fun S hS => (hex_dual S hS).choose
  have hdual_spec : ∀ (S : Finset (Fin N)) (hS : S ∈ Bases) (a b : S),
      dot (A b.1) (dualOf S hS a) = if b = a then -1 else 0 :=
    fun S hS => (hex_dual S hS).choose_spec.1
  have hdual_ne : ∀ (S : Finset (Fin N)) (hS : S ∈ Bases) (a : S), dualOf S hS a ≠ 0 :=
    fun S hS => (hex_dual S hS).choose_spec.2
  -- Build finite set of all dual basis vectors across all S ∈ Bases
  let W : Finset (Fin D → ℝ) :=
    Bases.attach.biUnion fun S => Finset.univ.image (fun a : S.1 => dualOf S.1 S.2 a)
  have hW_ne : ∀ w ∈ W, w ≠ 0 := by
    intro w hw
    rcases Finset.mem_biUnion.mp hw with ⟨⟨S, hS⟩, _, hwS⟩
    rcases Finset.mem_image.mp hwS with ⟨a, _, rfl⟩
    exact hdual_ne S hS a
  obtain ⟨φ, hφ⟩ := exists_generic_functional W hW_ne
  -- Part 1: VertSets = tight sets of basis vertices
  let VertSets : Finset (Finset (Fin N)) :=
    Finset.univ.filter (fun S : Finset (Fin N) => ∃ x, IsBasisVert x ∧ tight x = S)
  refine ⟨VertSets, ?_, ?_, ?_⟩
  · -- Seidel's 8-line bound on VertSets.card!
    have hV_sub_Bases : ∀ S ∈ VertSets, S ∈ Bases := by
      intro S hS
      simp only [VertSets, Finset.mem_filter, Finset.mem_univ, true_and] at hS
      obtain ⟨x, ⟨_, hcard, hli⟩, rfl⟩ := hS
      simp only [Bases, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hcard, hli⟩
    -- For each S ∈ VertSets, pick its unique basis vertex x(S), and split S into S⁺ and S⁻
    have hpick_x : ∀ S ∈ VertSets, ∃ x, IsBasisVert x ∧ tight x = S := by
      intro S hS
      simpa [VertSets] using hS
    let xOf : ∀ S ∈ VertSets, (Fin D → ℝ) := fun S hS => (hpick_x S hS).choose
    have hxOf_bv : ∀ S (hS : S ∈ VertSets), IsBasisVert (xOf S hS) := fun S hS => (hpick_x S hS).choose_spec.1
    have hxOf_tight : ∀ S (hS : S ∈ VertSets), tight (xOf S hS) = S := fun S hS => (hpick_x S hS).choose_spec.2
    let Splus : ∀ S ∈ VertSets, Finset (Fin N) := fun S hS =>
      S.attach.filter (fun a => 0 < dot φ (dualOf S (hV_sub_Bases S hS) a)) |>.image Subtype.val
    let Sminus : ∀ S ∈ VertSets, Finset (Fin N) := fun S hS =>
      S.attach.filter (fun a => dot φ (dualOf S (hV_sub_Bases S hS) a) < 0) |>.image Subtype.val
    have hsplit_card : ∀ S (hS : S ∈ VertSets), (Splus S hS).card + (Sminus S hS).card = D := by
      intro S hS
      have hB : S ∈ Bases := hV_sub_Bases S hS
      have hcard_S : S.card = D := (Finset.mem_filter.mp hB).2.1
      have hinj : Function.Injective (Subtype.val : S → Fin N) := Subtype.val_injective
      rw [Finset.card_image_of_injective _ hinj, Finset.card_image_of_injective _ hinj]
      have hfilt_eq : S.attach.filter (fun a => dot φ (dualOf S hB a) < 0) =
          S.attach.filter (fun a => ¬ 0 < dot φ (dualOf S hB a)) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_attach, true_and]
        have hne : dot φ (dualOf S hB a) ≠ 0 := by
          apply hφ
          rw [Finset.mem_biUnion]
          exact ⟨⟨S, hB⟩, Finset.mem_attach _ _, Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩
        constructor
        · intro h; linarith
        · intro h; exact lt_of_le_of_ne (not_lt.mp h) hne
      rw [hfilt_eq, card_filter_add_not, Finset.card_attach, hcard_S]
    -- Key optimality lemmas for Splus and Sminus:
    have hmax_on_Splus : ∀ S (hS : S ∈ VertSets) (z : Fin D → ℝ),
        z ∈ Poly → (∀ a ∈ Splus S hS, dot (A a) z = b a) → z ≠ xOf S hS →
        dot φ z < dot φ (xOf S hS) := by
      intro S hS z hzP hzT hne
      have hB : S ∈ Bases := hV_sub_Bases S hS
      have hS_card : S.card = D := (Finset.mem_filter.mp hB).2.1
      have hS_li : LinearIndependent ℝ (fun a : S => A a.1) := (Finset.mem_filter.mp hB).2.2
      have hxt : tight (xOf S hS) = S := hxOf_tight S hS
      have hexp := neg_dual_basis_expand A S hS_card hS_li (dualOf S hB) (hdual_spec S hB) (z - xOf S hS)
      have hdot_diff : dot φ z - dot φ (xOf S hS) =
          ∑ a : S, (-dot (A a.1) (z - xOf S hS)) * dot φ (dualOf S hB a) := by
        conv_lhs => rw [← dot_sub_right, hexp, dot_sum_right]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [dot_smul_right]
      have ha_tight_fn : ∀ a : S, dot (A a.1) (xOf S hS) = b a.1 := fun a => by
        have ht : a.1 ∈ tight (xOf S hS) := by rw [hxt]; exact a.2
        exact (Finset.mem_filter.mp ht).2
      have hcoeff_nn : ∀ a : S, 0 ≤ -dot (A a.1) (z - xOf S hS) := by
        intro a
        have ha_le : dot (A a.1) z ≤ b a.1 := hzP a.1
        rw [dot_sub_right, ha_tight_fn a]; linarith
      have hterm_le : ∀ a : S, (-dot (A a.1) (z - xOf S hS)) * dot φ (dualOf S hB a) ≤ 0 := by
        intro a
        by_cases hpos : 0 < dot φ (dualOf S hB a)
        · have ha_sp : a.1 ∈ Splus S hS := by
            rw [Finset.mem_image]
            exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hpos⟩, rfl⟩
          have ha_z : dot (A a.1) z = b a.1 := hzT a.1 ha_sp
          rw [dot_sub_right, ha_z, ha_tight_fn a, sub_self, neg_zero, zero_mul]
        · exact mul_nonpos_of_nonneg_of_nonpos (hcoeff_nn a) (not_lt.mp hpos)
      have hex_neg : ∃ a : S, (-dot (A a.1) (z - xOf S hS)) * dot φ (dualOf S hB a) < 0 := by
        have hex_pos_c : ∃ a : S, 0 < -dot (A a.1) (z - xOf S hS) := by
          by_contra hall
          push Not at hall
          have hall0 : ∀ a : S, -dot (A a.1) (z - xOf S hS) = 0 :=
            fun a => le_antisymm (hall a) (hcoeff_nn a)
          have hz0 : z - xOf S hS = 0 := by
            rw [hexp]; exact Finset.sum_eq_zero fun a _ => by rw [hall0 a, zero_smul]
          exact hne (sub_eq_zero.mp hz0)
        obtain ⟨a, ha_pos⟩ := hex_pos_c
        have hnot_sp : ¬ 0 < dot φ (dualOf S hB a) := by
          intro hpos
          have ha_sp : a.1 ∈ Splus S hS :=
            Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hpos⟩, rfl⟩
          have ha_z : dot (A a.1) z = b a.1 := hzT a.1 ha_sp
          rw [dot_sub_right, ha_z, ha_tight_fn a, sub_self, neg_zero] at ha_pos
          exact lt_irrefl 0 ha_pos
        have hne_phi : dot φ (dualOf S hB a) ≠ 0 :=
          hφ _ (Finset.mem_biUnion.mpr ⟨⟨S, hB⟩, Finset.mem_attach _ _,
            Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩)
        have hneg_phi : dot φ (dualOf S hB a) < 0 := lt_of_le_of_ne (not_lt.mp hnot_sp) hne_phi
        exact ⟨a, mul_neg_of_pos_of_neg ha_pos hneg_phi⟩
      have hsum_neg : ∑ a : S, (-dot (A a.1) (z - xOf S hS)) * dot φ (dualOf S hB a) < 0 := by
        obtain ⟨a0, ha0⟩ := hex_neg
        exact sum_neg_of_nonpos (fun a _ => hterm_le a) ⟨a0, Finset.mem_univ a0, ha0⟩
      linarith
    have hmin_on_Sminus : ∀ S (hS : S ∈ VertSets) (z : Fin D → ℝ),
        z ∈ Poly → (∀ a ∈ Sminus S hS, dot (A a) z = b a) → z ≠ xOf S hS →
        dot φ (xOf S hS) < dot φ z := by
      intro S hS z hzP hzT hne
      have hB : S ∈ Bases := hV_sub_Bases S hS
      have hS_card : S.card = D := (Finset.mem_filter.mp hB).2.1
      have hS_li : LinearIndependent ℝ (fun a : S => A a.1) := (Finset.mem_filter.mp hB).2.2
      have hxt : tight (xOf S hS) = S := hxOf_tight S hS
      have hexp := neg_dual_basis_expand A S hS_card hS_li (dualOf S hB) (hdual_spec S hB) (z - xOf S hS)
      have hdot_diff : dot φ z - dot φ (xOf S hS) =
          ∑ a : S, (-dot (A a.1) (z - xOf S hS)) * dot φ (dualOf S hB a) := by
        conv_lhs => rw [← dot_sub_right, hexp, dot_sum_right]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [dot_smul_right]
      have ha_tight_fn : ∀ a : S, dot (A a.1) (xOf S hS) = b a.1 := fun a => by
        have ht : a.1 ∈ tight (xOf S hS) := by rw [hxt]; exact a.2
        exact (Finset.mem_filter.mp ht).2
      have hcoeff_nn : ∀ a : S, 0 ≤ -dot (A a.1) (z - xOf S hS) := by
        intro a
        have ha_le : dot (A a.1) z ≤ b a.1 := hzP a.1
        rw [dot_sub_right, ha_tight_fn a]; linarith
      have hterm_ge : ∀ a : S, 0 ≤ (-dot (A a.1) (z - xOf S hS)) * dot φ (dualOf S hB a) := by
        intro a
        by_cases hneg : dot φ (dualOf S hB a) < 0
        · have ha_sm : a.1 ∈ Sminus S hS :=
            Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hneg⟩, rfl⟩
          have ha_z : dot (A a.1) z = b a.1 := hzT a.1 ha_sm
          rw [dot_sub_right, ha_z, ha_tight_fn a, sub_self, neg_zero, zero_mul]
        · exact mul_nonneg (hcoeff_nn a) (not_lt.mp hneg)
      have hex_pos : ∃ a : S, 0 < (-dot (A a.1) (z - xOf S hS)) * dot φ (dualOf S hB a) := by
        have hex_pos_c : ∃ a : S, 0 < -dot (A a.1) (z - xOf S hS) := by
          by_contra hall
          push Not at hall
          have hall0 : ∀ a : S, -dot (A a.1) (z - xOf S hS) = 0 :=
            fun a => le_antisymm (hall a) (hcoeff_nn a)
          have hz0 : z - xOf S hS = 0 := by
            rw [hexp]; exact Finset.sum_eq_zero fun a _ => by rw [hall0 a, zero_smul]
          exact hne (sub_eq_zero.mp hz0)
        obtain ⟨a, ha_pos⟩ := hex_pos_c
        have hnot_sm : ¬ dot φ (dualOf S hB a) < 0 := by
          intro hneg
          have ha_sm : a.1 ∈ Sminus S hS :=
            Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hneg⟩, rfl⟩
          have ha_z : dot (A a.1) z = b a.1 := hzT a.1 ha_sm
          rw [dot_sub_right, ha_z, ha_tight_fn a, sub_self, neg_zero] at ha_pos
          exact lt_irrefl 0 ha_pos
        have hne_phi : dot φ (dualOf S hB a) ≠ 0 :=
          hφ _ (Finset.mem_biUnion.mpr ⟨⟨S, hB⟩, Finset.mem_attach _ _,
            Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩)
        have hpos_phi : 0 < dot φ (dualOf S hB a) := lt_of_le_of_ne (not_lt.mp hnot_sm) hne_phi.symm
        exact ⟨a, mul_pos ha_pos hpos_phi⟩
      have hsum_pos : 0 < ∑ a : S, (-dot (A a.1) (z - xOf S hS)) * dot φ (dualOf S hB a) := by
        obtain ⟨a0, ha0⟩ := hex_pos
        exact Finset.sum_pos' (fun a _ => hterm_ge a) ⟨a0, Finset.mem_univ a0, ha0⟩
      linarith
    -- Split VertSets.attach into V1 (|Splus| ≤ D/2) and V2 (|Sminus| ≤ D/2)
    let V1 := VertSets.attach.filter fun S => (Splus S.1 S.2).card ≤ D / 2
    let V2 := VertSets.attach.filter fun S => (Sminus S.1 S.2).card ≤ D / 2
    let Small := (Finset.univ : Finset (Finset (Fin N))).filter fun T => T.card ≤ D / 2
    have hcov : VertSets.attach ⊆ V1 ∪ V2 := by
      intro S _
      have hsum := hsplit_card S.1 S.2
      rw [Finset.mem_union]
      by_cases h1 : (Splus S.1 S.2).card ≤ D / 2
      · left; exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, h1⟩
      · right; exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, by omega⟩
    have hV1_le : V1.card ≤ Small.card := by
      refine Finset.card_le_card_of_injOn (fun S => Splus S.1 S.2) ?_ ?_
      · intro S hS
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hS).2⟩
      · intro S1 _ S2 _ heq
        dsimp only at heq
        ext : 1
        have h1_eq_2 : xOf S1.1 S1.2 = xOf S2.1 S2.2 := by
          by_contra hne
          have hsub1 : ∀ a ∈ Splus S1.1 S1.2, dot (A a) (xOf S2.1 S2.2) = b a := by
            intro a ha
            rw [heq] at ha
            have haS2 : a ∈ S2.1 := by
              rcases Finset.mem_image.mp ha with ⟨b, _, rfl⟩; exact b.2
            rw [← hxOf_tight S2.1 S2.2] at haS2
            exact (Finset.mem_filter.mp haS2).2
          have hsub2 : ∀ a ∈ Splus S2.1 S2.2, dot (A a) (xOf S1.1 S1.2) = b a := by
            intro a ha
            rw [← heq] at ha
            have haS1 : a ∈ S1.1 := by
              rcases Finset.mem_image.mp ha with ⟨b, _, rfl⟩; exact b.2
            rw [← hxOf_tight S1.1 S1.2] at haS1
            exact (Finset.mem_filter.mp haS1).2
          have hlt1 := hmax_on_Splus S1.1 S1.2 (xOf S2.1 S2.2) (hxOf_bv S2.1 S2.2).1 hsub1 (Ne.symm hne)
          have hlt2 := hmax_on_Splus S2.1 S2.2 (xOf S1.1 S1.2) (hxOf_bv S1.1 S1.2).1 hsub2 hne
          linarith
        rw [← hxOf_tight S1.1 S1.2, ← hxOf_tight S2.1 S2.2, h1_eq_2]
    have hV2_le : V2.card ≤ Small.card := by
      refine Finset.card_le_card_of_injOn (fun S => Sminus S.1 S.2) ?_ ?_
      · intro S hS
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hS).2⟩
      · intro S1 _ S2 _ heq
        dsimp only at heq
        ext : 1
        have h1_eq_2 : xOf S1.1 S1.2 = xOf S2.1 S2.2 := by
          by_contra hne
          have hsub1 : ∀ a ∈ Sminus S1.1 S1.2, dot (A a) (xOf S2.1 S2.2) = b a := by
            intro a ha
            rw [heq] at ha
            have haS2 : a ∈ S2.1 := by
              rcases Finset.mem_image.mp ha with ⟨b, _, rfl⟩; exact b.2
            rw [← hxOf_tight S2.1 S2.2] at haS2
            exact (Finset.mem_filter.mp haS2).2
          have hsub2 : ∀ a ∈ Sminus S2.1 S2.2, dot (A a) (xOf S1.1 S1.2) = b a := by
            intro a ha
            rw [← heq] at ha
            have haS1 : a ∈ S1.1 := by
              rcases Finset.mem_image.mp ha with ⟨b, _, rfl⟩; exact b.2
            rw [← hxOf_tight S1.1 S1.2] at haS1
            exact (Finset.mem_filter.mp haS1).2
          have hlt1 := hmin_on_Sminus S1.1 S1.2 (xOf S2.1 S2.2) (hxOf_bv S2.1 S2.2).1 hsub1 (Ne.symm hne)
          have hlt2 := hmin_on_Sminus S2.1 S2.2 (xOf S1.1 S1.2) (hxOf_bv S1.1 S1.2).1 hsub2 hne
          linarith
        rw [← hxOf_tight S1.1 S1.2, ← hxOf_tight S2.1 S2.2, h1_eq_2]
    have hSmall_card : Small.card ≤ ∑ j ∈ Finset.range (D / 2 + 1), N.choose j := by
      have hsub : Small ⊆ (Finset.range (D / 2 + 1)).biUnion
          (fun j => Finset.powersetCard j (Finset.univ : Finset (Fin N))) := by
        intro T hT
        rw [Finset.mem_biUnion]
        refine ⟨T.card, Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hT).2), ?_⟩
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩
      calc Small.card
          ≤ ((Finset.range (D / 2 + 1)).biUnion
              (fun j => Finset.powersetCard j (Finset.univ : Finset (Fin N)))).card :=
            Finset.card_le_card hsub
        _ ≤ ∑ j ∈ Finset.range (D / 2 + 1),
              (Finset.powersetCard j (Finset.univ : Finset (Fin N))).card :=
            Finset.card_biUnion_le
        _ = ∑ j ∈ Finset.range (D / 2 + 1), N.choose j := by
            refine Finset.sum_congr rfl fun j _ => by simp
    calc VertSets.card = VertSets.attach.card := (Finset.card_attach).symm
      _ ≤ (V1 ∪ V2).card := Finset.card_le_card hcov
      _ ≤ V1.card + V2.card := Finset.card_union_le _ _
      _ ≤ Small.card + Small.card := add_le_add hV1_le hV2_le
      _ = 2 * Small.card := by ring
      _ ≤ 2 * ∑ j ∈ Finset.range (D / 2 + 1), N.choose j := Nat.mul_le_mul_left 2 hSmall_card
  · -- Part 2: Every S ∈ VertSets has card D
    intro S hS
    simp only [VertSets, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    obtain ⟨x, ⟨_, hcard, _⟩, rfl⟩ := hS
    exact hcard
  · -- Part 3: Every nonempty face F(E) contains a basis vertex w with E ⊆ tight w
    intro E ⟨x0, hx0P, hx0E⟩
    let F : Set (Fin D → ℝ) := { x | x ∈ Poly ∧ ∀ a ∈ E, dot (A a) x = b a }
    have hF_nonempty : F.Nonempty := ⟨x0, hx0P, hx0E⟩
    obtain ⟨R, hR⟩ := hbdd
    have hF_closed : IsClosed F := by
      have h1 : IsClosed Poly := by
        have : Poly = ⋂ a : Fin N, { x | dot (A a) x ≤ b a } := by ext x; simp [Poly]
        rw [this]
        exact isClosed_iInter fun a => isClosed_le (dot_continuous (A a)) continuous_const
      have h2 : IsClosed { x : Fin D → ℝ | ∀ a ∈ E, dot (A a) x = b a } := by
        have : { x : Fin D → ℝ | ∀ a ∈ E, dot (A a) x = b a } =
            ⋂ a ∈ E, { x | dot (A a) x = b a } := by ext x; simp
        rw [this]
        exact isClosed_biInter fun a _ => isClosed_eq (dot_continuous (A a)) continuous_const
      exact h1.inter h2
    have hF_sub_box : F ⊆ Set.pi Set.univ (fun _ : Fin D => Set.Icc (-R) R) := by
      intro x hx k _
      exact abs_le.mp (hR x hx.1 k)
    have hF_compact : IsCompact F :=
      (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hF_closed hF_sub_box
    obtain ⟨xmax, hxmax_F, hxmax_max⟩ :=
      hF_compact.exists_isMaxOn hF_nonempty (dot_continuous φ).continuousOn
    set M := dot φ xmax
    let MaxSet : Set (Fin D → ℝ) := { x | x ∈ F ∧ dot φ x = M }
    let Cards : Finset ℕ := (Finset.range (N + 1)).filter fun c => ∃ x ∈ MaxSet, (tight x).card = c
    have hCards_ne : Cards.Nonempty := by
      refine ⟨(tight xmax).card, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, xmax, ⟨hxmax_F, rfl⟩, rfl⟩⟩
      have : (tight xmax).card ≤ N := by
        calc (tight xmax).card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_card (Finset.subset_univ _)
          _ = N := by simp
      omega
    obtain ⟨cmax, hcmax_mem, hcmax_ge⟩ := Cards.exists_max_image id hCards_ne
    obtain ⟨w, ⟨hwF, hwM⟩, hw_card⟩ := (Finset.mem_filter.mp hcmax_mem).2
    -- Prove span { A a | a ∈ tight w } = ⊤!
    have hspan_top : Submodule.span ℝ (Set.range (fun a : tight w => A a.1)) = ⊤ := by
      by_contra hne_top
      obtain ⟨h0, hh0_ne, hh0_orth⟩ := exists_orth_ne_zero hne_top
      let h : Fin D → ℝ := if 0 ≤ dot φ h0 then h0 else -h0
      have hh_ne : h ≠ 0 := by
        dsimp [h]; split_ifs
        · exact hh0_ne
        · exact neg_ne_zero.mpr hh0_ne
      have hh_phi : 0 ≤ dot φ h := by
        dsimp [h]; split_ifs with hpos
        · exact hpos
        · rw [dot_neg_right]; linarith
      have hh_orth : ∀ a ∈ tight w, dot (A a) h = 0 := by
        intro a ha
        have h0a : dot (A a) h0 = 0 := hh0_orth (A a) (Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩)
        dsimp [h]; split_ifs
        · exact h0a
        · rw [dot_neg_right, h0a, neg_zero]
      -- Some a must have dot (A a) h > 0, else w + t • h ∈ Poly for all t ≥ 0, contradicting hbdd!
      let Pos : Finset (Fin N) := Finset.univ.filter fun a => 0 < dot (A a) h
      have hPos_ne : Pos.Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        have hall_le : ∀ a : Fin N, dot (A a) h ≤ 0 := by
          intro a
          by_contra hgt
          push Not at hgt
          have : a ∈ Pos := Finset.mem_filter.mpr ⟨Finset.mem_univ a, hgt⟩
          rw [hempty] at this
          exact Finset.notMem_empty a this
        have hex_k : ∃ k : Fin D, h k ≠ 0 := by
          by_contra hall; push Not at hall; exact hh_ne (funext hall)
        obtain ⟨k0, hk0⟩ := hex_k
        let t : ℝ := (|w k0| + R + 1) / |h k0|
        have ht_pos : 0 ≤ t := by
          have hRnn : 0 ≤ R := le_trans (abs_nonneg (w k0)) (hR w hwF.1 k0)
          exact div_nonneg (by linarith [abs_nonneg (w k0)]) (abs_nonneg _)
        have hwt_mem : w + t • h ∈ Poly := by
          intro a
          rw [dot_add_right, dot_smul_right]
          have : t * dot (A a) h ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht_pos (hall_le a)
          linarith [hwF.1 a]
        have hbd := hR (w + t • h) hwt_mem k0
        have hhk : |h k0| > 0 := abs_pos.mpr hk0
        have h1 : |t * h k0| = |w k0| + R + 1 := by
          rw [abs_mul, abs_of_nonneg ht_pos]
          dsimp [t]
          field_simp [hhk.ne']
        have h2 : |t * h k0| - |w k0| ≤ |w k0 + t * h k0| := by
          have := abs_sub_abs_le_abs_sub (t * h k0) (-w k0)
          rw [abs_neg, sub_neg_eq_add, add_comm] at this
          exact this
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hbd
        linarith
      -- Minimize t(a) = (b a - dot (A a) w) / dot (A a) h over a ∈ Pos
      let step : Fin N → ℝ := fun a => (b a - dot (A a) w) / dot (A a) h
      obtain ⟨aStar, haStar_mem, haStar_min⟩ := Pos.exists_min_image step hPos_ne
      have haStar_pos : 0 < dot (A aStar) h := (Finset.mem_filter.mp haStar_mem).2
      have haStar_not_tight : aStar ∉ tight w := by
        intro ht
        have := hh_orth aStar ht
        linarith
      have hstep_pos : 0 < step aStar := by
        have hlt : dot (A aStar) w < b aStar := by
          have hle := hwF.1 aStar
          have hne : dot (A aStar) w ≠ b aStar := fun heq =>
            haStar_not_tight (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩)
          exact lt_of_le_of_ne hle hne
        exact div_pos (by linarith) haStar_pos
      let w' : Fin D → ℝ := w + step aStar • h
      have hw'_Poly : w' ∈ Poly := by
        intro a
        simp only [w', dot_add_right, dot_smul_right]
        by_cases ha : a ∈ Pos
        · have hap : 0 < dot (A a) h := (Finset.mem_filter.mp ha).2
          have hmin : step aStar ≤ step a := haStar_min a ha
          have hmul := mul_le_mul_of_nonneg_right hmin hap.le
          dsimp [step] at hmul
          rw [div_mul_cancel₀ _ hap.ne'] at hmul
          linarith
        · have hal : dot (A a) h ≤ 0 := by
            by_contra hgt; push Not at hgt
            exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩)
          have hmul : step aStar * dot (A a) h ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hstep_pos.le hal
          linarith [hwF.1 a]
      have htight_sub : tight w ⊆ tight w' := by
        intro a ha
        have ha_eq : dot (A a) w = b a := (Finset.mem_filter.mp ha).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simp only [w', dot_add_right, dot_smul_right, hh_orth a ha, mul_zero, add_zero, ha_eq]
      have haStar_in_w' : aStar ∈ tight w' := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simp only [w', dot_add_right, dot_smul_right, step]
        rw [div_mul_cancel₀ _ haStar_pos.ne']
        ring
      have hw'_F : w' ∈ F := by
        refine ⟨hw'_Poly, fun a haE => ?_⟩
        have ha_tw : a ∈ tight w := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwF.2 a haE⟩
        exact (Finset.mem_filter.mp (htight_sub ha_tw)).2
      have hw'_M : dot φ w' = M := by
        have hle : dot φ w' ≤ M := hxmax_max hw'_F
        have hge : M ≤ dot φ w' := by
          simp only [w', dot_add_right, dot_smul_right, hwM]
          have : 0 ≤ step aStar * dot φ h := mul_nonneg hstep_pos.le hh_phi
          linarith
        linarith
      have hcard_lt : (tight w).card < (tight w').card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨htight_sub, fun heq =>
          haStar_not_tight (heq ▸ haStar_in_w')⟩)
      have hw'_in_Cards : (tight w').card ∈ Cards := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, w', ⟨hw'_F, hw'_M⟩, rfl⟩
        have : (tight w').card ≤ N := by
          calc (tight w').card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_card (Finset.subset_univ _)
            _ = N := by simp
        omega
      have hle_cmax := hcmax_ge (tight w').card hw'_in_Cards
      dsimp at hle_cmax
      omega
    -- Hence (tight w).card = D and { A a | a ∈ tight w } is linearly independent!
    have hcard_ge : D ≤ (tight w).card := by
      have hle : Module.finrank ℝ (Submodule.span ℝ (Set.range (fun a : tight w => A a.1))) ≤
          (Set.range (fun a : tight w => A a.1)).toFinset.card := finrank_span_le_card _
      rw [hspan_top, finrank_top] at hle
      simp only [Module.finrank_pi, Fintype.card_fin] at hle
      calc D ≤ (Set.range (fun a : tight w => A a.1)).toFinset.card := hle
        _ ≤ (Finset.univ : Finset (tight w)).card := by
            rw [Set.toFinset_range]
            exact Finset.card_image_le
        _ = (tight w).card := by simp
    have hcard_eq : (tight w).card = D := le_antisymm (hsimple w hwF.1) hcard_ge
    have hli : LinearIndependent ℝ (fun a : tight w => A a.1) :=
      linearIndependent_of_top_le_span_of_card_eq_finrank (le_of_eq hspan_top.symm) (by simp [hcard_eq])
    refine ⟨tight w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, ⟨hwF.1, hcard_eq, hli⟩, rfl⟩, ?_⟩
    intro a haE
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwF.2 a haE⟩

/-- Predicate for a strict extreme grid tuple of a Minkowski sum `Q 0 + ⋯ + Q (n - 1)` in `ℝ^r`. -/
private def StrictVert {n m r : ℕ} (Q : Fin n → Fin m → (Fin r → ℝ))
    (i : Fin n → Fin m) : Prop :=
  ∃ u : Fin r → ℝ, ∀ k : Fin n, ∀ j : Fin m, j ≠ i k → dot u (Q k j) < dot u (Q k (i k))

open Classical in
/-- Core Minkowski-sum vertex bound in `ℝ^r` for `r ≤ n`:
at most `12 ^ n * m ^ (n - 1)` grid tuples are strict extreme points of `Q 0 + ⋯ + Q (n - 1)`. -/
private lemma minkowski_vertices_le {n m r : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m) (hr : r ≤ n)
    (Q : Fin n → Fin m → (Fin r → ℝ)) :
    (Finset.univ.filter (StrictVert Q)).card ≤ 12 ^ n * m ^ (n - 1) := by
  classical
  have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- Step 1: Center each Q k so ∑ j, Qc k j = 0
  let Qc : Fin n → Fin m → (Fin r → ℝ) := fun k j =>
    Q k j - ((m : ℝ)⁻¹) • ∑ j' : Fin m, Q k j'
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hQc_sum : ∀ k : Fin n, ∑ j : Fin m, Qc k j = 0 := by
    intro k
    ext c
    simp only [Qc, Finset.sum_sub_distrib, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_apply,
      Pi.zero_apply]
    field_simp [hmR]
    ring
  have hSV_eq : ∀ i, StrictVert Q i ↔ StrictVert Qc i := by
    intro i
    constructor <;> (rintro ⟨u, hu⟩; refine ⟨u, fun k j hj => ?_⟩)
    · simp only [Qc, dot_sub_right]; linarith [hu k j hj]
    · have := hu k j hj; simp only [Qc, dot_sub_right] at this; linarith
  -- Step 2: Restrict to W = span { Qc k j } of dimension r' ≤ r ≤ n
  let W : Submodule ℝ (Fin r → ℝ) := Submodule.span ℝ { v | ∃ k j, Qc k j = v }
  set r' := Module.finrank ℝ W
  have hr'_le_r : r' ≤ r := by
    simpa [r'] using Submodule.finrank_le W
  have hr'_le_n : r' ≤ n := le_trans hr'_le_r hr
  -- If r' = 0, then Qc = 0 so no strict vertices exist (since m ≥ 2)!
  rcases Nat.eq_zero_or_pos r' with hr0 | hr'_pos
  · have hW_bot : W = ⊥ := Submodule.finrank_eq_zero.mp hr0
    have hQc_zero : ∀ k j, Qc k j = 0 := by
      intro k j
      have : Qc k j ∈ W := Submodule.subset_span ⟨k, j, rfl⟩
      rwa [hW_bot, Submodule.mem_bot] at this
    have hempty : Finset.univ.filter (StrictVert Q) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rw [hSV_eq]
      rintro ⟨u, hu⟩
      let k0 : Fin n := ⟨0, hn⟩
      have hex_ne : ∃ j : Fin m, j ≠ i k0 := by
        by_cases h0 : i k0 = ⟨0, by omega⟩
        · exact ⟨⟨1, by omega⟩, by rw [h0]; intro h; exact absurd (congrArg Fin.val h) (by norm_num)⟩
        · exact ⟨⟨0, by omega⟩, Ne.symm h0⟩
      obtain ⟨j, hj⟩ := hex_ne
      have := hu k0 j hj
      simp [hQc_zero] at this
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  -- Step 3: Transport Qc into Fin r' → ℝ via a basis of W
  let BW : Module.Basis (Fin r') ℝ W := Module.finBasis ℝ W
  let q : Fin n → Fin m → (Fin r' → ℝ) := fun k j =>
    BW.equivFun ⟨Qc k j, Submodule.subset_span ⟨k, j, rfl⟩⟩
  have hq_sum : ∀ k : Fin n, ∑ j : Fin m, q k j = 0 := by
    intro k
    have h1 : (∑ j : Fin m, (⟨Qc k j, Submodule.subset_span ⟨k, j, rfl⟩⟩ : W)) = 0 := by
      ext c
      have := congrFun (hQc_sum k) c
      simpa using this
    have := congrArg BW.equivFun h1
    simpa [q, map_sum] using this
  have hq_span : Submodule.span ℝ { v : Fin r' → ℝ | ∃ k j, q k j = v } = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hle : Submodule.span ℝ { v : Fin r' → ℝ | ∃ k j, q k j = v } =
        Submodule.map BW.equivFun.toLinearMap (Submodule.span ℝ (Set.range fun p : Fin n × Fin m =>
          (⟨Qc p.1 p.2, Submodule.subset_span ⟨p.1, p.2, rfl⟩⟩ : W))) := by
      rw [Submodule.map_span]
      congr 1
      ext v
      constructor
      · rintro ⟨k, j, rfl⟩
        exact ⟨⟨Qc k j, Submodule.subset_span ⟨k, j, rfl⟩⟩, ⟨(k, j), rfl⟩, rfl⟩
      · rintro ⟨_, ⟨⟨k, j⟩, rfl⟩, rfl⟩
        exact ⟨k, j, rfl⟩
    have hW_top : Submodule.span ℝ (Set.range fun p : Fin n × Fin m =>
        (⟨Qc p.1 p.2, Submodule.subset_span ⟨p.1, p.2, rfl⟩⟩ : W)) = ⊤ := by
      let S_W : Set W := Set.range fun p : Fin n × Fin m =>
        (⟨Qc p.1 p.2, Submodule.subset_span ⟨p.1, p.2, rfl⟩⟩ : W)
      change Submodule.span ℝ S_W = ⊤
      rw [eq_top_iff]
      rintro ⟨x, hx⟩ _
      have hmap := Submodule.map_span W.subtype S_W
      have hsub_eq : W.subtype '' S_W = { v | ∃ k j, Qc k j = v } := by
        ext v
        constructor
        · rintro ⟨_, ⟨⟨k, j⟩, rfl⟩, rfl⟩; exact ⟨k, j, rfl⟩
        · rintro ⟨k, j, rfl⟩; exact ⟨⟨Qc k j, Submodule.subset_span ⟨k, j, rfl⟩⟩, ⟨(k, j), rfl⟩, rfl⟩
      rw [hsub_eq] at hmap
      have hx_mem : x ∈ Submodule.map W.subtype (Submodule.span ℝ S_W) := by
        rw [hmap]; exact hx
      rcases hx_mem with ⟨y, hy, hyx⟩
      have : y = ⟨x, hx⟩ := Subtype.ext hyx
      rwa [← this]
    rw [hle, hW_top, Submodule.map_top, LinearEquiv.range]
    simp
  have hSV_to_q : ∀ i, StrictVert Q i → StrictVert q i := by
    intro i hi
    obtain ⟨u, hu⟩ := (hSV_eq i).mp hi
    let f : (Fin r' → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun v => dot u (BW.equivFun.symm v).1
        map_add' := fun v1 v2 => by simp [map_add, dot_add_right]
        map_smul' := fun c v => by simp [map_smul, dot_smul_right] }
    obtain ⟨u', hu'⟩ := dot_linear_rep f
    refine ⟨u', fun k j hj => ?_⟩
    rw [← hu' (q k j), ← hu' (q k (i k))]
    simp only [f, q, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_apply_apply]
    exact hu k j hj
  -- Step 4: Positive lower bound on f(u) = ∑ k, max_j ⟨u, q k j⟩ on the unit l∞-sphere in ℝ^{r'}
  let sphere : Set (Fin r' → ℝ) := { u | (∀ c, |u c| ≤ 1) ∧ ∃ c, |u c| = 1 }
  have hsphere_compact : IsCompact sphere := by
    have hcl : IsClosed sphere := by
      have h1 : IsClosed { u : Fin r' → ℝ | ∀ c, |u c| ≤ 1 } := by
        have : { u : Fin r' → ℝ | ∀ c, |u c| ≤ 1 } = ⋂ c : Fin r', { u | |u c| ≤ 1 } := by ext u; simp
        rw [this]
        exact isClosed_iInter fun c => isClosed_le (continuous_abs.comp (continuous_apply c)) continuous_const
      have h2 : IsClosed { u : Fin r' → ℝ | ∃ c, |u c| = 1 } := by
        have : { u : Fin r' → ℝ | ∃ c, |u c| = 1 } = ⋃ c : Fin r', { u | |u c| = 1 } := by ext u; simp
        rw [this]
        exact isClosed_iUnion_of_finite fun c => isClosed_eq (continuous_abs.comp (continuous_apply c)) continuous_const
      exact h1.inter h2
    have hsub : sphere ⊆ Set.pi Set.univ (fun _ : Fin r' => Set.Icc (-1 : ℝ) 1) := by
      intro u hu c _
      exact abs_le.mp (hu.1 c)
    exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hcl hsub
  have hsphere_ne : sphere.Nonempty := by
    refine ⟨Pi.single ⟨0, hr'_pos⟩ 1, ?_, ⟨0, hr'_pos⟩, by simp⟩
    intro c
    by_cases hc : c = ⟨0, hr'_pos⟩
    · subst hc; simp
    · simp [hc]
  let suppSum : (Fin r' → ℝ) → ℝ := fun u =>
    ∑ k : Fin n, Finset.univ.sup' Finset.univ_nonempty (fun j : Fin m => dot u (q k j))
  have hsupp_cont : Continuous suppSum := by
    unfold suppSum
    refine continuous_finsetSum _ fun k _ => ?_
    exact continuous_sup' Finset.univ_nonempty (fun j u => dot u (q k j)) fun j _ => by
      have hfun : (fun u : Fin r' → ℝ => dot u (q k j)) = (fun u => dot (q k j) u) :=
        funext fun u => dot_comm u (q k j)
      rw [hfun]
      exact dot_continuous (q k j)
  have hsupp_pos : ∀ u ∈ sphere, 0 < suppSum u := by
    intro u hu
    have hu_ne : u ≠ 0 := by
      obtain ⟨c0, hc0⟩ := hu.2
      intro h0; rw [h0] at hc0; simp at hc0
    have hterm_nn : ∀ k : Fin n,
        0 ≤ Finset.univ.sup' Finset.univ_nonempty (fun j : Fin m => dot u (q k j)) := by
      intro k
      have hsum0 : ∑ j : Fin m, dot u (q k j) = 0 := by
        rw [← dot_sum_right, hq_sum k, dot_zero_right]
      by_contra hneg
      push Not at hneg
      have hall_neg : ∀ j : Fin m, dot u (q k j) < 0 := fun j =>
        lt_of_le_of_lt (Finset.le_sup' (fun j : Fin m => dot u (q k j)) (Finset.mem_univ j)) hneg
      have hsum_neg : ∑ j : Fin m, dot u (q k j) < 0 :=
        sum_neg_of_nonpos (fun j _ => (hall_neg j).le) ⟨⟨0, by omega⟩, Finset.mem_univ _, hall_neg _⟩
      linarith
    have hex_pos : ∃ k : Fin n,
        0 < Finset.univ.sup' Finset.univ_nonempty (fun j : Fin m => dot u (q k j)) := by
      by_contra hall
      push Not at hall
      have hall_le0 : ∀ k j, dot u (q k j) ≤ 0 := fun k j =>
        le_trans (Finset.le_sup' (fun j : Fin m => dot u (q k j)) (Finset.mem_univ j)) (hall k)
      have hall_eq0 : ∀ k j, dot u (q k j) = 0 := by
        intro k j
        have hsum0 : ∑ j' : Fin m, dot u (q k j') = 0 := by
          rw [← dot_sum_right, hq_sum k, dot_zero_right]
        by_contra hne0
        have hlt : dot u (q k j) < 0 := lt_of_le_of_ne (hall_le0 k j) hne0
        have hsum_neg : ∑ j' : Fin m, dot u (q k j') < 0 :=
          sum_neg_of_nonpos (fun j' _ => hall_le0 k j') ⟨j, Finset.mem_univ j, hlt⟩
        linarith
      have hdot_top : ∀ v : Fin r' → ℝ, dot u v = 0 := by
        intro v
        have hv : v ∈ Submodule.span ℝ { w : Fin r' → ℝ | ∃ k j, q k j = w } := by
          rw [hq_span]; trivial
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
        · rintro _ ⟨k, j, rfl⟩; exact hall_eq0 k j
        · exact dot_zero_right u
        · intro x y _ _ hx hy; rw [dot_add_right, hx, hy, add_zero]
        · intro c x _ hx; rw [dot_smul_right, hx, mul_zero]
      exact hu_ne (dot_self_eq_zero (hdot_top u))
    obtain ⟨k0, hk0⟩ := hex_pos
    exact Finset.sum_pos' (fun k _ => hterm_nn k) ⟨k0, Finset.mem_univ k0, hk0⟩
  obtain ⟨u_min, hu_min_mem, hu_min_le⟩ := hsphere_compact.exists_isMinOn hsphere_ne hsupp_cont.continuousOn
  set δ := suppSum u_min
  have hδ_pos : 0 < δ := hsupp_pos u_min hu_min_mem
  have hsupp_bound : ∀ u : Fin r' → ℝ, ∀ c : Fin r', δ * |u c| ≤ suppSum u := by
    intro u c
    by_cases hu0 : u = 0
    · subst hu0
      simp only [Pi.zero_apply, abs_zero, mul_zero, suppSum]
      have : ∀ k : Fin n, Finset.univ.sup' Finset.univ_nonempty (fun j : Fin m => dot (0 : Fin r' → ℝ) (q k j)) = 0 := by
        intro k
        apply le_antisymm
        · exact Finset.sup'_le _ _ fun j _ => by simp [dot_zero_left]
        · exact le_trans (by simp [dot_zero_left])
            (Finset.le_sup' (fun j : Fin m => dot (0 : Fin r' → ℝ) (q k j)) (Finset.mem_univ ⟨0, by omega⟩))
      simp [this]
    · obtain ⟨cmax, _, hcmax⟩ := Finset.univ.exists_max_image (fun c' : Fin r' => |u c'|)
        ⟨⟨0, hr'_pos⟩, Finset.mem_univ _⟩
      set M := |u cmax|
      have hM_pos : 0 < M := by
        by_contra hle; push Not at hle
        apply hu0; ext c'
        have : |u c'| ≤ 0 := le_trans (hcmax c' (Finset.mem_univ _)) hle
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
      let u1 : Fin r' → ℝ := M⁻¹ • u
      have hu1_mem : u1 ∈ sphere := by
        refine ⟨fun c' => ?_, cmax, ?_⟩
        · simp only [u1, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hM_pos]
          rw [inv_mul_le_iff₀ hM_pos, mul_one]
          exact hcmax c' (Finset.mem_univ _)
        · simp only [u1, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hM_pos]
          exact inv_mul_cancel₀ hM_pos.ne'
      have hhom : suppSum u = M * suppSum u1 := by
        simp only [suppSum, u1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        apply le_antisymm
        · exact Finset.sup'_le _ _ fun j _ => by
            have hle := Finset.le_sup' (fun j' : Fin m => dot (M⁻¹ • u) (q k j')) (Finset.mem_univ j)
            rw [dot_smul_left] at hle
            have := mul_le_mul_of_nonneg_left hle hM_pos.le
            rwa [← mul_assoc, mul_inv_cancel₀ hM_pos.ne', one_mul] at this
        · have hle_u : ∀ j : Fin m, M * dot (M⁻¹ • u) (q k j) ≤
              Finset.univ.sup' Finset.univ_nonempty (fun j' : Fin m => dot u (q k j')) := by
            intro j
            rw [dot_smul_left, ← mul_assoc, mul_inv_cancel₀ hM_pos.ne', one_mul]
            exact Finset.le_sup' (fun j' : Fin m => dot u (q k j')) (Finset.mem_univ j)
          have hdiv : ∀ j : Fin m, dot (M⁻¹ • u) (q k j) ≤
              M⁻¹ * Finset.univ.sup' Finset.univ_nonempty (fun j' : Fin m => dot u (q k j')) := by
            intro j
            have := mul_le_mul_of_nonneg_left (hle_u j) (inv_nonneg.mpr hM_pos.le)
            rwa [← mul_assoc, inv_mul_cancel₀ hM_pos.ne', one_mul] at this
          have hsup := Finset.sup'_le Finset.univ_nonempty _ fun j _ => hdiv j
          have := mul_le_mul_of_nonneg_left hsup hM_pos.le
          rwa [← mul_assoc, mul_inv_cancel₀ hM_pos.ne', one_mul] at this
      have hδ_le : δ ≤ suppSum u1 := hu_min_le hu1_mem
      calc δ * |u c| ≤ δ * M := mul_le_mul_of_nonneg_left (hcmax c (Finset.mem_univ _)) hδ_pos.le
        _ ≤ suppSum u1 * M := mul_le_mul_of_nonneg_right hδ_le hM_pos.le
        _ = suppSum u := by rw [hhom, mul_comm]
  -- Step 5: Build the Cayley-dual polytope in dimension D = r' + (n - 1) with N = n * m facets!
  let D := r' + (n - 1)
  have hD_le : D ≤ 2 * n - 1 := by omega
  have hD_ge : n ≤ D := by omega
  have hD_div : D / 2 + 1 ≤ n := by omega
  let N := n * m
  -- Equivalence Fin n × Fin m ≃ Fin N
  let eIdx : Fin n × Fin m ≃ Fin N := finProdFinEquiv
  -- Coordinates of x : Fin D → ℝ: first r' are u, last (n - 1) are α_0, ..., α_{n-2};
  -- α_{n-1} = 1 - ∑_{k < n-1} α_k!
  let splitU : (Fin D → ℝ) → (Fin r' → ℝ) := fun x c => x ⟨c.1, by omega⟩
  let splitA : (Fin D → ℝ) → (Fin (n - 1) → ℝ) := fun x t => x ⟨r' + t.1, by omega⟩
  let mkX : (Fin r' → ℝ) → (Fin (n - 1) → ℝ) → (Fin D → ℝ) := fun u α idx =>
    if h : idx.1 < r' then u ⟨idx.1, h⟩ else α ⟨idx.1 - r', by omega⟩
  have hsplitU_mkX : ∀ u α, splitU (mkX u α) = u := by
    intro u α; ext c; simp [splitU, mkX, c.2]
  have hsplitA_mkX : ∀ u α, splitA (mkX u α) = α := by
    intro u α; ext t
    have hnot : ¬ (r' + t.1 < r') := by omega
    simp [splitA, mkX, hnot]
  let A_pair : Fin n → Fin m → (Fin D → ℝ) := fun k j =>
    if h : k.1 < n - 1 then
      mkX (q k j) (-Pi.single ⟨k.1, h⟩ (1 : ℝ))
    else
      mkX (q k j) (fun _ => 1)
  let b_pair : Fin n → Fin m → ℝ := fun k _ => if k.1 < n - 1 then 0 else 1
  let A : Fin N → Fin D → ℝ := fun a => A_pair (eIdx.symm a).1 (eIdx.symm a).2
  let b : Fin N → ℝ := fun a => b_pair (eIdx.symm a).1 (eIdx.symm a).2
  have hdot_pair : ∀ (k : Fin n) (j : Fin m) (x : Fin D → ℝ),
      dot (A_pair k j) x =
        if h : k.1 < n - 1 then dot (q k j) (splitU x) - splitA x ⟨k.1, h⟩
        else dot (q k j) (splitU x) + ∑ t : Fin (n - 1), splitA x t := by
    intro k j x
    have hsum_split : ∀ (f : Fin D → ℝ),
        ∑ idx : Fin D, f idx =
          (∑ c : Fin r', f ⟨c.1, by omega⟩) + ∑ t : Fin (n - 1), f ⟨r' + t.1, by omega⟩ := by
      intro f
      exact Fin.sum_univ_add f
    conv_lhs => simp only [dot]
    rw [hsum_split]
    split_ifs with hk
    · have h1 : ∑ c : Fin r', A_pair k j ⟨c.1, by omega⟩ * x ⟨c.1, by omega⟩ =
          dot (q k j) (splitU x) := by
        simp only [A_pair, dif_pos hk, mkX, splitU, dot]
        refine Finset.sum_congr rfl fun c _ => by simp [c.2]
      have h2 : ∑ t : Fin (n - 1), A_pair k j ⟨r' + t.1, by omega⟩ * x ⟨r' + t.1, by omega⟩ =
          -splitA x ⟨k.1, hk⟩ := by
        simp only [A_pair, dif_pos hk, mkX, splitA]
        rw [Finset.sum_eq_single (⟨k.1, hk⟩ : Fin (n - 1))]
        · have hnot : ¬ (r' + k.1 < r') := by omega
          simp [hnot]
        · intro t _ ht
          have hnot : ¬ (r' + t.1 < r') := by omega
          simp [hnot, ht]
        · intro h; exact (h (Finset.mem_univ _)).elim
      rw [h1, h2]; ring
    · have h1 : ∑ c : Fin r', A_pair k j ⟨c.1, by omega⟩ * x ⟨c.1, by omega⟩ =
          dot (q k j) (splitU x) := by
        simp only [A_pair, dif_neg hk, mkX, splitU, dot]
        refine Finset.sum_congr rfl fun c _ => by simp [c.2]
      have h2 : ∑ t : Fin (n - 1), A_pair k j ⟨r' + t.1, by omega⟩ * x ⟨r' + t.1, by omega⟩ =
          ∑ t : Fin (n - 1), splitA x t := by
        simp only [A_pair, dif_neg hk, mkX, splitA]
        refine Finset.sum_congr rfl fun t _ => ?_
        have hnot : ¬ (r' + t.1 < r') := by omega
        simp [hnot]
      rw [h1, h2]
  -- Step 6: Any perturbed polytope P_ε with |ε a| < 1 / (2 * n) is bounded!
  have hP_bdd : ∀ (ε : Fin N → ℝ), (∀ a, |ε a| < 1 / (2 * (n : ℝ))) →
      ∃ R : ℝ, ∀ x : Fin D → ℝ, (∀ a, dot (A a) x ≤ b a + ε a) → ∀ idx, |x idx| ≤ R := by
    intro ε hε
    let Qmax : ℝ := 1 + ∑ k : Fin n, ∑ j : Fin m, ∑ c : Fin r', |q k j c|
    let Ru : ℝ := 2 / δ
    let Rα : ℝ := 2 + (n : ℝ) * (Ru * Qmax + 1)
    refine ⟨max Ru Rα, fun x hx idx => ?_⟩
    have hx_pair : ∀ k j, dot (A_pair k j) x ≤ b_pair k j + ε (eIdx (k, j)) := by
      intro k j
      have := hx (eIdx (k, j))
      simpa [A, b] using this
    -- Bound splitU x using suppSum (splitU x) ≤ 2!
    have hsupp_le : suppSum (splitU x) ≤ 2 := by
      have hper_k : ∀ k : Fin n,
          Finset.univ.sup' Finset.univ_nonempty (fun j : Fin m => dot (splitU x) (q k j)) ≤
            (if h : k.1 < n - 1 then splitA x ⟨k.1, h⟩ else 1 - ∑ t : Fin (n - 1), splitA x t) +
              1 / (2 * (n : ℝ)) := by
        intro k
        refine Finset.sup'_le _ _ fun j _ => ?_
        have h1 := hx_pair k j
        rw [hdot_pair] at h1
        have hε_lt : ε (eIdx (k, j)) < 1 / (2 * (n : ℝ)) := (abs_lt.mp (hε _)).2
        rw [dot_comm]
        split_ifs at h1 ⊢ with hk
        · simp only [b_pair, if_pos hk] at h1; linarith
        · simp only [b_pair, if_neg hk] at h1; linarith
      have hsum_alpha : ∑ k : Fin n,
          (if h : k.1 < n - 1 then splitA x ⟨k.1, h⟩ else 1 - ∑ t : Fin (n - 1), splitA x t) = 1 := by
        have hlast : (⟨n - 1, by omega⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
        rw [← Finset.add_sum_erase _ _ hlast]
        have hnot : ¬ (n - 1 < n - 1) := by omega
        simp only [dif_neg hnot]
        have hrest : ∑ k ∈ Finset.univ.erase (⟨n - 1, by omega⟩ : Fin n),
            (if h : k.1 < n - 1 then splitA x ⟨k.1, h⟩ else 1 - ∑ t : Fin (n - 1), splitA x t) =
            ∑ t : Fin (n - 1), splitA x t := by
          refine Finset.sum_bij (fun k hk => ⟨k.1, by
            have hne := (Finset.mem_erase.mp hk).1
            have hlt := k.2
            have : k.1 ≠ n - 1 := fun h => hne (Fin.ext h)
            omega⟩) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro k1 _ k2 _ h; exact Fin.ext (congrArg (fun x : Fin (n - 1) => x.1) h)
          · intro t _
            refine ⟨⟨t.1, by omega⟩, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, by ext; rfl⟩
            intro h; have := congrArg Fin.val h; dsimp at this; omega
          · intro k hk
            have hlt : k.1 < n - 1 := by
              have hne := (Finset.mem_erase.mp hk).1
              have : k.1 ≠ n - 1 := fun h => hne (Fin.ext h)
              omega
            simp [dif_pos hlt]
        rw [hrest]; ring
      calc suppSum (splitU x)
          ≤ ∑ k : Fin n, ((if h : k.1 < n - 1 then splitA x ⟨k.1, h⟩
              else 1 - ∑ t : Fin (n - 1), splitA x t) + 1 / (2 * (n : ℝ))) :=
            Finset.sum_le_sum fun k _ => hper_k k
        _ = 1 + (n : ℝ) * (1 / (2 * (n : ℝ))) := by
            rw [Finset.sum_add_distrib, hsum_alpha, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
        _ ≤ 2 := by
            have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
            have : (n : ℝ) * (1 / (2 * (n : ℝ))) = 1 / 2 := by field_simp [hnR.ne']
            linarith
    have hu_bd : ∀ c : Fin r', |splitU x c| ≤ Ru := by
      intro c
      have h1 := hsupp_bound (splitU x) c
      have : δ * |splitU x c| ≤ 2 := le_trans h1 hsupp_le
      dsimp [Ru]
      exact (le_div_iff₀' hδ_pos).mpr this
    -- Bound every splitA x t from below and above!
    have hdot_bd : ∀ k j, |dot (q k j) (splitU x)| ≤ Ru * Qmax := by
      intro k j
      calc |dot (q k j) (splitU x)|
          ≤ ∑ c : Fin r', |q k j c * splitU x c| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ c : Fin r', |q k j c| * Ru := by
            refine Finset.sum_le_sum fun c _ => ?_
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hu_bd c) (abs_nonneg _)
        _ = Ru * ∑ c : Fin r', |q k j c| := by rw [← Finset.sum_mul, mul_comm]
        _ ≤ Ru * Qmax := by
            refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (by norm_num) hδ_pos.le)
            have hle1 : ∑ c : Fin r', |q k j c| ≤ ∑ j' : Fin m, ∑ c : Fin r', |q k j' c| :=
              Finset.single_le_sum (f := fun j' => ∑ c : Fin r', |q k j' c|)
                (fun j' _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)
            have hle2 : ∑ j' : Fin m, ∑ c : Fin r', |q k j' c| ≤
                ∑ k' : Fin n, ∑ j' : Fin m, ∑ c : Fin r', |q k' j' c| :=
              Finset.single_le_sum (f := fun k' => ∑ j' : Fin m, ∑ c : Fin r', |q k' j' c|)
                (fun k' _ => Finset.sum_nonneg fun _ _ =>
                  Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ k)
            dsimp [Qmax]; linarith
    have hα_lo : ∀ t : Fin (n - 1), -(Ru * Qmax + 1) ≤ splitA x t := by
      intro t
      let k : Fin n := ⟨t.1, by omega⟩
      let j0 : Fin m := ⟨0, by omega⟩
      have h1 := hx_pair k j0
      rw [hdot_pair] at h1
      have hk : k.1 < n - 1 := t.2
      simp only [dif_pos hk, b_pair, if_pos hk] at h1
      have hε1 : ε (eIdx (k, j0)) < 1 := by
        have hlt := (abs_lt.mp (hε (eIdx (k, j0)))).2
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
        have : 1 / (2 * (n : ℝ)) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        linarith
      have hdb := (abs_le.mp (hdot_bd k j0)).1
      linarith
    have hα_sum_hi : ∑ t : Fin (n - 1), splitA x t ≤ 2 + Ru * Qmax := by
      let kn : Fin n := ⟨n - 1, by omega⟩
      let j0 : Fin m := ⟨0, by omega⟩
      have h1 := hx_pair kn j0
      rw [hdot_pair] at h1
      have hnot : ¬ (kn.1 < n - 1) := by dsimp [kn]; omega
      simp only [dif_neg hnot, b_pair, if_neg hnot] at h1
      have hε1 : ε (eIdx (kn, j0)) < 1 := by
        have hlt := (abs_lt.mp (hε (eIdx (kn, j0)))).2
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
        have : 1 / (2 * (n : ℝ)) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        linarith
      have hdb := (abs_le.mp (hdot_bd kn j0)).1
      linarith
    have hα_bd : ∀ t : Fin (n - 1), |splitA x t| ≤ Rα := by
      intro t
      have hlo := hα_lo t
      have hhi : splitA x t ≤ Rα := by
        have hsum_rest : ∑ s ∈ Finset.univ.erase t, (-(Ru * Qmax + 1)) ≤
            ∑ s ∈ Finset.univ.erase t, splitA x s :=
          Finset.sum_le_sum fun s _ => hα_lo s
        have hcard_er : (Finset.univ.erase t).card ≤ n - 1 := by
          have := Finset.card_erase_le (s := (Finset.univ : Finset (Fin (n - 1)))) (a := t)
          simp at this ⊢
        have hsp : splitA x t + ∑ s ∈ Finset.univ.erase t, splitA x s = ∑ s : Fin (n - 1), splitA x s :=
          Finset.add_sum_erase _ _ (Finset.mem_univ t)
        have hnn : 0 ≤ Ru * Qmax + 1 := by
          have hRu : 0 ≤ Ru := div_nonneg (by norm_num) hδ_pos.le
          have hQm : 0 ≤ Qmax := by
            dsimp [Qmax]
            have : 0 ≤ ∑ k : Fin n, ∑ j : Fin m, ∑ c : Fin r', |q k j c| :=
              Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
            linarith
          nlinarith
        have hcard_le_n : ((Finset.univ.erase t).card : ℝ) + 1 ≤ (n : ℝ) := by
          have : (Finset.univ.erase t).card + 1 ≤ n := by omega
          exact_mod_cast this
        simp only [Finset.sum_const, nsmul_eq_mul] at hsum_rest
        dsimp [Rα]
        nlinarith
      rw [abs_le]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
      have hnn : 0 ≤ Ru * Qmax + 1 := by
        have hRu : 0 ≤ Ru := div_nonneg (by norm_num) hδ_pos.le
        have hQm : 0 ≤ Qmax := by
          dsimp [Qmax]
          have : 0 ≤ ∑ k : Fin n, ∑ j : Fin m, ∑ c : Fin r', |q k j c| :=
            Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
          linarith
        nlinarith
      exact ⟨by dsimp [Rα]; nlinarith, hhi⟩
    by_cases hidx : idx.1 < r'
    · exact le_trans (hu_bd ⟨idx.1, hidx⟩) (le_max_left _ _)
    · have ht : idx.1 - r' < n - 1 := by omega
      have hxeq : x idx = splitA x ⟨idx.1 - r', ht⟩ := by
        dsimp [splitA]; congr 1; ext; dsimp; omega
      rw [hxeq]
      exact le_trans (hα_bd ⟨idx.1 - r', ht⟩) (le_max_right _ _)
  -- Step 7: For each i ∈ SV, build its witness x^(i) and right-inverse L_i on the n tight equations!
  let SV : Finset (Fin n → Fin m) := Finset.univ.filter (StrictVert Q)
  have hex_wit : ∀ i ∈ SV,
      ∃ (xi : Fin D → ℝ) (Li : (Fin n → ℝ) →ₗ[ℝ] (Fin D → ℝ)) (δi : ℝ),
        0 < δi ∧
        (∀ k : Fin n, dot (A_pair k (i k)) xi = b_pair k (i k)) ∧
        (∀ k : Fin n, ∀ j : Fin m, j ≠ i k → dot (A_pair k j) xi + δi ≤ b_pair k j) ∧
        (∀ (v : Fin n → ℝ) (k : Fin n), dot (A_pair k (i k)) (Li v) = v k) := by
    intro i hi
    have hq_sv := hSV_to_q i (Finset.mem_filter.mp hi).2
    obtain ⟨u0, hu0⟩ := hq_sv
    -- Normalize u0 by S_u = ∑ k, dot u0 (q k (i k)) > 0
    have hSu_pos : 0 < ∑ k : Fin n, dot u0 (q k (i k)) := by
      have hterm_pos : ∀ k : Fin n, 0 < dot u0 (q k (i k)) := by
        intro k
        have hsum0 : ∑ j : Fin m, dot u0 (q k j) = 0 := by
          rw [← dot_sum_right, hq_sum k, dot_zero_right]
        have hlt_all : ∀ j : Fin m, j ≠ i k → dot u0 (q k j) < dot u0 (q k (i k)) := hu0 k
        have hex_ne : ∃ j : Fin m, j ≠ i k := by
          by_cases h0 : i k = ⟨0, by omega⟩
          · exact ⟨⟨1, by omega⟩, by rw [h0]; intro h; exact absurd (congrArg Fin.val h) (by norm_num)⟩
          · exact ⟨⟨0, by omega⟩, Ne.symm h0⟩
        obtain ⟨j1, hj1⟩ := hex_ne
        have hlt_sum : ∑ j : Fin m, dot u0 (q k j) < ∑ _j : Fin m, dot u0 (q k (i k)) :=
          Finset.sum_lt_sum (fun j _ => by
            by_cases hj : j = i k
            · rw [hj]
            · exact (hlt_all j hj).le)
            ⟨j1, Finset.mem_univ j1, hlt_all j1 hj1⟩
        rw [hsum0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt_sum
        have hmpos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
        nlinarith
      exact Finset.sum_pos (fun k _ => hterm_pos k) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    set S_u := ∑ k : Fin n, dot u0 (q k (i k))
    let u1 : Fin r' → ℝ := S_u⁻¹ • u0
    let α1 : Fin (n - 1) → ℝ := fun t => dot u1 (q ⟨t.1, by omega⟩ (i ⟨t.1, by omega⟩))
    let xi : Fin D → ℝ := mkX u1 α1
    have hxi_tight : ∀ k : Fin n, dot (A_pair k (i k)) xi = b_pair k (i k) := by
      intro k
      rw [hdot_pair, hsplitU_mkX, hsplitA_mkX]
      split_ifs with hk
      · simp only [b_pair, if_pos hk, α1, dot_comm (q k (i k)) u1]; ring
      · simp only [b_pair, if_neg hk]
        have hk_eq : k = ⟨n - 1, by omega⟩ := by ext; dsimp; omega
        rw [hk_eq]
        have hsum_all : dot u1 (q ⟨n - 1, by omega⟩ (i ⟨n - 1, by omega⟩)) +
            ∑ t : Fin (n - 1), α1 t = 1 := by
          have hlast : (⟨n - 1, by omega⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
          have htot : ∑ k' : Fin n, dot u1 (q k' (i k')) = 1 := by
            simp only [u1, dot_smul_left, ← Finset.mul_sum]
            exact inv_mul_cancel₀ hSu_pos.ne'
          rw [← htot, ← Finset.add_sum_erase _ _ hlast]
          congr 1
          refine Finset.sum_bij (fun t _ => ⟨t.1, by omega⟩) ?_ ?_ ?_ ?_
          · intro t _
            refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
            intro h; have := congrArg Fin.val h; dsimp at this; omega
          · intro t1 _ t2 _ h; exact Fin.ext (congrArg (fun x : Fin n => x.1) h)
          · intro k' hk'
            have hne := (Finset.mem_erase.mp hk').1
            have hlt : k'.1 < n - 1 := by
              have : k'.1 ≠ n - 1 := fun h => hne (Fin.ext h); omega
            exact ⟨⟨k'.1, hlt⟩, Finset.mem_univ _, by ext; rfl⟩
          · intro t _; rfl
        rw [dot_comm]; exact hsum_all
    have hxi_strict : ∀ k j, j ≠ i k → dot (A_pair k j) xi < b_pair k j := by
      intro k j hj
      have hlt : dot u1 (q k j) < dot u1 (q k (i k)) := by
        simp only [u1, dot_smul_left]
        exact mul_lt_mul_of_pos_left (hu0 k j hj) (inv_pos.mpr hSu_pos)
      have ht := hxi_tight k
      rw [hdot_pair] at ht ⊢
      rw [hsplitU_mkX, hsplitA_mkX] at ht ⊢
      rw [dot_comm (q k j) u1, dot_comm (q k (i k)) u1] at *
      split_ifs at ht ⊢ <;> linarith
    -- Linear independence of { A_pair k (i k) | k : Fin n }!
    have hli_i : LinearIndependent ℝ (fun k : Fin n => A_pair k (i k)) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      -- Look at last (n - 1) coords: -c k + c (n-1) = 0 for k < n - 1
      let kn : Fin n := ⟨n - 1, by omega⟩
      have hce : ∀ k : Fin n, c k = c kn := by
        intro k
        by_cases hk : k.1 < n - 1
        · have hidx := congrFun hc ⟨r' + k.1, by omega⟩
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hidx
          have hval : ∀ k' : Fin n, A_pair k' (i k') ⟨r' + k.1, by omega⟩ =
              if k' = k then -1 else if k' = kn then 1 else 0 := by
            intro k'
            have hnot : ¬ (r' + k.1 < r') := by omega
            by_cases hk' : k'.1 < n - 1
            · simp only [A_pair, dif_pos hk', mkX, dif_neg hnot, Pi.neg_apply, Pi.single_apply]
              have hne_kn : k' ≠ kn := fun h => by have := congrArg Fin.val h; dsimp [kn] at this; omega
              simp only [hne_kn, ↓reduceIte]
              by_cases hkk' : k' = k
              · subst hkk'; simp
              · have hne_val : k.1 ≠ k'.1 := fun h => hkk' (Fin.ext h.symm)
                simp [hkk', hne_val]
            · have hk'_eq : k' = kn := by ext; dsimp [kn]; omega
              have hne_k : k' ≠ k := fun h => by rw [h] at hk'; exact hk' hk
              simp only [A_pair, dif_neg hk', mkX, dif_neg hnot]
              rw [if_neg hne_k, if_pos hk'_eq]
          have hsum_eval : ∑ k' : Fin n, c k' * A_pair k' (i k') ⟨r' + k.1, by omega⟩ = -c k + c kn := by
            simp_rw [hval]
            have hkne : k ≠ kn := fun h => by have := congrArg Fin.val h; dsimp [kn] at this; omega
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
            rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hkne.symm, Finset.mem_univ kn⟩)]
            have hrest : ∑ k' ∈ (Finset.univ.erase k).erase kn,
                c k' * (if k' = k then (-1 : ℝ) else if k' = kn then 1 else 0) = 0 := by
              refine Finset.sum_eq_zero fun k' hk' => ?_
              have h1 : k' ≠ kn := (Finset.mem_erase.mp hk').1
              have h2 : k' ≠ k := (Finset.mem_erase.mp (Finset.mem_erase.mp hk').2).1
              simp [h1, h2]
            rw [hrest, if_pos rfl, if_neg hkne.symm, if_pos rfl]; ring
          linarith
        · have : k = kn := by ext; dsimp [kn]; omega
          rw [this]
      -- Now dot with xi: ∑ k, c k * b_pair k (i k) = c kn * 1 = 0!
      have hdot0 : dot (∑ k : Fin n, c k • A_pair k (i k)) xi = 0 := by
        rw [hc, dot_zero_left]
      rw [dot_sum_left] at hdot0
      have hsum_b : ∑ k : Fin n, dot (c k • A_pair k (i k)) xi = c kn := by
        simp_rw [dot_smul_left, hxi_tight, hce]
        rw [← Finset.mul_sum]
        have hb1 : ∑ k : Fin n, b_pair k (i k) = 1 := by
          rw [Finset.sum_eq_single kn]
          · simp [b_pair, kn]
          · intro k _ hk_ne
            have hlt : k.1 < n - 1 := by
              have : k.1 ≠ n - 1 := fun h => hk_ne (Fin.ext h); omega
            simp [b_pair, hlt]
          · intro h; exact (h (Finset.mem_univ kn)).elim
        rw [hb1, mul_one]
      have hckn : c kn = 0 := by linarith
      intro k; rw [hce k, hckn]
    -- Build right inverse Li of x ↦ (dot (A_pair k (i k)) x)_k via surjectivity!
    let ev : (Fin D → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      { toFun := fun x k => dot (A_pair k (i k)) x
        map_add' := fun x1 x2 => by ext k; exact dot_add_right _ x1 x2
        map_smul' := fun c x => by ext k; simp [dot_smul_right] }
    have hev_surj : Function.Surjective ev := by
      rw [← LinearMap.range_eq_top]
      by_contra hne_top
      obtain ⟨c, hc_ne, hc_orth⟩ := exists_orth_ne_zero hne_top
      have hdep : ∑ k : Fin n, c k • A_pair k (i k) = 0 := by
        apply dot_self_eq_zero
        have hzero : ∀ x : Fin D → ℝ, dot (∑ k : Fin n, c k • A_pair k (i k)) x = 0 := by
          intro x
          have h0 := hc_orth (ev x) (LinearMap.mem_range_self ev x)
          have h1 : dot (ev x) c = ∑ k : Fin n, c k * dot (A_pair k (i k)) x := by
            simp only [dot, ev, LinearMap.coe_mk, AddHom.coe_mk]
            exact Finset.sum_congr rfl fun k _ => mul_comm _ _
          rw [dot_sum_left]
          simp_rw [dot_smul_left]
          rw [← h1, h0]
        exact hzero _
      have hall0 := Fintype.linearIndependent_iff.mp hli_i c hdep
      exact hc_ne (funext hall0)
    -- Construct linear right inverse Li on the standard basis of Fin n → ℝ
    have hex_pre : ∀ k : Fin n, ∃ w : Fin D → ℝ, ev w = Pi.single k 1 := fun k => hev_surj (Pi.single k 1)
    choose w_pre hw_pre using hex_pre
    let Li : (Fin n → ℝ) →ₗ[ℝ] (Fin D → ℝ) :=
      { toFun := fun v => ∑ k : Fin n, v k • w_pre k
        map_add' := fun v1 v2 => by
          simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := fun c v => by
          simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
    have hLi : ∀ (v : Fin n → ℝ) (k : Fin n), dot (A_pair k (i k)) (Li v) = v k := by
      intro v k
      change ev (Li v) k = v k
      simp only [Li, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, hw_pre,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      rw [Finset.sum_eq_single k]
      · simp
      · intro k' _ hk'; simp [hk'.symm]
      · intro h; exact (h (Finset.mem_univ k)).elim
    -- Minimum strict slack δi > 0 over all (k, j) with j ≠ i k
    let Off : Finset (Fin n × Fin m) := Finset.univ.filter fun p => p.2 ≠ i p.1
    have hOff_ne : Off.Nonempty := by
      let k0 : Fin n := ⟨0, hn⟩
      by_cases h0 : i k0 = ⟨0, by omega⟩
      · exact ⟨(k0, ⟨1, by omega⟩), Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [h0]; intro h; exact absurd (congrArg Fin.val h) (by norm_num)⟩⟩
      · exact ⟨(k0, ⟨0, by omega⟩), Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ne.symm h0⟩⟩
    obtain ⟨pMin, hpMin_mem, hpMin_le⟩ :=
      Off.exists_min_image (fun p => b_pair p.1 p.2 - dot (A_pair p.1 p.2) xi) hOff_ne
    set δi := b_pair pMin.1 pMin.2 - dot (A_pair pMin.1 pMin.2) xi
    have hδi_pos : 0 < δi := by
      have hne := (Finset.mem_filter.mp hpMin_mem).2
      linarith [hxi_strict pMin.1 pMin.2 hne]
    refine ⟨xi, Li, δi, hδi_pos, hxi_tight, fun k j hj => ?_, hLi⟩
    have := hpMin_le (k, j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
    linarith
  -- Step 8: Pick a tiny generic RHS perturbation ε : Fin N → ℝ so P_ε is bounded, simple, and preserves all i ∈ SV!
  -- Every (D+1)-subset T ⊆ Fin N gives a linear dependence ∑ a ∈ T, ψ a • A a = 0!
  let BadSubs : Finset (Finset (Fin N)) := Finset.univ.filter fun T : Finset (Fin N) => T.card = D + 1
  have hex_dep : ∀ T ∈ BadSubs, ∃ ψ : Fin N → ℝ, ψ ≠ 0 ∧ (∀ a ∉ T, ψ a = 0) ∧
      ∑ a : Fin N, ψ a • A a = 0 := by
    intro T hT
    have hcardT : T.card = D + 1 := (Finset.mem_filter.mp hT).2
    let L : (T → ℝ) →ₗ[ℝ] (Fin D → ℝ) :=
      { toFun := fun c => ∑ a : T, c a • A a.1
        map_add' := fun c1 c2 => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := fun r c => by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
    have hker_ne : LinearMap.ker L ≠ ⊥ := by
      intro hbot
      have hrk := LinearMap.finrank_range_add_finrank_ker L
      rw [hbot, finrank_bot, add_zero] at hrk
      have hle : Module.finrank ℝ (LinearMap.range L) ≤ D := by
        simpa using Submodule.finrank_le (LinearMap.range L)
      have hdom : Module.finrank ℝ (T → ℝ) = D + 1 := by simp [hcardT]
      omega
    obtain ⟨c, hc_ker, hc_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
    let ψ : Fin N → ℝ := fun a => if h : a ∈ T then c ⟨a, h⟩ else 0
    refine ⟨ψ, ?_, fun a ha => dif_neg ha, ?_⟩
    · intro h0
      apply hc_ne
      ext ⟨a, ha⟩
      have := congrFun h0 a
      simpa [ψ, ha] using this
    · have hsum_eq : ∑ a : Fin N, ψ a • A a = ∑ a : T, c a • A a.1 := by
        rw [← Finset.sum_subset (Finset.subset_univ T) (fun a _ ha => by simp [ψ, ha])]
        rw [← Finset.sum_attach T]
        refine Finset.sum_congr rfl fun a _ => by simp [ψ, a.2]
      rw [hsum_eq]
      exact hc_ker
  choose ψOf hψ_spec using hex_dep
  let badHyp : Finset ((Fin N → ℝ) × ℝ) :=
    BadSubs.attach.image fun T => (ψOf T.1 T.2, -dot (ψOf T.1 T.2) b)
  have hbadHyp_ne : ∀ p ∈ badHyp, p.1 ≠ 0 := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨T, _, rfl⟩
    exact (hψ_spec T.1 T.2).1
  -- Compute safe radius η > 0 so all i ∈ SV retain their tight face in P_ε!
  choose ξOf LOf δOf hwit_spec using hex_wit
  -- Uniform bound on |dot (A_pair k j) (LOf i hi v)| ≤ (C_norm - 1) * max_l |v l|
  have hex_C : ∃ C_norm : ℝ, 0 < C_norm ∧ ∀ i (hi : i ∈ SV) (k : Fin n) (j : Fin m),
      ∑ l : Fin n, |dot (A_pair k j) (LOf i hi (Pi.single l 1))| ≤ C_norm - 1 := by
    let g : { i : Fin n → Fin m // i ∈ SV } → ℝ := fun i' =>
      ∑ k' : Fin n, ∑ j' : Fin m, ∑ l : Fin n, |dot (A_pair k' j') (LOf i'.1 i'.2 (Pi.single l 1))|
    have hg_nn : ∀ i', 0 ≤ g i' := fun _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => abs_nonneg _
    by_cases hSV : SV.Nonempty
    · obtain ⟨iMax, _, hiMax_ge⟩ := SV.attach.exists_max_image g (by
        obtain ⟨i0, hi0⟩ := hSV; exact ⟨⟨i0, hi0⟩, Finset.mem_attach _ _⟩)
      refine ⟨1 + g iMax, by linarith [hg_nn iMax], fun i hi k j => ?_⟩
      have h1 : ∑ l : Fin n, |dot (A_pair k j) (LOf i hi (Pi.single l 1))| ≤
          ∑ j' : Fin m, ∑ l : Fin n, |dot (A_pair k j') (LOf i hi (Pi.single l 1))| :=
        Finset.single_le_sum (f := fun j' => ∑ l : Fin n, |dot (A_pair k j') (LOf i hi (Pi.single l 1))|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      have h2 : ∑ j' : Fin m, ∑ l : Fin n, |dot (A_pair k j') (LOf i hi (Pi.single l 1))| ≤ g ⟨i, hi⟩ :=
        Finset.single_le_sum (f := fun k' => ∑ j' : Fin m, ∑ l : Fin n, |dot (A_pair k' j') (LOf i hi (Pi.single l 1))|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ k)
      have h3 : g ⟨i, hi⟩ ≤ g iMax := hiMax_ge ⟨i, hi⟩ (Finset.mem_attach _ _)
      linarith
    · exact ⟨1, zero_lt_one, fun i hi => (hSV ⟨i, hi⟩).elim⟩
  obtain ⟨C_norm, hC_pos, hC_le⟩ := hex_C
  have hex_δmin : ∃ δmin : ℝ, 0 < δmin ∧ ∀ i (hi : i ∈ SV), δmin ≤ δOf i hi := by
    by_cases hSV : SV.Nonempty
    · obtain ⟨iMin, _, hiMin_le⟩ :=
        SV.attach.exists_min_image (fun i => δOf i.1 i.2) (by
          obtain ⟨i0, hi0⟩ := hSV; exact ⟨⟨i0, hi0⟩, Finset.mem_attach _ _⟩)
      exact ⟨δOf iMin.1 iMin.2, (hwit_spec iMin.1 iMin.2).1,
        fun i hi => hiMin_le ⟨i, hi⟩ (Finset.mem_attach _ _)⟩
    · exact ⟨1, zero_lt_one, fun i hi => (hSV ⟨i, hi⟩).elim⟩
  obtain ⟨δmin, hδmin_pos, hδmin_le⟩ := hex_δmin
  let η : ℝ := min (1 / (2 * (n : ℝ))) (δmin / (2 * C_norm))
  have hη_pos : 0 < η := lt_min (by positivity) (div_pos hδmin_pos (by linarith))
  obtain ⟨ε, hε_small, hε_avoid⟩ := exists_avoid_hyperplanes badHyp hbadHyp_ne hη_pos
  have hε_bdd : ∀ a, |ε a| < 1 / (2 * (n : ℝ)) := fun a =>
    lt_of_lt_of_le (hε_small a) (min_le_left _ _)
  have hPε_bdd := hP_bdd ε hε_bdd
  -- P_ε is simple!
  have hPε_simple : ∀ x : Fin D → ℝ, (∀ a, dot (A a) x ≤ b a + ε a) →
      (Finset.univ.filter (fun a => dot (A a) x = b a + ε a)).card ≤ D := by
    intro x _
    by_contra hgt
    push Not at hgt
    obtain ⟨T, hT_sub, hT_card⟩ :=
      Finset.exists_subset_card_eq (Nat.succ_le_of_lt hgt)
    have hT_bad : T ∈ BadSubs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT_card⟩
    let ψ := ψOf T hT_bad
    have hψ_supp : ∀ a ∉ T, ψ a = 0 := (hψ_spec T hT_bad).2.1
    have hψ_dep : ∑ a : Fin N, ψ a • A a = 0 := (hψ_spec T hT_bad).2.2
    have hdot0 : dot (∑ a : Fin N, ψ a • A a) x = 0 := by rw [hψ_dep, dot_zero_left]
    rw [dot_sum_left] at hdot0
    have hsum_eq : ∑ a : Fin N, dot (ψ a • A a) x = dot ψ b + dot ψ ε := by
      simp only [dot_smul_left]
      rw [show dot ψ b + dot ψ ε = ∑ a : Fin N, (ψ a * b a + ψ a * ε a) by
        simp only [dot, Finset.sum_add_distrib]]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases haT : a ∈ T
      · have ht : dot (A a) x = b a + ε a := (Finset.mem_filter.mp (hT_sub haT)).2
        rw [ht]; ring
      · rw [hψ_supp a haT]; ring
    have heq_avoid : dot ψ ε = -dot ψ b := by linarith
    exact hε_avoid (ψ, -dot ψ b) (Finset.mem_image.mpr ⟨⟨T, hT_bad⟩, Finset.mem_attach _ _, rfl⟩) heq_avoid
  -- Apply Seidel's bound to P_ε!
  obtain ⟨VertSets, hVert_card, hVert_D, hVert_face⟩ :=
    simple_polytope_faces_bound A (fun a => b a + ε a) hPε_bdd hPε_simple
  -- Every i ∈ SV has a nonempty tight face E(i) = { eIdx (k, i k) | k } in P_ε!
  let faceSet : (Fin n → Fin m) → Finset (Fin N) := fun i =>
    Finset.univ.image fun k : Fin n => eIdx (k, i k)
  have hface_inj : Function.Injective faceSet := by
    intro i1 i2 heq
    funext k
    have hmem : eIdx (k, i1 k) ∈ faceSet i2 := by
      rw [← heq]; exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
    rcases Finset.mem_image.mp hmem with ⟨k', _, hk'⟩
    have hpair := eIdx.injective hk'
    have hk_eq : k' = k := congrArg Prod.fst hpair
    subst hk_eq
    exact (congrArg Prod.snd hpair).symm
  have hface_card : ∀ i, (faceSet i).card = n := by
    intro i
    rw [Finset.card_image_of_injective]
    · simp
    · intro k1 k2 h; exact congrArg Prod.fst (eIdx.injective h)
  have hSV_in_VertSets : ∀ i ∈ SV, ∃ S ∈ VertSets, faceSet i ⊆ S := by
    intro i hi
    apply hVert_face (faceSet i)
    let v_i : Fin n → ℝ := fun k => ε (eIdx (k, i k))
    let x_i : Fin D → ℝ := ξOf i hi + LOf i hi v_i
    have hδ_le : δmin ≤ δOf i hi := hδmin_le i hi
    have hLi_bd : ∀ k j, |dot (A_pair k j) (LOf i hi v_i)| ≤ (C_norm - 1) * η := by
      intro k j
      have hv_rep : v_i = ∑ l : Fin n, v_i l • Pi.single l (1 : ℝ) := by
        ext l
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
        rw [Finset.sum_eq_single l]
        · simp
        · intro l' _ hl'; simp [hl'.symm]
        · intro h; exact (h (Finset.mem_univ l)).elim
      rw [hv_rep, map_sum, dot_sum_right]
      calc |∑ l : Fin n, dot (A_pair k j) (LOf i hi (v_i l • Pi.single l 1))|
          ≤ ∑ l : Fin n, |dot (A_pair k j) (LOf i hi (v_i l • Pi.single l 1))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ l : Fin n, η * |dot (A_pair k j) (LOf i hi (Pi.single l 1))| := by
            refine Finset.sum_le_sum fun l _ => ?_
            rw [map_smul, dot_smul_right, abs_mul]
            exact mul_le_mul_of_nonneg_right (hε_small _).le (abs_nonneg _)
        _ = (∑ l : Fin n, |dot (A_pair k j) (LOf i hi (Pi.single l 1))|) * η := by
            rw [← Finset.mul_sum, mul_comm]
        _ ≤ (C_norm - 1) * η := mul_le_mul_of_nonneg_right (hC_le i hi k j) hη_pos.le
    refine ⟨x_i, ?_, ?_⟩
    · intro a
      obtain ⟨⟨k, j⟩, rfl⟩ := eIdx.surjective a
      simp only [A, b, Equiv.symm_apply_apply, x_i, dot_add_right]
      by_cases hj : j = i k
      · subst hj
        rw [(hwit_spec i hi).2.1 k, (hwit_spec i hi).2.2.2 v_i k]
      · have hslack := (hwit_spec i hi).2.2.1 k j hj
        have hη_le : η ≤ δmin / (2 * C_norm) := min_le_right _ _
        have hCη : C_norm * η ≤ δmin / 2 := by
          have := mul_le_mul_of_nonneg_left hη_le hC_pos.le
          have heq : C_norm * (δmin / (2 * C_norm)) = δmin / 2 := by field_simp [hC_pos.ne']
          linarith
        have hLi_lt : dot (A_pair k j) (LOf i hi v_i) ≤ (C_norm - 1) * η :=
          (abs_le.mp (hLi_bd k j)).2
        have hε_gt : -η < ε (eIdx (k, j)) := (abs_lt.mp (hε_small _)).1
        linarith
    · intro a ha
      rcases Finset.mem_image.mp ha with ⟨k, _, rfl⟩
      simp only [A, b, Equiv.symm_apply_apply, x_i, dot_add_right]
      rw [(hwit_spec i hi).2.1 k, (hwit_spec i hi).2.2.2 v_i k]
  -- Count: SV.image faceSet ⊆ VertSets.biUnion (fun S => S.powersetCard n)!
  have hsub_pow : SV.image faceSet ⊆ VertSets.biUnion (fun S => Finset.powersetCard n S) := by
    intro F hF
    rcases Finset.mem_image.mp hF with ⟨i, hi, rfl⟩
    obtain ⟨S, hS, hsub⟩ := hSV_in_VertSets i hi
    exact Finset.mem_biUnion.mpr ⟨S, hS, Finset.mem_powersetCard.mpr ⟨hsub, hface_card i⟩⟩
  have hSV_card : SV.card ≤ VertSets.card * 2 ^ (2 * n - 1) := by
    calc SV.card = (SV.image faceSet).card := (Finset.card_image_of_injective SV hface_inj).symm
      _ ≤ (VertSets.biUnion fun S => Finset.powersetCard n S).card := Finset.card_le_card hsub_pow
      _ ≤ ∑ S ∈ VertSets, (Finset.powersetCard n S).card := Finset.card_biUnion_le
      _ ≤ ∑ _S ∈ VertSets, 2 ^ (2 * n - 1) := by
          refine Finset.sum_le_sum fun S hS => ?_
          rw [Finset.card_powersetCard, hVert_D S hS]
          calc D.choose n ≤ 2 ^ D := Nat.choose_le_two_pow D n
            _ ≤ 2 ^ (2 * n - 1) := Nat.pow_le_pow_right (by norm_num) hD_le
      _ = VertSets.card * 2 ^ (2 * n - 1) := by simp
  have hsum_le : ∑ j ∈ Finset.range (D / 2 + 1), N.choose j ≤ 3 ^ n * m ^ (n - 1) := by
    have hsub_r : Finset.range (D / 2 + 1) ⊆ Finset.range n := Finset.range_mono hD_div
    calc ∑ j ∈ Finset.range (D / 2 + 1), N.choose j
        ≤ ∑ j ∈ Finset.range n, (n * m).choose j := Finset.sum_le_sum_of_subset hsub_r
      _ ≤ 3 ^ n * m ^ (n - 1) := sum_choose_le n m (by omega)
  have hpow4 : 2 * 2 ^ (2 * n - 1) = 4 ^ n := by
    have h2 : 2 * 2 ^ (2 * n - 1) = 2 ^ (2 * n) := by
      cases n with
      | zero => omega
      | succ k =>
        have : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
        rw [this, ← pow_succ']
        congr 1
    rw [h2, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  calc SV.card ≤ VertSets.card * 2 ^ (2 * n - 1) := hSV_card
    _ ≤ (2 * ∑ j ∈ Finset.range (D / 2 + 1), N.choose j) * 2 ^ (2 * n - 1) :=
        Nat.mul_le_mul_right _ hVert_card
    _ = (2 * 2 ^ (2 * n - 1)) * (∑ j ∈ Finset.range (D / 2 + 1), N.choose j) := by ring
    _ = 4 ^ n * (∑ j ∈ Finset.range (D / 2 + 1), N.choose j) := by rw [hpow4]
    _ ≤ 4 ^ n * (3 ^ n * m ^ (n - 1)) := Nat.mul_le_mul_left _ hsum_le
    _ = 12 ^ n * m ^ (n - 1) := by rw [← mul_assoc, ← Nat.mul_pow]

/- ### Module 5: Strict Separation, Extreme-Ray Sign Determination, and Projection Bound -/

/-- Strict separation of a point `p` outside a convex set `C` from a finite subset `F ⊆ C`. -/
private lemma strict_separate_finset {D : ℕ} {C : Set (Fin D → ℝ)} (hC : Convex ℝ C)
    {p : Fin D → ℝ} (hp : p ∉ C) {F : Finset (Fin D → ℝ)} (hF : ∀ q ∈ F, q ∈ C) :
    ∃ u : Fin D → ℝ, ∀ q ∈ F, dot u q < dot u p := by
  have hsub : convexHull ℝ (F : Set (Fin D → ℝ)) ⊆ C :=
    convexHull_min (fun q hq => hF q hq) hC
  have hp_not : p ∉ convexHull ℝ (F : Set (Fin D → ℝ)) := fun hm => hp (hsub hm)
  have hcl : IsClosed (convexHull ℝ (F : Set (Fin D → ℝ))) :=
    (F.finite_toSet.isCompact_convexHull ℝ).isClosed
  obtain ⟨f, t, hft, hfp⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hcl hp_not
  obtain ⟨u, hu⟩ := dot_linear_rep f.toLinearMap
  refine ⟨u, fun q hq => ?_⟩
  have h1 : f q < t := hft q (subset_convexHull ℝ _ hq)
  have h2 : dot u q = f q := (hu q).symm
  have h3 : dot u p = f p := (hu p).symm
  linarith

/-- If `W` spans `ℝ^{n+1}` and `N = {u | ∀ w ∈ W, dot u w > 0}` is nonempty, then whether
`∃ u ∈ N, dot u v < 0` is completely determined by the sign pattern of `v` on a finite set `R`
of orthogonal vectors to `n`-element subsets of `W_base` (with `|R| ≤ W_base.card ^ n`). -/
private lemma cone_neg_determined_by_rays {n : ℕ}
    (W_base : Finset (Fin (n + 1) → ℝ))
    (R : Finset (Fin (n + 1) → ℝ))
    (hR : ∀ S : Finset (Fin (n + 1) → ℝ),
      S ⊆ W_base → S.card = n → LinearIndependent ℝ (fun w : S => w.1) →
      ∃ r ∈ R, r ≠ 0 ∧ ∀ w ∈ S, dot w r = 0)
    (Wi : Finset (Fin (n + 1) → ℝ))
    (hWi_sub : ∀ w ∈ Wi, w ∈ W_base ∨ -w ∈ W_base)
    (hWi_span : Submodule.span ℝ (Wi : Set (Fin (n + 1) → ℝ)) = ⊤)
    (hN_ne : ∃ u : Fin (n + 1) → ℝ, ∀ w ∈ Wi, 0 < dot u w)
    {v v' : Fin (n + 1) → ℝ} (hsign : signMap R v = signMap R v') :
    (∃ u : Fin (n + 1) → ℝ, (∀ w ∈ Wi, 0 < dot u w) ∧ dot u v < 0) ↔
    (∃ u : Fin (n + 1) → ℝ, (∀ w ∈ Wi, 0 < dot u w) ∧ dot u v' < 0) := by
  classical
  -- Prove one direction and apply symmetrically!
  suffices hdir : ∀ (a b : Fin (n + 1) → ℝ), signMap R a = signMap R b →
      (∃ u : Fin (n + 1) → ℝ, (∀ w ∈ Wi, 0 < dot u w) ∧ dot u a < 0) →
      (∃ u : Fin (n + 1) → ℝ, (∀ w ∈ Wi, 0 < dot u w) ∧ dot u b < 0) by
    exact ⟨hdir v v' hsign, hdir v' v hsign.symm⟩
  intro a b hab ⟨u0, hu0_pos, hu0_neg⟩
  let w0 : Fin (n + 1) → ℝ := ∑ w ∈ Wi, w
  have hWi_ne : Wi.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Finset.coe_empty, Submodule.span_empty] at hWi_span
    have : (Pi.single (0 : Fin (n + 1)) (1 : ℝ) : Fin (n + 1) → ℝ) ∈ (⊥ : Submodule ℝ _) := by
      rw [hWi_span]; trivial
    rw [Submodule.mem_bot] at this
    have := congrFun this 0
    simp at this
  have hw0_pos : 0 < dot u0 w0 := by
    rw [dot_sum_right]
    exact Finset.sum_pos (fun w hw => hu0_pos w hw) hWi_ne
  -- Compact slice K = { u | dot u w0 = 1 ∧ ∀ w ∈ Wi, 0 ≤ dot u w }
  let K : Set (Fin (n + 1) → ℝ) := { u | dot u w0 = 1 ∧ ∀ w ∈ Wi, 0 ≤ dot u w }
  have hK_closed : IsClosed K := by
    have h1 : IsClosed { u : Fin (n + 1) → ℝ | dot u w0 = 1 } :=
      isClosed_eq (by simpa only [dot_comm _ w0] using dot_continuous w0) continuous_const
    have h2 : IsClosed { u : Fin (n + 1) → ℝ | ∀ w ∈ Wi, 0 ≤ dot u w } := by
      have : { u : Fin (n + 1) → ℝ | ∀ w ∈ Wi, 0 ≤ dot u w } = ⋂ w ∈ Wi, { u | 0 ≤ dot u w } := by
        ext u; simp
      rw [this]
      exact isClosed_biInter fun w _ =>
        isClosed_le continuous_const (by simpa only [dot_comm _ w] using dot_continuous w)
    exact h1.inter h2
  have hK_bdd : ∃ M : ℝ, ∀ u ∈ K, ∀ c : Fin (n + 1), |u c| ≤ M := by
    -- On the unit l∞-sphere, g(u) = ∑ w ∈ Wi, |dot u w| is continuous and strictly positive!
    let sphere : Set (Fin (n + 1) → ℝ) := { u | (∀ c, |u c| ≤ 1) ∧ ∃ c, |u c| = 1 }
    have hsphere_compact : IsCompact sphere := by
      have hcl : IsClosed sphere := by
        have h1 : IsClosed { u : Fin (n + 1) → ℝ | ∀ c, |u c| ≤ 1 } := by
          have : { u : Fin (n + 1) → ℝ | ∀ c, |u c| ≤ 1 } = ⋂ c, { u | |u c| ≤ 1 } := by ext u; simp
          rw [this]
          exact isClosed_iInter fun c => isClosed_le (continuous_abs.comp (continuous_apply c)) continuous_const
        have h2 : IsClosed { u : Fin (n + 1) → ℝ | ∃ c, |u c| = 1 } := by
          have : { u : Fin (n + 1) → ℝ | ∃ c, |u c| = 1 } = ⋃ c, { u | |u c| = 1 } := by ext u; simp
          rw [this]
          exact isClosed_iUnion_of_finite fun c => isClosed_eq (continuous_abs.comp (continuous_apply c)) continuous_const
        exact h1.inter h2
      exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hcl
        (fun u hu c _ => abs_le.mp (hu.1 c))
    have hsphere_ne : sphere.Nonempty :=
      ⟨Pi.single 0 1, fun c => by by_cases hc : c = 0 <;> simp [hc], 0, by simp⟩
    let g : (Fin (n + 1) → ℝ) → ℝ := fun u => ∑ w ∈ Wi, |dot u w|
    have hg_cont : Continuous g := continuous_finsetSum _ fun w _ =>
      continuous_abs.comp (by
        have hfun : (fun u : Fin (n + 1) → ℝ => dot u w) = (fun u => dot w u) :=
          funext fun u => dot_comm u w
        rw [hfun]
        exact dot_continuous w)
    have hg_pos : ∀ u ∈ sphere, 0 < g u := by
      intro u hu
      have hu_ne : u ≠ 0 := by
        obtain ⟨c0, hc0⟩ := hu.2; intro h0; rw [h0] at hc0; simp at hc0
      by_contra hle; push Not at hle
      have hall0 : ∀ w ∈ Wi, dot u w = 0 := fun w hw => by
        have hge : 0 ≤ |dot u w| := abs_nonneg _
        have hle_sum : |dot u w| ≤ g u :=
          Finset.single_le_sum (f := fun w => |dot u w|) (fun _ _ => abs_nonneg _) hw
        exact abs_eq_zero.mp (le_antisymm (le_trans hle_sum hle) hge)
      have hdot_top : ∀ x : Fin (n + 1) → ℝ, dot u x = 0 := by
        intro x
        have hx : x ∈ Submodule.span ℝ (Wi : Set (Fin (n + 1) → ℝ)) := by rw [hWi_span]; trivial
        refine Submodule.span_induction ?_ (dot_zero_right u)
          (fun _ _ _ _ hx hy => by rw [dot_add_right, hx, hy, add_zero])
          (fun c _ _ hx => by rw [dot_smul_right, hx, mul_zero]) hx
        intro w hw; exact hall0 w hw
      exact hu_ne (dot_self_eq_zero (hdot_top u))
    obtain ⟨umin, humin_mem, humin_le⟩ := hsphere_compact.exists_isMinOn hsphere_ne hg_cont.continuousOn
    set γ := g umin
    have hγ_pos : 0 < γ := hg_pos umin humin_mem
    refine ⟨1 / γ, fun u hu c => ?_⟩
    by_cases hu_zero : u = 0
    · rw [hu_zero]; simp only [Pi.zero_apply, abs_zero]; exact div_nonneg zero_le_one hγ_pos.le
    · obtain ⟨cmax, _, hcmax⟩ := Finset.univ.exists_max_image (fun c' => |u c'|) ⟨0, Finset.mem_univ _⟩
      set M := |u cmax|
      have hM_pos : 0 < M := by
        by_contra hle; push Not at hle
        apply hu_zero; ext c'
        exact abs_eq_zero.mp (le_antisymm (le_trans (hcmax c' (Finset.mem_univ _)) hle) (abs_nonneg _))
      let u1 := M⁻¹ • u
      have hu1_mem : u1 ∈ sphere := by
        refine ⟨fun c' => ?_, cmax, ?_⟩
        · simp only [u1, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hM_pos]
          rw [inv_mul_le_iff₀ hM_pos, mul_one]; exact hcmax c' (Finset.mem_univ _)
        · simp only [u1, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hM_pos]
          exact inv_mul_cancel₀ hM_pos.ne'
      have hgu : g u = 1 := by
        calc g u = ∑ w ∈ Wi, dot u w :=
              Finset.sum_congr rfl fun w hw => abs_of_nonneg (hu.2 w hw)
          _ = dot u w0 := (dot_sum_right Wi u id).symm
          _ = 1 := hu.1
      have hgu1 : g u1 = M⁻¹ := by
        calc g u1 = ∑ w ∈ Wi, |M⁻¹ * dot u w| := by simp [g, u1, dot_smul_left]
          _ = M⁻¹ * g u := by
              simp_rw [abs_mul, abs_inv, abs_of_pos hM_pos, ← Finset.mul_sum]; rfl
          _ = M⁻¹ := by rw [hgu, mul_one]
      have hγ_le : γ ≤ M⁻¹ := hgu1 ▸ humin_le hu1_mem
      have hM_le : M ≤ 1 / γ := by
        rw [le_div_iff₀ hγ_pos, mul_comm]
        have := mul_le_mul_of_nonneg_left hγ_le hM_pos.le
        rw [mul_inv_cancel₀ hM_pos.ne'] at this
        linarith
      exact le_trans (hcmax c (Finset.mem_univ _)) hM_le
  obtain ⟨MK, hMK⟩ := hK_bdd
  have hK_compact : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hK_closed
      (fun u hu c _ => abs_le.mp (hMK u hu c))
  have hu0_scaled : ((dot u0 w0)⁻¹ • u0) ∈ K := by
    refine ⟨?_, fun w hw => ?_⟩
    · rw [dot_smul_left, inv_mul_cancel₀ hw0_pos.ne']
    · rw [dot_smul_left]; exact mul_nonneg (inv_nonneg.mpr hw0_pos.le) (hu0_pos w hw).le
  have hdot_a_cont : Continuous (fun u : Fin (n + 1) → ℝ => dot u a) := by
    have hfun : (fun u : Fin (n + 1) → ℝ => dot u a) = (fun u => dot a u) :=
      funext fun u => dot_comm u a
    rw [hfun]; exact dot_continuous a
  obtain ⟨umin_a, humin_K, humin_min⟩ :=
    hK_compact.exists_isMinOn ⟨_, hu0_scaled⟩ hdot_a_cont.continuousOn
  set mval := dot umin_a a
  have hmval_neg : mval < 0 := by
    have h1 : dot umin_a a ≤ dot ((dot u0 w0)⁻¹ • u0) a := humin_min hu0_scaled
    have h2 : dot ((dot u0 w0)⁻¹ • u0) a < 0 := by
      rw [dot_smul_left]; exact mul_neg_of_pos_of_neg (inv_pos.mpr hw0_pos) hu0_neg
    linarith
  -- Pick u* ∈ K minimizing dot u a that maximizes the number of zero constraints T(u) = {w ∈ Wi | dot u w = 0}
  let tightU : (Fin (n + 1) → ℝ) → Finset (Fin (n + 1) → ℝ) := fun u =>
    Wi.filter fun w => dot u w = 0
  let MinSet : Set (Fin (n + 1) → ℝ) := { u | u ∈ K ∧ dot u a = mval }
  let Cards : Finset ℕ := (Finset.range (Wi.card + 1)).filter fun c => ∃ u ∈ MinSet, (tightU u).card = c
  have hCards_ne : Cards.Nonempty := by
    refine ⟨(tightU umin_a).card, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, umin_a, ⟨humin_K, rfl⟩, rfl⟩⟩
    exact Nat.lt_succ_of_le (Finset.card_filter_le _ _)
  obtain ⟨cmax, hcmax_mem, hcmax_ge⟩ := Cards.exists_max_image id hCards_ne
  obtain ⟨uStar, ⟨huStar_K, huStar_m⟩, huStar_card⟩ := (Finset.mem_filter.mp hcmax_mem).2
  -- Prove span (insert w0 (tightU uStar)) = ⊤!
  have hspan_top : Submodule.span ℝ (insert w0 (tightU uStar : Set (Fin (n + 1) → ℝ))) = ⊤ := by
    by_contra hne_top
    obtain ⟨h0, hh0_ne, hh0_orth⟩ := exists_orth_ne_zero hne_top
    let h : Fin (n + 1) → ℝ := if dot h0 a ≤ 0 then h0 else -h0
    have hh_ne : h ≠ 0 := by
      dsimp [h]; split_ifs
      · exact hh0_ne
      · exact neg_ne_zero.mpr hh0_ne
    have hh_a : dot h a ≤ 0 := by
      dsimp [h]; split_ifs with hle
      · exact hle
      · rw [dot_neg_left]; linarith
    have hh_w0 : dot h w0 = 0 := by
      have h0w : dot w0 h0 = 0 := hh0_orth w0 (Submodule.subset_span (Set.mem_insert _ _))
      dsimp [h]; split_ifs
      · rwa [dot_comm]
      · rw [dot_neg_left, dot_comm, h0w, neg_zero]
    have hh_tight : ∀ w ∈ tightU uStar, dot h w = 0 := by
      intro w hw
      have h0w : dot w h0 = 0 := hh0_orth w (Submodule.subset_span (Set.mem_insert_of_mem _ hw))
      dsimp [h]; split_ifs
      · rwa [dot_comm]
      · rw [dot_neg_left, dot_comm, h0w, neg_zero]
    -- Some w ∈ Wi must have dot h w < 0 (else uStar + t • h ∈ K for all t ≥ 0, contradicting hMK!)
    let NegW : Finset (Fin (n + 1) → ℝ) := Wi.filter fun w => dot h w < 0
    have hNegW_ne : NegW.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hall_nn : ∀ w ∈ Wi, 0 ≤ dot h w := by
        intro w hw
        by_contra hlt; push Not at hlt
        have : w ∈ NegW := Finset.mem_filter.mpr ⟨hw, hlt⟩
        rw [hempty] at this; exact Finset.notMem_empty w this
      have hex_k : ∃ c, h c ≠ 0 := by
        by_contra hall; push Not at hall; exact hh_ne (funext hall)
      obtain ⟨c0, hc0⟩ := hex_k
      let t : ℝ := (|uStar c0| + MK + 1) / |h c0|
      have ht_nn : 0 ≤ t := by
        have hMK_nn : 0 ≤ MK := le_trans (abs_nonneg (uStar c0)) (hMK uStar huStar_K c0)
        exact div_nonneg (by linarith [abs_nonneg (uStar c0)]) (abs_nonneg _)
      have hu_mem : uStar + t • h ∈ K := by
        refine ⟨?_, fun w hw => ?_⟩
        · rw [dot_add_left, dot_smul_left, huStar_K.1, hh_w0, mul_zero, add_zero]
        · rw [dot_add_left, dot_smul_left]
          linarith [huStar_K.2 w hw, mul_nonneg ht_nn (hall_nn w hw)]
      have hbd := hMK (uStar + t • h) hu_mem c0
      have hhc : 0 < |h c0| := abs_pos.mpr hc0
      have h1 : |t * h c0| = |uStar c0| + MK + 1 := by
        rw [abs_mul, abs_of_nonneg ht_nn]; dsimp [t]; field_simp [hhc.ne']
      have h2 : |t * h c0| - |uStar c0| ≤ |uStar c0 + t * h c0| := by
        have := abs_sub_abs_le_abs_sub (t * h c0) (-uStar c0)
        rw [abs_neg, sub_neg_eq_add, add_comm] at this
        exact this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hbd
      linarith
    let step : (Fin (n + 1) → ℝ) → ℝ := fun w => dot uStar w / (-dot h w)
    obtain ⟨wStar, hwStar_mem, hwStar_min⟩ := NegW.exists_min_image step hNegW_ne
    have hwStar_Wi : wStar ∈ Wi := (Finset.mem_filter.mp hwStar_mem).1
    have hwStar_neg : dot h wStar < 0 := (Finset.mem_filter.mp hwStar_mem).2
    have hwStar_not_tight : wStar ∉ tightU uStar := by
      intro ht; linarith [hh_tight wStar ht]
    have hstep_pos : 0 < step wStar := by
      have hpos : 0 < dot uStar wStar :=
        lt_of_le_of_ne (huStar_K.2 wStar hwStar_Wi) (fun heq =>
          hwStar_not_tight (Finset.mem_filter.mpr ⟨hwStar_Wi, heq.symm⟩))
      exact div_pos hpos (by linarith)
    let u' := uStar + step wStar • h
    have hu'_K : u' ∈ K := by
      refine ⟨?_, fun w hw => ?_⟩
      · simp only [u', dot_add_left, dot_smul_left, huStar_K.1, hh_w0, mul_zero, add_zero]
      · simp only [u', dot_add_left, dot_smul_left]
        by_cases hwN : w ∈ NegW
        · have hwn : dot h w < 0 := (Finset.mem_filter.mp hwN).2
          have hmin := hwStar_min w hwN
          have hmul := mul_le_mul_of_nonneg_right hmin (by linarith : 0 ≤ -dot h w)
          rw [show step w = dot uStar w / (-dot h w) from rfl, div_mul_cancel₀ _ (by linarith : -dot h w ≠ 0)] at hmul
          linarith
        · have hwnn : 0 ≤ dot h w := by
            by_contra hlt; push Not at hlt
            exact hwN (Finset.mem_filter.mpr ⟨hw, hlt⟩)
          linarith [huStar_K.2 w hw, mul_nonneg hstep_pos.le hwnn]
    have hu'_m : dot u' a = mval := by
      have hge : mval ≤ dot u' a := humin_min hu'_K
      have hle : dot u' a ≤ mval := by
        simp only [u', dot_add_left, dot_smul_left, huStar_m]
        linarith [mul_nonpos_of_nonneg_of_nonpos hstep_pos.le hh_a]
      linarith
    have hsub_t : tightU uStar ⊆ tightU u' := by
      intro w hw
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, ?_⟩
      simp only [u', dot_add_left, dot_smul_left, (Finset.mem_filter.mp hw).2, hh_tight w hw,
        mul_zero, add_zero]
    have hwStar_in : wStar ∈ tightU u' := by
      refine Finset.mem_filter.mpr ⟨hwStar_Wi, ?_⟩
      simp only [u', dot_add_left, dot_smul_left, step]
      have hne : dot h wStar ≠ 0 := by linarith
      have : dot uStar wStar / (-dot h wStar) * dot h wStar = -dot uStar wStar := by
        field_simp [hne]
      linarith
    have hcard_lt : (tightU uStar).card < (tightU u').card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub_t, fun heq =>
        hwStar_not_tight (heq ▸ hwStar_in)⟩)
    have hu'_in_Cards : (tightU u').card ∈ Cards :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_filter_le _ _)),
        u', ⟨hu'_K, hu'_m⟩, rfl⟩
    have hle := hcmax_ge (tightU u').card hu'_in_Cards
    dsimp at hle
    omega
  -- Now finrank(span(tightU uStar)) = n!
  let Ut : Submodule ℝ (Fin (n + 1) → ℝ) := Submodule.span ℝ (tightU uStar : Set (Fin (n + 1) → ℝ))
  have hUt_rank : Module.finrank ℝ Ut = n := by
    have hsup : Ut ⊔ Submodule.span ℝ {w0} = ⊤ := by
      rw [← Submodule.span_union, Set.union_singleton]
      exact hspan_top
    have hge : n ≤ Module.finrank ℝ Ut := by
      have hadd := Submodule.finrank_sup_add_finrank_inf_eq Ut (Submodule.span ℝ {w0})
      rw [hsup, finrank_top] at hadd
      simp only [Module.finrank_pi, Fintype.card_fin] at hadd
      have h1 : Module.finrank ℝ (Submodule.span ℝ ({w0} : Set (Fin (n + 1) → ℝ))) ≤ 1 := by
        by_cases hw0 : w0 = 0
        · rw [hw0, Submodule.span_zero_singleton, finrank_bot]; exact Nat.zero_le 1
        · rw [finrank_span_singleton hw0]
      omega
    have hlt : Module.finrank ℝ Ut < n + 1 := by
      have hne_top : Ut ≠ ⊤ := by
        intro htop
        have hw0_in : w0 ∈ Ut := by rw [htop]; trivial
        have hdot0 : ∀ x ∈ Ut, dot uStar x = 0 := by
          intro x hx
          refine Submodule.span_induction ?_ (dot_zero_right uStar)
            (fun _ _ _ _ hx hy => by rw [dot_add_right, hx, hy, add_zero])
            (fun c _ _ hx => by rw [dot_smul_right, hx, mul_zero]) hx
          intro w hw; exact (Finset.mem_filter.mp hw).2
        have := hdot0 w0 hw0_in
        linarith [huStar_K.1]
      have hle : Module.finrank ℝ Ut ≤ n + 1 := by simpa using Submodule.finrank_le Ut
      have hne : Module.finrank ℝ Ut ≠ n + 1 := fun heq =>
        hne_top (Submodule.eq_top_of_finrank_eq (by simpa using heq))
      omega
    omega
  -- Extract an n-element linearly independent subset S_t ⊆ tightU uStar, then normalize signs into W_base!
  obtain ⟨S_set, hS_sub_set, hS_span, hS_li⟩ :=
    exists_linearIndependent ℝ (tightU uStar : Set (Fin (n + 1) → ℝ))
  have hS_fin : S_set.Finite := (tightU uStar).finite_toSet.subset hS_sub_set
  let S_t : Finset (Fin (n + 1) → ℝ) := hS_fin.toFinset
  have hSt_sub : S_t ⊆ tightU uStar := fun w hw => hS_sub_set (hS_fin.mem_toFinset.mp hw)
  have hSt_li : LinearIndependent ℝ (fun w : S_t => w.1) := by
    have hcoe : (S_t : Set (Fin (n + 1) → ℝ)) = S_set := hS_fin.coe_toFinset
    exact hS_li.comp (fun w : S_t => (⟨w.1, hcoe ▸ w.2⟩ : S_set))
      (fun w1 w2 h => Subtype.ext (congrArg (Subtype.val : S_set → _) h))
  have hSt_card : S_t.card = n := by
    have hfr := finrank_span_eq_card hSt_li
    have hrng : Set.range (fun w : S_t => w.1) = S_set := by
      ext x; simp [S_t, hS_fin.mem_toFinset]
    rw [hrng, hS_span] at hfr
    simpa [Ut, hUt_rank] using hfr.symm
  -- Normalize each w ∈ S_t to normW w ∈ W_base (either w or -w)
  let normW : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) := fun w => if w ∈ W_base then w else -w
  let S_norm : Finset (Fin (n + 1) → ℝ) := S_t.image normW
  have hSnorm_sub : S_norm ⊆ W_base := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨w, hw, rfl⟩
    have hwWi : w ∈ Wi := (Finset.mem_filter.mp (hSt_sub hw)).1
    dsimp [normW]
    split_ifs with hmem
    · exact hmem
    · exact (hWi_sub w hwWi).resolve_left hmem
  have hnormW_inj : Set.InjOn normW (S_t : Set (Fin (n + 1) → ℝ)) := by
    intro w1 hw1 w2 hw2 heq
    by_contra hne
    have hdep : (if w1 ∈ W_base then (1 : ℝ) else -1) • w1 +
        (-(if w2 ∈ W_base then (1 : ℝ) else -1)) • w2 = 0 := by
      dsimp [normW] at heq
      split_ifs at heq ⊢ <;> simp_all
    let c : S_t → ℝ := fun w =>
      if w.1 = w1 then (if w1 ∈ W_base then 1 else -1)
      else if w.1 = w2 then -(if w2 ∈ W_base then 1 else -1) else 0
    have hsum0 : ∑ w : S_t, c w • w.1 = 0 := by
      have h1 : (⟨w1, hw1⟩ : S_t) ≠ ⟨w2, hw2⟩ := fun h => hne (congrArg Subtype.val h)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨w1, hw1⟩ : S_t))]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h1.symm, Finset.mem_univ (⟨w2, hw2⟩ : S_t)⟩)]
      have hrest : ∑ w ∈ (Finset.univ.erase (⟨w1, hw1⟩ : S_t)).erase ⟨w2, hw2⟩, c w • w.1 = 0 := by
        refine Finset.sum_eq_zero fun w hw => ?_
        have hne2 : w.1 ≠ w2 := fun h => (Finset.mem_erase.mp hw).1 (Subtype.ext h)
        have hne1 : w.1 ≠ w1 := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1 (Subtype.ext h)
        simp [c, hne1, hne2]
      rw [hrest, add_zero]
      have hc1 : c ⟨w1, hw1⟩ = if w1 ∈ W_base then 1 else -1 := by simp [c]
      have hc2 : c ⟨w2, hw2⟩ = -(if w2 ∈ W_base then 1 else -1) := by simp [c, Ne.symm hne]
      rw [hc1, hc2]; exact hdep
    have hc0 := Fintype.linearIndependent_iff.mp hSt_li c hsum0 ⟨w1, hw1⟩
    simp only [c, if_pos rfl] at hc0
    split_ifs at hc0 <;> norm_num at hc0
  have hSnorm_card : S_norm.card = n := by
    rw [Finset.card_image_of_injOn hnormW_inj, hSt_card]
  have hSnorm_li : LinearIndependent ℝ (fun w : S_norm => w.1) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsum_t : ∑ w : S_t,
        (c ⟨normW w.1, Finset.mem_image.mpr ⟨w.1, w.2, rfl⟩⟩ * (if w.1 ∈ W_base then 1 else -1)) • w.1 = 0 := by
      have hbij : ∑ x : S_norm, c x • x.1 =
          ∑ w : S_t, c ⟨normW w.1, Finset.mem_image.mpr ⟨w.1, w.2, rfl⟩⟩ • normW w.1 := by
        symm
        refine Finset.sum_bij (fun w _ => ⟨normW w.1, Finset.mem_image.mpr ⟨w.1, w.2, rfl⟩⟩) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro w1 _ w2 _ h
          exact Subtype.ext (hnormW_inj w1.2 w2.2 (congrArg Subtype.val h))
        · intro x _
          rcases Finset.mem_image.mp x.2 with ⟨w, hw, hwx⟩
          exact ⟨⟨w, hw⟩, Finset.mem_univ _, Subtype.ext hwx⟩
        · intro _ _; rfl
      rw [← hc, hbij]
      refine Finset.sum_congr rfl fun w _ => ?_
      dsimp [normW]; split_ifs <;> simp
    have hall0 := Fintype.linearIndependent_iff.mp hSt_li _ hsum_t
    intro x
    rcases Finset.mem_image.mp x.2 with ⟨w, hw, hwx⟩
    have h0 := hall0 ⟨w, hw⟩
    have hsign_ne : (if w ∈ W_base then (1 : ℝ) else -1) ≠ 0 := by split_ifs <;> norm_num
    have hc0 : c ⟨normW w, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩ = 0 :=
      (mul_eq_zero.mp h0).resolve_right hsign_ne
    have hx_eq : x = ⟨normW w, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩ := Subtype.ext hwx.symm
    rw [hx_eq]
    exact hc0
  -- Get r ∈ R orthogonal to S_norm!
  obtain ⟨r, hrR, hr_ne, hr_orth⟩ := hR S_norm hSnorm_sub hSnorm_card hSnorm_li
  -- Both r and uStar lie in the 1D orthogonal complement of Ut! So uStar = λ • r for some λ ≠ 0!
  have hr_orth_St : ∀ w ∈ S_t, dot w r = 0 := by
    intro w hw
    have h := hr_orth (normW w) (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
    dsimp [normW] at h
    split_ifs at h
    · exact h
    · rw [dot_neg_left] at h; linarith
  have huStar_orth_St : ∀ w ∈ S_t, dot w uStar = 0 := fun w hw => by
    rw [dot_comm]; exact (Finset.mem_filter.mp (hSt_sub hw)).2
  -- Linear map x ↦ (dot (eSt k) x)_{k : Fin n} has 1D kernel!
  let eSt : Fin n ≃ S_t := (Fintype.equivFinOfCardEq (by simp [hSt_card])).symm
  let Lker : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun x k => dot (eSt k).1 x
      map_add' := fun x1 x2 => by ext k; exact dot_add_right _ x1 x2
      map_smul' := fun c x => by ext k; simp [dot_smul_right] }
  have hker_rank : Module.finrank ℝ (LinearMap.ker Lker) = 1 := by
    have hsurj : LinearMap.range Lker = ⊤ := by
      by_contra hne_top
      obtain ⟨c, hc_ne, hc_orth⟩ := exists_orth_ne_zero hne_top
      have hdep : ∑ w : S_t, c (eSt.symm w) • w.1 = 0 := by
        apply dot_self_eq_zero
        have hzero : ∀ x, dot (∑ w : S_t, c (eSt.symm w) • w.1) x = 0 := fun x => by
          rw [dot_sum_left]
          have hbij : ∑ w : S_t, dot (c (eSt.symm w) • w.1) x =
              ∑ k : Fin n, dot (c k • (eSt k).1) x := by
            symm
            refine Finset.sum_bij (fun k _ => eSt k) (fun _ _ => Finset.mem_univ _)
              (fun _ _ _ _ h => eSt.injective h)
              (fun w _ => ⟨eSt.symm w, Finset.mem_univ _, eSt.apply_symm_apply w⟩)
              (fun k _ => by simp)
          rw [hbij]
          have h0 := hc_orth (Lker x) (LinearMap.mem_range_self Lker x)
          have h1 : dot (Lker x) c = ∑ k : Fin n, c k * dot (eSt k).1 x := by
            simp only [dot, Lker, LinearMap.coe_mk, AddHom.coe_mk]
            exact Finset.sum_congr rfl fun k _ => mul_comm _ _
          simp_rw [dot_smul_left]
          rw [← h1, h0]
        exact hzero _
      have hall0 := Fintype.linearIndependent_iff.mp hSt_li (fun w => c (eSt.symm w)) hdep
      apply hc_ne
      ext k
      simpa using hall0 (eSt k)
    have hrk := LinearMap.finrank_range_add_finrank_ker Lker
    rw [hsurj, finrank_top] at hrk
    simp only [Module.finrank_pi, Fintype.card_fin] at hrk
    omega
  have hr_ker : r ∈ LinearMap.ker Lker := by ext k; exact hr_orth_St (eSt k).1 (eSt k).2
  have huStar_ker : uStar ∈ LinearMap.ker Lker := by ext k; exact huStar_orth_St (eSt k).1 (eSt k).2
  have hspan_r : Submodule.span ℝ ({(⟨r, hr_ker⟩ : LinearMap.ker Lker)} : Set (LinearMap.ker Lker)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hne : (⟨r, hr_ker⟩ : LinearMap.ker Lker) ≠ 0 := fun h => hr_ne (congrArg Subtype.val h)
    rw [finrank_span_singleton hne, hker_rank]
  have hu_in_span : (⟨uStar, huStar_ker⟩ : LinearMap.ker Lker) ∈ Submodule.span ℝ {⟨r, hr_ker⟩} := by
    rw [hspan_r]; trivial
  rw [Submodule.mem_span_singleton] at hu_in_span
  obtain ⟨lam, hlam⟩ := hu_in_span
  have huStar_eq : uStar = lam • r := (congrArg Subtype.val hlam).symm
  -- Since signMap R a = signMap R b, dot uStar a < 0 implies dot uStar b < 0!
  have hsame_sign : signOf (dot r a) = signOf (dot r b) := by
    have := congrFun hab r
    simpa [signMap, hrR] using this
  have huStar_b_neg : dot uStar b < 0 := by
    have ha_neg : lam * dot r a < 0 := by
      rw [← dot_smul_left, ← huStar_eq, huStar_m]; exact hmval_neg
    rw [huStar_eq, dot_smul_left]
    simp only [signOf] at hsame_sign
    rcases lt_trichotomy (dot r a) 0 with h1 | h1 | h1 <;>
      rcases lt_trichotomy (dot r b) 0 with h2 | h2 | h2
    · have hlam_pos : 0 < lam := by nlinarith
      nlinarith
    · exfalso; simp [not_lt_of_gt h1, h1, h2] at hsame_sign
    · exfalso; simp [not_lt_of_gt h1, h1, h2] at hsame_sign
    · rw [h1, mul_zero] at ha_neg; exact absurd ha_neg (lt_irrefl 0)
    · rw [h1, mul_zero] at ha_neg; exact absurd ha_neg (lt_irrefl 0)
    · rw [h1, mul_zero] at ha_neg; exact absurd ha_neg (lt_irrefl 0)
    · exfalso; simp [h1, h2, not_lt_of_gt h2] at hsame_sign
    · exfalso; simp [h1, h2] at hsame_sign
    · have hlam_neg : lam < 0 := by nlinarith
      nlinarith
  -- Perturb uStar by tiny ε • u1 (for u1 ∈ N) to get strict positivity on all Wi AND dot u b < 0!
  obtain ⟨u1, hu1⟩ := hN_ne
  let ε : ℝ := (-dot uStar b) / (2 * (|dot u1 b| + 1))
  have hε_pos : 0 < ε := div_pos (by linarith) (by linarith [abs_nonneg (dot u1 b)])
  refine ⟨uStar + ε • u1, fun w hw => ?_, ?_⟩
  · rw [dot_add_left, dot_smul_left]
    linarith [huStar_K.2 w hw, mul_pos hε_pos (hu1 w hw)]
  · rw [dot_add_left, dot_smul_left]
    have h1 : ε * dot u1 b ≤ ε * (|dot u1 b| + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [le_abs_self (dot u1 b)]) hε_pos.le
    have h2 : ε * (|dot u1 b| + 1) = (-dot uStar b) / 2 := by
      dsimp [ε]
      have hne : |dot u1 b| + 1 ≠ 0 := by linarith [abs_nonneg (dot u1 b)]
      field_simp [hne]
    linarith

/- ### Module 6: Balanced Alternating Partitions, Deterministic Clarkson-Shor, & Main Theorem -/

/-- Binomial ratio bound for Clarkson-Shor subsampling:
`s * m.choose s ≤ 3 * m * (m - t).choose (s - 1)` whenever `2 ≤ t`, `4 * t ≤ m`, `s = m / (2 * t)`. -/
private lemma choose_ratio_clarkson {m t s : ℕ} (ht : 2 ≤ t) (hmt : 4 * t ≤ m) (hs : s = m / (2 * t)) :
    s * m.choose s ≤ 3 * m * (m - t).choose (s - 1) := by
  have hs_ge2 : 2 ≤ s := by
    rw [hs]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hst2 : 2 * s * t ≤ m := by
    rw [hs]
    have := Nat.div_mul_le_self m (2 * t)
    linarith
  have hs_le_m4 : s ≤ m / 4 := by
    have : 4 * s ≤ m := by nlinarith
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith)
  have hts_le : 2 * (t + s) ≤ m := by omega
  have h1 : s * m.choose s = m * (m - 1).choose (s - 1) := by
    cases m with
    | zero => omega
    | succ m' =>
      cases s with
      | zero => omega
      | succ s' =>
        simp only [Nat.add_sub_cancel]
        exact succ_mul_choose_succ m' s'
  rw [h1, show 3 * m * (m - t).choose (s - 1) = m * (3 * (m - t).choose (s - 1)) by ring]
  refine Nat.mul_le_mul_left m ?_
  -- Prove (m - 1).choose (s - 1) ≤ 3 * (m - t).choose (s - 1) via descFactorial!
  suffices hdesc : (m - 1).descFactorial (s - 1) ≤ 3 * (m - t).descFactorial (s - 1) by
    have hfac_pos : 0 < (s - 1).factorial := Nat.factorial_pos _
    have hL := Nat.descFactorial_eq_factorial_mul_choose (m - 1) (s - 1)
    have hR := Nat.descFactorial_eq_factorial_mul_choose (m - t) (s - 1)
    nlinarith
  suffices hR : ((m - 1).descFactorial (s - 1) : ℝ) ≤ 3 * ((m - t).descFactorial (s - 1) : ℝ) by
    exact_mod_cast hR
  have hprod_eq : ∀ a k : ℕ, (a.descFactorial k : ℝ) = ∏ j ∈ Finset.range k, ((a - j : ℕ) : ℝ) := by
    intro a k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.descFactorial_succ, Nat.cast_mul, ih, Finset.prod_range_succ, mul_comm]
  rw [hprod_eq, hprod_eq]
  have hsR_pos : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr (by omega)
  have hterm : ∀ j ∈ Finset.range (s - 1),
      ((m - 1 - j : ℕ) : ℝ) ≤ (1 + 1 / (s : ℝ)) * ((m - t - j : ℕ) : ℝ) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hmtj : m / 2 ≤ m - t - j := by omega
    have hmtjR : (m : ℝ) / 2 ≤ ((m - t - j : ℕ) : ℝ) := by
      have : m ≤ 2 * (m - t - j) := by omega
      have hR' : (m : ℝ) ≤ 2 * ((m - t - j : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    have hdiff : ((m - 1 - j : ℕ) : ℝ) ≤ ((m - t - j : ℕ) : ℝ) + (t : ℝ) := by
      have : m - 1 - j ≤ (m - t - j) + t := by omega
      exact_mod_cast this
    have hts : (t : ℝ) ≤ (1 / (s : ℝ)) * ((m - t - j : ℕ) : ℝ) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hsR_pos]
      have h2st : 2 * (s : ℝ) * (t : ℝ) ≤ (m : ℝ) := by exact_mod_cast hst2
      nlinarith
    linarith
  calc ∏ j ∈ Finset.range (s - 1), ((m - 1 - j : ℕ) : ℝ)
      ≤ ∏ j ∈ Finset.range (s - 1), ((1 + 1 / (s : ℝ)) * ((m - t - j : ℕ) : ℝ)) :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) hterm
    _ = (1 + 1 / (s : ℝ)) ^ (s - 1) * ∏ j ∈ Finset.range (s - 1), ((m - t - j : ℕ) : ℝ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    _ ≤ 3 * ∏ j ∈ Finset.range (s - 1), ((m - t - j : ℕ) : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
        have hexp : 1 + 1 / (s : ℝ) ≤ Real.exp (1 / (s : ℝ)) := by
          linarith [Real.add_one_le_exp (1 / (s : ℝ))]
        calc (1 + 1 / (s : ℝ)) ^ (s - 1)
            ≤ (1 + 1 / (s : ℝ)) ^ s := by
              exact pow_le_pow_right₀ (by linarith [div_nonneg zero_le_one hsR_pos.le]) (Nat.sub_le s 1)
          _ ≤ (Real.exp (1 / (s : ℝ))) ^ s := pow_le_pow_left₀ (by positivity) hexp s
          _ = Real.exp ((s : ℝ) * (1 / (s : ℝ))) := (Real.exp_nat_mul _ s).symm
          _ = Real.exp 1 := by congr 1; field_simp [hsR_pos.ne']
          _ ≤ 3 := by linarith [Real.exp_one_lt_d9]

open Classical in
/-- Deterministic Clarkson-Shor subsampling bound for `t`-shallow grid tuples in `ℝ^n`:
the number of tuples `i : Fin n → Fin m` admitting `u : Fin n → ℝ` with at most `t - 1`
other indices `j ≠ i k` having `dot u (Q k j) ≥ dot u (Q k (i k))` for every `k`
is at most `4 * t * 36 ^ n * m ^ (n - 1)`. -/
private lemma shallow_tuples_le {n m t : ℕ} (hn : 1 ≤ n) (ht : 2 ≤ t) (hmt : 4 * t ≤ m)
    (Q : Fin n → Fin m → (Fin n → ℝ)) :
    (Finset.univ.filter (fun i : Fin n → Fin m =>
      ∃ u : Fin n → ℝ, ∀ k : Fin n,
        (Finset.univ.filter (fun j : Fin m => j ≠ i k ∧ dot u (Q k (i k)) ≤ dot u (Q k j))).card < t)).card ≤
      4 * t * 36 ^ n * m ^ (n - 1) := by
  classical
  set s := m / (2 * t)
  have hs_ge2 : 2 ≤ s := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hm_le_4ts : m ≤ 4 * t * s := by
    have hlt := Nat.lt_div_mul_add (a := m) (b := 2 * t) (by omega)
    dsimp [s] at *
    nlinarith
  let Shallow := Finset.univ.filter (fun i : Fin n → Fin m =>
    ∃ u : Fin n → ℝ, ∀ k : Fin n,
      (Finset.univ.filter (fun j : Fin m => j ≠ i k ∧ dot u (Q k (i k)) ≤ dot u (Q k j))).card < t)
  let Choices : Finset (Fin n → Finset (Fin m)) :=
    Fintype.piFinset fun _ : Fin n => (Finset.univ : Finset (Fin m)).powersetCard s
  let Good : Finset ((Fin n → Finset (Fin m)) × (Fin n → Fin m)) :=
    (Choices ×ˢ Finset.univ).filter fun p =>
      (∀ k : Fin n, p.2 k ∈ p.1 k) ∧
      ∃ u : Fin n → ℝ, ∀ k : Fin n, ∀ j ∈ p.1 k, j ≠ p.2 k → dot u (Q k j) < dot u (Q k (p.2 k))
  -- Upper bound on Good.card: sum over R ∈ Choices; each R gives at most 12^n * s^(n-1) strict vertices!
  have hGood_ub : Good.card ≤ m.choose s ^ n * (12 ^ n * s ^ (n - 1)) := by
    have hChoices_card : Choices.card = m.choose s ^ n := by
      simp [Choices, Fintype.card_piFinset]
    have hfiber : ∀ R ∈ Choices,
        (Finset.univ.filter fun i : Fin n → Fin m => (R, i) ∈ Good).card ≤ 12 ^ n * s ^ (n - 1) := by
      intro R hR
      have hRk_card : ∀ k : Fin n, (R k).card = s := fun k =>
        (Finset.mem_powersetCard.mp (Fintype.mem_piFinset.mp hR k)).2
      let eR : ∀ k : Fin n, Fin s ≃ (R k) := fun k => (Fintype.equivFinOfCardEq (by simp [hRk_card k])).symm
      let QR : Fin n → Fin s → (Fin n → ℝ) := fun k j => Q k (eR k j).1
      let mapI : (Fin n → Fin s) → (Fin n → Fin m) := fun i' k => (eR k (i' k)).1
      have hsub : (Finset.univ.filter fun i : Fin n → Fin m => (R, i) ∈ Good) ⊆
          (Finset.univ.filter (StrictVert QR)).image mapI := by
        intro i hi
        have hG := (Finset.mem_filter.mp hi).2
        have hmem_R : ∀ k, i k ∈ R k := (Finset.mem_filter.mp hG).2.1
        obtain ⟨u, hu⟩ := (Finset.mem_filter.mp hG).2.2
        let i' : Fin n → Fin s := fun k => (eR k).symm ⟨i k, hmem_R k⟩
        refine Finset.mem_image.mpr ⟨i', Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, fun k j hj => ?_⟩, ?_⟩
        · have hj_ne : (eR k j).1 ≠ i k := by
            intro heq
            apply hj
            have : eR k j = ⟨i k, hmem_R k⟩ := Subtype.ext heq
            simpa [i'] using congrArg (eR k).symm this
          have hi'_eq : (eR k (i' k)).1 = i k := by simp [i']
          simp only [QR, hi'_eq]
          exact hu k (eR k j).1 (eR k j).2 hj_ne
        · ext k; simp [mapI, i']
      calc (Finset.univ.filter fun i => (R, i) ∈ Good).card
          ≤ ((Finset.univ.filter (StrictVert QR)).image mapI).card := Finset.card_le_card hsub
        _ ≤ (Finset.univ.filter (StrictVert QR)).card := Finset.card_image_le
        _ ≤ 12 ^ n * s ^ (n - 1) := minkowski_vertices_le hn hs_ge2 le_rfl QR
    have hsum_eq : Good.card = ∑ R ∈ Choices, (Finset.univ.filter fun i => (R, i) ∈ Good).card := by
      have h1 : Good = Choices.biUnion fun R =>
          (Finset.univ.filter fun i => (R, i) ∈ Good).image fun i => (R, i) := by
        ext ⟨R, i⟩
        simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
          true_and, Prod.mk.injEq]
        constructor
        · intro hG
          exact ⟨R, (Finset.mem_product.mp (Finset.mem_filter.mp hG).1).1, i, hG, rfl, rfl⟩
        · rintro ⟨R', _, i', hG, rfl, rfl⟩; exact hG
      calc Good.card
          = (Choices.biUnion fun R => (Finset.univ.filter fun i => (R, i) ∈ Good).image fun i => (R, i)).card :=
            congrArg Finset.card h1
        _ = ∑ R ∈ Choices, ((Finset.univ.filter fun i => (R, i) ∈ Good).image fun i => (R, i)).card := by
            refine Finset.card_biUnion fun R1 _ R2 _ hne => ?_
            change Disjoint _ _
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            rcases Finset.mem_image.mp hx1 with ⟨_, _, rfl⟩
            rcases Finset.mem_image.mp hx2 with ⟨_, _, h⟩
            exact hne (congrArg Prod.fst h).symm
        _ = ∑ R ∈ Choices, (Finset.univ.filter fun i => (R, i) ∈ Good).card :=
            Finset.sum_congr rfl fun R _ => Finset.card_image_of_injective _ fun a b h => congrArg Prod.snd h
    rw [hsum_eq]
    calc ∑ R ∈ Choices, (Finset.univ.filter fun i => (R, i) ∈ Good).card
        ≤ ∑ _R ∈ Choices, (12 ^ n * s ^ (n - 1)) := Finset.sum_le_sum hfiber
      _ = Choices.card * (12 ^ n * s ^ (n - 1)) := by simp
      _ = m.choose s ^ n * (12 ^ n * s ^ (n - 1)) := by rw [hChoices_card]
  -- Lower bound on Good.card: sum over i ∈ Shallow; each i appears in at least (m - t).choose (s - 1) ^ n choices!
  have hGood_lb : Shallow.card * (m - t).choose (s - 1) ^ n ≤ Good.card := by
    have hfiber_i : ∀ i ∈ Shallow,
        (m - t).choose (s - 1) ^ n ≤ (Choices.filter fun R => (R, i) ∈ Good).card := by
      intro i hi
      obtain ⟨u, hu⟩ := (Finset.mem_filter.mp hi).2
      let Safe : Fin n → Finset (Fin m) := fun k =>
        Finset.univ.filter fun j : Fin m => j ≠ i k ∧ dot u (Q k j) < dot u (Q k (i k))
      have hSafe_card : ∀ k : Fin n, m - t ≤ (Safe k).card := by
        intro k
        let Bad := Finset.univ.filter fun j : Fin m => j ≠ i k ∧ dot u (Q k (i k)) ≤ dot u (Q k j)
        have hBad_lt : Bad.card < t := hu k
        have hdisj : Disjoint (insert (i k) Bad) (Safe k) := by
          rw [Finset.disjoint_left]
          intro j hj1 hj2
          have hjS := (Finset.mem_filter.mp hj2).2
          rcases Finset.mem_insert.mp hj1 with rfl | hjB
          · exact hjS.1 rfl
          · linarith [(Finset.mem_filter.mp hjB).2.2, hjS.2]
        have hunion : insert (i k) Bad ∪ Safe k = Finset.univ := by
          ext j
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ,
            true_and, iff_true, Bad, Safe]
          by_cases hji : j = i k
          · left; left; exact hji
          · by_cases hle : dot u (Q k (i k)) ≤ dot u (Q k j)
            · left; right; exact ⟨hji, hle⟩
            · right; exact ⟨hji, not_le.mp hle⟩
        have hsum := Finset.card_union_of_disjoint hdisj
        rw [hunion, Finset.card_univ, Fintype.card_fin] at hsum
        have hins : (insert (i k) Bad).card ≤ Bad.card + 1 := Finset.card_insert_le _ _
        omega
      let ValidChoices : Finset (Fin n → Finset (Fin m)) :=
        Fintype.piFinset fun k : Fin n =>
          ((Safe k).powersetCard (s - 1)).image (fun T => insert (i k) T)
      have hVC_sub : ValidChoices ⊆ Choices.filter fun R => (R, i) ∈ Good := by
        intro R hR
        have hRk : ∀ k, R k ∈ ((Safe k).powersetCard (s - 1)).image (fun T => insert (i k) T) :=
          Fintype.mem_piFinset.mp hR
        have hR_in_Choices : R ∈ Choices := by
          rw [Fintype.mem_piFinset]
          intro k
          rcases Finset.mem_image.mp (hRk k) with ⟨T, hT, hTeq⟩
          rw [← hTeq]
          have hT_sub := (Finset.mem_powersetCard.mp hT).1
          have hT_card := (Finset.mem_powersetCard.mp hT).2
          have hi_not_T : i k ∉ T := fun hm => (Finset.mem_filter.mp (hT_sub hm)).2.1 rfl
          refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
          rw [Finset.card_insert_of_notMem hi_not_T, hT_card]
          omega
        refine Finset.mem_filter.mpr ⟨hR_in_Choices, Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hR_in_Choices, Finset.mem_univ _⟩, fun k => ?_, u, fun k j hjR hjne => ?_⟩⟩
        · rcases Finset.mem_image.mp (hRk k) with ⟨T, _, hTeq⟩
          dsimp only
          rw [← hTeq]; exact Finset.mem_insert_self _ _
        · rcases Finset.mem_image.mp (hRk k) with ⟨T, hT, hTeq⟩
          dsimp only at hjR hjne ⊢
          rw [← hTeq] at hjR
          rcases Finset.mem_insert.mp hjR with rfl | hjT
          · exact (hjne rfl).elim
          · exact (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp hT).1 hjT)).2.2
      have hVC_card : (m - t).choose (s - 1) ^ n ≤ ValidChoices.card := by
        rw [Fintype.card_piFinset]
        calc (m - t).choose (s - 1) ^ n
            = ∏ _k : Fin n, (m - t).choose (s - 1) := by simp
          _ ≤ ∏ k : Fin n, (((Safe k).powersetCard (s - 1)).image (fun T => insert (i k) T)).card := by
              refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun k _ => ?_
              rw [Finset.card_image_of_injOn]
              · rw [Finset.card_powersetCard]
                exact Nat.choose_le_choose (s - 1) (hSafe_card k)
              · intro T1 hT1 T2 hT2 heq
                have h1 : i k ∉ T1 := fun hm => (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp hT1).1 hm)).2.1 rfl
                have h2 : i k ∉ T2 := fun hm => (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp hT2).1 hm)).2.1 rfl
                have := congrArg (fun S => S.erase (i k)) heq
                simpa [Finset.erase_insert h1, Finset.erase_insert h2] using this
      exact le_trans hVC_card (Finset.card_le_card hVC_sub)
    have hsum_sub : Shallow.biUnion (fun i => (Choices.filter fun R => (R, i) ∈ Good).image fun R => (R, i)) ⊆ Good := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨i, _, hxI⟩
      rcases Finset.mem_image.mp hxI with ⟨R, hR, rfl⟩
      exact (Finset.mem_filter.mp hR).2
    calc Shallow.card * (m - t).choose (s - 1) ^ n
        = ∑ _i ∈ Shallow, (m - t).choose (s - 1) ^ n := by simp
      _ ≤ ∑ i ∈ Shallow, (Choices.filter fun R => (R, i) ∈ Good).card := Finset.sum_le_sum hfiber_i
      _ = (Shallow.biUnion fun i => (Choices.filter fun R => (R, i) ∈ Good).image fun R => (R, i)).card := by
          rw [Finset.card_biUnion]
          · refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.card_image_of_injective]
            intro a b h; exact congrArg Prod.fst h
          · intro i1 _ i2 _ hne
            change Disjoint _ _
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            rcases Finset.mem_image.mp hx1 with ⟨_, _, rfl⟩
            rcases Finset.mem_image.mp hx2 with ⟨_, _, h⟩
            exact hne (congrArg Prod.snd h).symm
      _ ≤ Good.card := Finset.card_le_card hsum_sub
  -- Combine upper and lower bounds and apply choose_ratio_clarkson!
  have hcomb : Shallow.card * (m - t).choose (s - 1) ^ n ≤ m.choose s ^ n * (12 ^ n * s ^ (n - 1)) :=
    le_trans hGood_lb hGood_ub
  have hratio : (s * m.choose s) ^ n ≤ (3 * m * (m - t).choose (s - 1)) ^ n :=
    Nat.pow_le_pow_left (choose_ratio_clarkson ht hmt rfl) n
  have hsn : s ^ n = s * s ^ (n - 1) := by
    cases n with
    | zero => omega
    | succ k => simp [pow_succ, mul_comm]
  have hmul_s : Shallow.card * s * (s ^ (n - 1) * (m - t).choose (s - 1) ^ n) ≤
      (36 ^ n * m ^ n) * (s ^ (n - 1) * (m - t).choose (s - 1) ^ n) := by
    calc Shallow.card * s * (s ^ (n - 1) * (m - t).choose (s - 1) ^ n)
        = s ^ n * (Shallow.card * (m - t).choose (s - 1) ^ n) := by rw [hsn]; ring
      _ ≤ s ^ n * (m.choose s ^ n * (12 ^ n * s ^ (n - 1))) := Nat.mul_le_mul_left _ hcomb
      _ = (s * m.choose s) ^ n * (12 ^ n * s ^ (n - 1)) := by rw [Nat.mul_pow]; ring
      _ ≤ (3 * m * (m - t).choose (s - 1)) ^ n * (12 ^ n * s ^ (n - 1)) := Nat.mul_le_mul_right _ hratio
      _ = (36 ^ n * m ^ n) * (s ^ (n - 1) * (m - t).choose (s - 1) ^ n) := by
          rw [Nat.mul_pow, Nat.mul_pow]
          have h36 : (3 : ℕ) ^ n * 12 ^ n = 36 ^ n := by rw [← Nat.mul_pow]
          calc 3 ^ n * m ^ n * (m - t).choose (s - 1) ^ n * (12 ^ n * s ^ (n - 1))
              = (3 ^ n * 12 ^ n) * m ^ n * (s ^ (n - 1) * (m - t).choose (s - 1) ^ n) := by ring
            _ = (36 ^ n * m ^ n) * (s ^ (n - 1) * (m - t).choose (s - 1) ^ n) := by rw [h36]
  have hpos_cancel : 0 < s ^ (n - 1) * (m - t).choose (s - 1) ^ n := by
    have h1 : 0 < s ^ (n - 1) := pow_pos (by omega) _
    have hst_le : s + t ≤ m := by
      have hdiv := Nat.div_mul_le_self m (2 * t)
      have h2st : 2 * s * t ≤ m := by dsimp [s]; linarith
      nlinarith
    have h2 : 0 < (m - t).choose (s - 1) := Nat.choose_pos (by omega)
    exact Nat.mul_pos h1 (pow_pos h2 n)
  have hSh_s : Shallow.card * s ≤ 36 ^ n * m ^ n := Nat.le_of_mul_le_mul_right hmul_s hpos_cancel
  have hmn : m ^ n = m * m ^ (n - 1) := by
    cases n with
    | zero => omega
    | succ k => simp [pow_succ, mul_comm]
  have hSh_s2 : Shallow.card * s ≤ (4 * t * 36 ^ n * m ^ (n - 1)) * s := by
    calc Shallow.card * s ≤ 36 ^ n * (m * m ^ (n - 1)) := hmn ▸ hSh_s
      _ ≤ 36 ^ n * ((4 * t * s) * m ^ (n - 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hm_le_4ts)
      _ = (4 * t * 36 ^ n * m ^ (n - 1)) * s := by ring
  exact Nat.le_of_mul_le_mul_right hSh_s2 (by omega)

/-- Existence of a balanced partition `E ⊆ Fin m` (`|E| = m / 2`) for any `X : Fin m → ℝ^{n+1}`
such that for EVERY `u : Fin (n+1) → ℝ`, fewer than `t` elements of `E` strictly beat all of `Eᶜ`
in direction `u` (provided `2 ∣ m`, `t ≤ m / 2`, and `(2 * m^2 + 1)^{n+1} < 2^t`). -/
private lemma exists_balanced_partition {n m t : ℕ} (hm_even : 2 ∣ m) (ht_le : t ≤ m / 2)
    (hbound : (2 * m ^ 2 + 1) ^ (n + 1) < 2 ^ t)
    (X : Fin m → (Fin (n + 1) → ℝ)) :
    ∃ E : Finset (Fin m), E.card = m / 2 ∧
      ∀ u : Fin (n + 1) → ℝ,
        (E.filter (fun a => ∀ b : Fin m, b ∉ E → dot u (X b) < dot u (X a))).card < t := by
  classical
  -- Step 1: Collect all pairwise differences W_X = { X a - X b | a, b : Fin m } (|W_X| ≤ m^2)
  let W_X : Finset (Fin (n + 1) → ℝ) :=
    (Finset.univ : Finset (Fin m × Fin m)).image fun p => X p.1 - X p.2
  have hWX_card : W_X.card ≤ m ^ 2 := by
    calc W_X.card ≤ (Finset.univ : Finset (Fin m × Fin m)).card := Finset.card_image_le
      _ = m ^ 2 := by simp [sq]
  -- By Module 3, signMap W_X u takes at most (2 * m^2 + 1)^(n + 1) values!
  obtain ⟨Signs, hSigns_mem, hSigns_card⟩ := card_sign_patterns_le (⊤ : Submodule ℝ (Fin (n + 1) → ℝ)) W_X
  have hSigns_le : Signs.card ≤ (2 * m ^ 2 + 1) ^ (n + 1) := by
    have hfr : Module.finrank ℝ (⊤ : Submodule ℝ (Fin (n + 1) → ℝ)) = n + 1 := by simp
    rw [hfr] at hSigns_card
    calc Signs.card
        ≤ ∑ j ∈ Finset.range (n + 1 + 1), 2 ^ j * W_X.card.choose j := hSigns_card
      _ ≤ (2 * W_X.card + 1) ^ (n + 1) := sum_two_pow_mul_choose_le W_X.card (n + 1)
      _ ≤ (2 * m ^ 2 + 1) ^ (n + 1) := by gcongr
  -- For each u, define the total order a ≺_u b iff dot u (X a) < dot u (X b) ∨ (dot u (X a) = dot u (X b) ∧ a < b)
  -- and define topSet u = the t largest elements of Fin m under ≺_u!
  let ltU : (Fin (n + 1) → ℝ) → Fin m → Fin m → Prop := fun u a b =>
    dot u (X a) < dot u (X b) ∨ (dot u (X a) = dot u (X b) ∧ a.1 < b.1)
  let topSet : (Fin (n + 1) → ℝ) → Finset (Fin m) := fun u =>
    Finset.univ.filter fun a : Fin m => (Finset.univ.filter fun b => ltU u a b).card < t
  have htop_card : ∀ u, (topSet u).card = t := by
    intro u
    -- ltU u is a strict total order on Fin m, so its rank function r(a) = #{b | ltU u a b} is a bijection Fin m → Fin m!
    let rk : Fin m → ℕ := fun a => (Finset.univ.filter fun b => ltU u a b).card
    have hlt_trans : ∀ a b c, ltU u a b → ltU u b c → ltU u a c := by
      intro a b c h1 h2
      rcases h1 with h1 | ⟨h1e, h1i⟩ <;> rcases h2 with h2 | ⟨h2e, h2i⟩
      · left; linarith
      · left; linarith
      · left; linarith
      · right; exact ⟨by linarith, by omega⟩
    have hlt_tri : ∀ a b : Fin m, a ≠ b → ltU u a b ∨ ltU u b a := by
      intro a b hne
      rcases lt_trichotomy (dot u (X a)) (dot u (X b)) with h | h | h
      · left; left; exact h
      · rcases lt_or_gt_of_ne (fun heq => hne (Fin.ext heq)) with h1 | h1
        · left; right; exact ⟨h, h1⟩
        · right; right; exact ⟨h.symm, h1⟩
      · right; left; exact h
    have hrk_lt : ∀ a b, ltU u a b → rk b < rk a := by
      intro a b hab
      refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
      · intro c hc
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_trans a b c hab (Finset.mem_filter.mp hc).2⟩
      · intro heq
        have hb_in : b ∈ Finset.univ.filter fun c => ltU u a c :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩
        rw [← heq] at hb_in
        have hbb := (Finset.mem_filter.mp hb_in).2
        rcases hbb with h | ⟨_, h⟩ <;> linarith
    have hrk_inj : Function.Injective rk := by
      intro a b heq
      by_contra hne
      rcases hlt_tri a b hne with h | h
      · have := hrk_lt a b h; omega
      · have := hrk_lt b a h; omega
    have hrk_lt_m : ∀ a : Fin m, rk a < m := by
      intro a
      have hne : a ∉ Finset.univ.filter fun b => ltU u a b := by
        intro hm
        rcases (Finset.mem_filter.mp hm).2 with h | ⟨_, h⟩ <;> linarith
      have hss : (Finset.univ.filter fun b => ltU u a b) ⊂ Finset.univ :=
        Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, fun heq => hne (by rw [heq]; exact Finset.mem_univ a)⟩
      simpa using Finset.card_lt_card hss
    let rkFin : Fin m → Fin m := fun a => ⟨rk a, hrk_lt_m a⟩
    have hrkFin_inj : Function.Injective rkFin := fun a b h => hrk_inj (congrArg Fin.val h)
    have hrkFin_bij : Function.Bijective rkFin := Finite.injective_iff_bijective.mp hrkFin_inj
    have hcard_eq : (topSet u).card = (Finset.univ.filter fun r : Fin m => r.1 < t).card := by
      refine Finset.card_bij (fun a _ => rkFin a) ?_ ?_ ?_
      · intro a ha; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
      · intro a1 _ a2 _ h; exact hrkFin_inj h
      · intro r hr
        obtain ⟨a, rfl⟩ := hrkFin_bij.2 r
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2⟩, rfl⟩
    rw [hcard_eq]
    have hrange_eq : (Finset.univ.filter fun r : Fin m => r.1 < t).card = (Finset.range t).card := by
      refine Finset.card_bij (fun r _ => r.1) ?_ ?_ ?_
      · intro r hr; exact Finset.mem_range.mpr (Finset.mem_filter.mp hr).2
      · intro r1 _ r2 _ h; exact Fin.ext h
      · intro k hk
        have hkm : k < m := by
          have := Finset.mem_range.mp hk
          omega
        exact ⟨⟨k, hkm⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hk⟩, rfl⟩
    rw [hrange_eq, Finset.card_range]
  -- topSet u depends ONLY on signMap W_X u!
  have htop_det : ∀ u u' : Fin (n + 1) → ℝ, signMap W_X u = signMap W_X u' → topSet u = topSet u' := by
    intro u u' hsign
    have hlt_iff : ∀ a b : Fin m, ltU u a b ↔ ltU u' a b := by
      intro a b
      have hmem : X a - X b ∈ W_X := Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩
      have hs := congrFun hsign (X a - X b)
      simp only [signMap, if_pos hmem, dot_sub_left, signOf] at hs
      have hcomm : ∀ z, dot (X a) z - dot (X b) z = dot z (X a) - dot z (X b) := fun z => by
        rw [dot_comm (X a) z, dot_comm (X b) z]
      rw [hcomm u, hcomm u'] at hs
      simp only [ltU]
      rcases lt_trichotomy (dot u (X a)) (dot u (X b)) with h1 | h1 | h1 <;>
        rcases lt_trichotomy (dot u' (X a)) (dot u' (X b)) with h2 | h2 | h2
      · simp [h1, h2]
      · exfalso; have : dot u (X a) - dot u (X b) < 0 := by linarith
        have : dot u' (X a) - dot u' (X b) = 0 := by linarith
        simp_all [not_lt_of_gt]
      · exfalso; have : dot u (X a) - dot u (X b) < 0 := by linarith
        have : 0 < dot u' (X a) - dot u' (X b) := by linarith
        simp_all [not_lt_of_gt]
      · exfalso; have : dot u (X a) - dot u (X b) = 0 := by linarith
        have : dot u' (X a) - dot u' (X b) < 0 := by linarith
        simp_all [not_lt_of_gt]
      · simp [h1, h2]
      · exfalso; have : dot u (X a) - dot u (X b) = 0 := by linarith
        have : 0 < dot u' (X a) - dot u' (X b) := by linarith
        simp_all
      · exfalso; have : 0 < dot u (X a) - dot u (X b) := by linarith
        have : dot u' (X a) - dot u' (X b) < 0 := by linarith
        simp_all [not_lt_of_gt]
      · exfalso; have : 0 < dot u (X a) - dot u (X b) := by linarith
        have : dot u' (X a) - dot u' (X b) = 0 := by linarith
        simp_all
      · simp [not_lt_of_gt h1, ne_of_gt h1, not_lt_of_gt h2, ne_of_gt h2]
    ext a
    simp only [topSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have : (Finset.univ.filter fun b => ltU u a b) = (Finset.univ.filter fun b => ltU u' a b) := by
      ext b; simp [hlt_iff a b]
    rw [this]
  -- Collect all distinct topSets in a Finset TopSets with TopSets.card ≤ (2 * m^2 + 1)^(n+1)!
  let TopSets : Finset (Finset (Fin m)) :=
    (Signs.filter fun g => ∃ u, signMap W_X u = g).attach.image fun g =>
      topSet (Finset.mem_filter.mp g.2).2.choose
  have hTop_mem : ∀ u, topSet u ∈ TopSets := by
    intro u
    have hg : signMap W_X u ∈ Signs.filter fun g => ∃ u', signMap W_X u' = g :=
      Finset.mem_filter.mpr ⟨hSigns_mem u trivial, u, rfl⟩
    refine Finset.mem_image.mpr ⟨⟨signMap W_X u, hg⟩, Finset.mem_attach _ _, ?_⟩
    exact htop_det _ u (Finset.mem_filter.mp hg).2.choose_spec
  have hTop_card_le : TopSets.card ≤ (2 * m ^ 2 + 1) ^ (n + 1) := by
    calc TopSets.card ≤ (Signs.filter fun g => ∃ u, signMap W_X u = g).attach.card := Finset.card_image_le
      _ = (Signs.filter fun g => ∃ u, signMap W_X u = g).card := Finset.card_attach
      _ ≤ Signs.card := Finset.card_filter_le _ _
      _ ≤ (2 * m ^ 2 + 1) ^ (n + 1) := hSigns_le
  -- Every T ∈ TopSets has T.card = t, so at most (m - t).choose (m/2 - t) subsets E of size m/2 contain T!
  let Half : Finset (Finset (Fin m)) := (Finset.univ : Finset (Fin m)).powersetCard (m / 2)
  let Bad : Finset (Finset (Fin m)) := TopSets.biUnion fun T => Half.filter fun E => T ⊆ E
  have hchoose_half : 2 ^ t * (m - t).choose (m / 2 - t) ≤ m.choose (m / 2) := by
    obtain ⟨q, rfl⟩ := hm_even
    have hq : 2 * q / 2 = q := Nat.mul_div_right q (by norm_num)
    rw [hq] at ht_le ⊢
    exact two_pow_mul_choose_half q t ht_le
  have hBad_lt : Bad.card < Half.card := by
    have hHalf_card : Half.card = m.choose (m / 2) := by simp [Half]
    have hHalf_pos : 0 < m.choose (m / 2) := Nat.choose_pos (Nat.div_le_self m 2)
    have hper_T : ∀ T ∈ TopSets, (Half.filter fun E => T ⊆ E).card ≤ (m - t).choose (m / 2 - t) := by
      intro T hT
      have hT_card : T.card = t := by
        rcases Finset.mem_image.mp hT with ⟨g, _, rfl⟩
        exact htop_card _
      have hbij : (Half.filter fun E => T ⊆ E).card =
          ((Finset.univ \ T).powersetCard (m / 2 - t)).card := by
        refine Finset.card_bij (fun E _ => E \ T) ?_ ?_ ?_
        · intro E hE
          have hEH := (Finset.mem_filter.mp hE).1
          have hTE := (Finset.mem_filter.mp hE).2
          have hE_card := (Finset.mem_powersetCard.mp hEH).2
          refine Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl T), ?_⟩
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hTE, hE_card, hT_card]
        · intro E1 hE1 E2 hE2 heq
          have h1 := (Finset.mem_filter.mp hE1).2
          have h2 := (Finset.mem_filter.mp hE2).2
          rw [← Finset.sdiff_union_of_subset h1, ← Finset.sdiff_union_of_subset h2, heq]
        · intro S hS
          have hSsub := (Finset.mem_powersetCard.mp hS).1
          have hScard := (Finset.mem_powersetCard.mp hS).2
          have hdisj : Disjoint S T := Finset.disjoint_of_subset_left hSsub Finset.sdiff_disjoint
          refine ⟨S ∪ T, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩,
            Finset.subset_union_right⟩, ?_⟩
          · rw [Finset.card_union_of_disjoint hdisj, hScard, hT_card]; omega
          · exact Finset.union_sdiff_cancel_right hdisj
      rw [hbij, Finset.card_powersetCard, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ T),
        Finset.card_univ, Fintype.card_fin, hT_card]
    have hBad_le : Bad.card ≤ TopSets.card * (m - t).choose (m / 2 - t) := by
      calc Bad.card ≤ ∑ T ∈ TopSets, (Half.filter fun E => T ⊆ E).card := Finset.card_biUnion_le
        _ ≤ ∑ _T ∈ TopSets, (m - t).choose (m / 2 - t) := Finset.sum_le_sum hper_T
        _ = TopSets.card * (m - t).choose (m / 2 - t) := by simp
    have hmul : 2 ^ t * Bad.card < 2 ^ t * Half.card := by
      rw [hHalf_card]
      calc 2 ^ t * Bad.card
          ≤ 2 ^ t * (TopSets.card * (m - t).choose (m / 2 - t)) := Nat.mul_le_mul_left _ hBad_le
        _ = TopSets.card * (2 ^ t * (m - t).choose (m / 2 - t)) := by ring
        _ ≤ TopSets.card * m.choose (m / 2) := Nat.mul_le_mul_left _ hchoose_half
        _ < 2 ^ t * m.choose (m / 2) :=
            Nat.mul_lt_mul_of_pos_right (lt_of_le_of_lt hTop_card_le hbound) hHalf_pos
    exact Nat.lt_of_mul_lt_mul_left hmul
  -- Pick E ∈ Half \ Bad!
  have hne_sdiff : (Half \ Bad).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hsub : Half ⊆ Bad := Finset.sdiff_eq_empty_iff_subset.mp hempty
    have := Finset.card_le_card hsub
    omega
  obtain ⟨E, hE⟩ := hne_sdiff
  have hE_half := (Finset.mem_sdiff.mp hE).1
  have hE_not_bad := (Finset.mem_sdiff.mp hE).2
  refine ⟨E, (Finset.mem_powersetCard.mp hE_half).2, fun u => ?_⟩
  by_contra hge
  push Not at hge
  -- If ≥ t elements of E strictly beat all of Eᶜ in direction u, then topSet u ⊆ E, contradicting E ∉ Bad!
  have hsub_top : topSet u ⊆ E := by
    intro b hb
    by_contra hbE
    have hcount_lt : (Finset.univ.filter fun a => ltU u b a).card < t := (Finset.mem_filter.mp hb).2
    have hsub_lt : E.filter (fun a => ∀ c : Fin m, c ∉ E → dot u (X c) < dot u (X a)) ⊆
        Finset.univ.filter fun a => ltU u b a := by
      intro a ha
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, .inl ?_⟩
      exact (Finset.mem_filter.mp ha).2 b hbE
    have := Finset.card_le_card hsub_lt
    omega
  apply hE_not_bad
  exact Finset.mem_biUnion.mpr ⟨topSet u, hTop_mem u, Finset.mem_filter.mpr ⟨hE_half, hsub_top⟩⟩

private lemma hasAddVCNDimAtMost_65536_pow (n : ℕ) (hn : 1 ≤ n)
    (C : Set (Fin (n + 1) → ℝ)) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C n (65536 ^ n) := by
  classical
  set m := 65536 ^ n
  intro x_raw y_raw hxy_raw
  set t := 36 * n * (n + 1)
  have hm_even : 2 ∣ m := by
    cases n with
    | zero => omega
    | succ k => dsimp [m]; rw [pow_succ]; exact dvd_mul_of_dvd_right (by norm_num) _
  have hm_ge2 : 2 ≤ m := by
    have : 65536 ^ 1 ≤ 65536 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have ht_ge2 : 2 ≤ t := by dsimp [t]; nlinarith
  have hmt : 4 * t ≤ m := by
    have h1 : 4 * t = 144 * n * (n + 1) := by dsimp [t]; ring
    rw [h1]
    exact four_mul_t_le n hn
  have hpart_bound : (2 * m ^ 2 + 1) ^ (n + 1) < 2 ^ t := by
    have h1 : 2 * m ^ 2 + 1 ≤ 3 * m ^ 2 := by
      have : 1 ≤ m ^ 2 := Nat.one_le_pow 2 m (by omega)
      omega
    have h2 : 3 * m ^ 2 < 2 ^ (34 * n) := by
      have hm2 : m ^ 2 = 2 ^ (32 * n) := by
        dsimp [m]; rw [show (65536 : ℕ) = 2 ^ 16 by norm_num, ← pow_mul, ← pow_mul]; ring_nf
      have h3 : 3 < 2 ^ (2 * n) := by
        have : 2 ^ 2 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      rw [hm2, show 34 * n = 2 * n + 32 * n by omega, pow_add]
      exact Nat.mul_lt_mul_of_pos_right h3 (pow_pos (by norm_num) _)
    calc (2 * m ^ 2 + 1) ^ (n + 1)
        ≤ (3 * m ^ 2) ^ (n + 1) := Nat.pow_le_pow_left h1 (n + 1)
      _ < (2 ^ (34 * n)) ^ (n + 1) := Nat.pow_lt_pow_left h2 (Nat.succ_ne_zero n)
      _ = 2 ^ (34 * n * (n + 1)) := (pow_mul 2 (34 * n) (n + 1)).symm
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by dsimp [t]; nlinarith)
  -- Restrict to Fin m
  let x : Fin n → Fin m → (Fin (n + 1) → ℝ) := fun k j => x_raw k j.castSucc
  let liftIdx : (Fin n → Fin m) → (Fin n → Fin (m + 1)) := fun i k => (i k).castSucc
  have hlift_inj : Function.Injective liftIdx := fun i1 i2 h =>
    funext fun k => Fin.castSucc_injective m (congrFun h k)
  let y : Set (Fin n → Fin m) → (Fin (n + 1) → ℝ) := fun s => y_raw (liftIdx '' s)
  let p : (Fin n → Fin m) → (Fin (n + 1) → ℝ) := fun i => ∑ k : Fin n, x k (i k)
  have hxy : ∀ (i : Fin n → Fin m) (s : Set (Fin n → Fin m)), y s + p i ∈ C ↔ i ∈ s := by
    intro i s
    have := hxy_raw (liftIdx i) (liftIdx '' s)
    rw [hlift_inj.mem_set_image] at this
    exact this
  -- Step 1: Every grid tuple i is a strict extreme point of conv(G)
  have hall_sv : ∀ i : Fin n → Fin m, StrictVert x i := by
    intro i
    let s : Set (Fin n → Fin m) := { r | r ≠ i }
    have hi_not : y s + p i ∉ C := fun hm => (hxy i s).1 hm rfl
    let F : Finset (Fin (n + 1) → ℝ) :=
      (Finset.univ.filter fun r => r ≠ i).image fun r => y s + p r
    have hF_C : ∀ q ∈ F, q ∈ C := by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
      exact (hxy r s).2 (Finset.mem_filter.mp hr).2
    obtain ⟨u, hu⟩ := strict_separate_finset hC hi_not hF_C
    refine ⟨u, fun k j hj => ?_⟩
    let r := Function.update i k j
    have hr_ne : r ≠ i := fun heq => hj (by simpa [r] using congrFun heq k)
    have hlt := hu (y s + p r) (Finset.mem_image.mpr
      ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr_ne⟩, rfl⟩)
    simp only [dot_add_right] at hlt
    have hp_diff : p i - p r = x k (i k) - x k j := by
      simp only [p]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
      have hrest : ∑ k' ∈ Finset.univ.erase k, x k' (r k') =
          ∑ k' ∈ Finset.univ.erase k, x k' (i k') :=
        Finset.sum_congr rfl fun k' hk' => by simp [r, (Finset.mem_erase.mp hk').1]
      rw [hrest]
      simp only [r, Function.update_self]
      abel
    have hdot_diff : dot u (p i) - dot u (p r) = dot u (x k (i k)) - dot u (x k j) := by
      rw [← dot_sub_right, hp_diff, dot_sub_right]
    linarith
  -- Step 2: Pick a balanced alternating partition E k ⊆ Fin m (|E k| = m / 2) for each k : Fin n!
  have hex_E : ∀ k : Fin n, ∃ E : Finset (Fin m), E.card = m / 2 ∧
      ∀ u : Fin (n + 1) → ℝ,
        (E.filter (fun a => ∀ b : Fin m, b ∉ E → dot u (x k b) < dot u (x k a))).card < t :=
    fun k => exists_balanced_partition hm_even (by omega) hpart_bound (x k)
  choose E hE_card hE_shallow using hex_E
  let O : Fin n → Finset (Fin m) := fun k => Finset.univ \ E k
  have hO_card : ∀ k : Fin n, (O k).card = m / 2 := by
    intro k
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, hE_card k]
    obtain ⟨q, hq⟩ := hm_even
    omega
  have hm_half_ge2 : 2 ≤ m / 2 := by omega
  -- Step 3: Span of differences within O = { x k b - x k b0 | k, b ∈ O k } is ALL of ℝ^{n+1}!
  have hO_ne : ∀ k : Fin n, (O k).Nonempty := fun k =>
    Finset.card_pos.mp (by rw [hO_card k]; omega)
  let b0 : Fin n → Fin m := fun k => (hO_ne k).choose
  have hb0_mem : ∀ k : Fin n, b0 k ∈ O k := fun k => (hO_ne k).choose_spec
  let W_O : Submodule ℝ (Fin (n + 1) → ℝ) :=
    Submodule.span ℝ { v | ∃ (k : Fin n) (b : Fin m), b ∈ O k ∧ x k b - x k (b0 k) = v }
  have hWO_top : W_O = ⊤ := by
    by_contra hne_top
    have hle_n : Module.finrank ℝ W_O ≤ n := by
      have hle : Module.finrank ℝ W_O ≤ n + 1 := by simpa using Submodule.finrank_le W_O
      have hne : Module.finrank ℝ W_O ≠ n + 1 := fun heq =>
        hne_top (Submodule.eq_top_of_finrank_eq (by simpa using heq))
      omega
    let BW := Module.finBasis ℝ W_O
    let eO : ∀ k : Fin n, Fin (m / 2) ≃ (O k) := fun k =>
      (Fintype.equivFinOfCardEq (by simp [hO_card k])).symm
    let QO : Fin n → Fin (m / 2) → (Fin (Module.finrank ℝ W_O) → ℝ) := fun k j =>
      BW.equivFun ⟨x k (eO k j).1 - x k (b0 k), Submodule.subset_span ⟨k, (eO k j).1, (eO k j).2, rfl⟩⟩
    have hQO_all : ∀ i' : Fin n → Fin (m / 2), StrictVert QO i' := by
      intro i'
      let i : Fin n → Fin m := fun k => (eO k (i' k)).1
      obtain ⟨u, hu⟩ := hall_sv i
      let f : (Fin (Module.finrank ℝ W_O) → ℝ) →ₗ[ℝ] ℝ :=
        { toFun := fun v => dot u (BW.equivFun.symm v).1
          map_add' := fun v1 v2 => by simp [map_add, dot_add_right]
          map_smul' := fun c v => by simp [map_smul, dot_smul_right] }
      obtain ⟨u', hu'⟩ := dot_linear_rep f
      refine ⟨u', fun k j hj => ?_⟩
      rw [← hu' (QO k j), ← hu' (QO k (i' k))]
      simp only [f, QO, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_apply_apply, dot_sub_right]
      have hne : (eO k j).1 ≠ i k := fun heq => hj ((eO k).injective (Subtype.ext heq))
      linarith [hu k (eO k j).1 hne]
    have hcard_eq : (Finset.univ.filter (StrictVert QO)).card = (m / 2) ^ n := by
      rw [Finset.filter_true_of_mem fun i' _ => hQO_all i']; simp
    have hle_mv := minkowski_vertices_le hn hm_half_ge2 hle_n QO
    rw [hcard_eq] at hle_mv
    have hmn : (m / 2) ^ n = (m / 2) * (m / 2) ^ (n - 1) := by
      cases n with
      | zero => omega
      | succ k => simp [pow_succ, mul_comm]
    have hlt_12 : 12 ^ n < m / 2 := by
      have h2 : m / 2 = 32768 * 65536 ^ (n - 1) := by
        cases n with
        | zero => omega
        | succ k =>
          simp only [m, Nat.add_sub_cancel, pow_succ]
          have : 65536 ^ k * 65536 = 2 * (32768 * 65536 ^ k) := by ring
          rw [this, Nat.mul_div_right _ (by norm_num)]
      rw [h2]
      cases n with
      | zero => omega
      | succ k =>
        simp only [Nat.add_sub_cancel, pow_succ]
        have hle12 : 12 ^ k ≤ 65536 ^ k := Nat.pow_le_pow_left (by norm_num) k
        have hpos6 : 0 < 65536 ^ k := pow_pos (by norm_num) k
        nlinarith
    have hpos : 0 < (m / 2) ^ (n - 1) := pow_pos (by omega) _
    rw [hmn] at hle_mv
    have := Nat.mul_lt_mul_of_pos_right hlt_12 hpos
    omega
  -- Step 4: Build W_base and ray set R (|R| ≤ (n * m^2)^n)
  let W_base : Finset (Fin (n + 1) → ℝ) :=
    (Finset.univ : Finset (Fin n × Fin m × Fin m)).image fun q => x q.1 q.2.1 - x q.1 q.2.2
  have hW_base_card : W_base.card ≤ n * m ^ 2 := by
    calc W_base.card ≤ (Finset.univ : Finset (Fin n × Fin m × Fin m)).card := Finset.card_image_le
      _ = n * m ^ 2 := by simp [sq]
  let LinSubs : Finset (Finset (Fin (n + 1) → ℝ)) :=
    (W_base.powersetCard n).filter fun S => LinearIndependent ℝ (fun w : S => w.1)
  have hex_ray : ∀ S ∈ LinSubs, ∃ r : Fin (n + 1) → ℝ, r ≠ 0 ∧ ∀ w ∈ S, dot w r = 0 := by
    intro S hS
    have hcardS : S.card = n := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).2
    have hU_ne : Submodule.span ℝ (S : Set (Fin (n + 1) → ℝ)) ≠ ⊤ := by
      intro htop
      have hle : Module.finrank ℝ (Submodule.span ℝ (S : Set (Fin (n + 1) → ℝ))) ≤
          (S : Set (Fin (n + 1) → ℝ)).toFinset.card := finrank_span_le_card _
      have htoF : (S : Set (Fin (n + 1) → ℝ)).toFinset = S := by ext w; simp
      rw [htop, finrank_top, htoF] at hle
      simp only [Module.finrank_pi, Fintype.card_fin, hcardS] at hle
      omega
    obtain ⟨r, hr_ne, hr_orth⟩ := exists_orth_ne_zero hU_ne
    exact ⟨r, hr_ne, fun w hw => hr_orth w (Submodule.subset_span hw)⟩
  let R : Finset (Fin (n + 1) → ℝ) := LinSubs.attach.image fun S => (hex_ray S.1 S.2).choose
  have hR_card : R.card ≤ (n * m ^ 2) ^ n := by
    calc R.card ≤ LinSubs.attach.card := Finset.card_image_le
      _ = LinSubs.card := Finset.card_attach
      _ ≤ (W_base.powersetCard n).card := Finset.card_filter_le _ _
      _ = W_base.card.choose n := Finset.card_powersetCard n W_base
      _ ≤ W_base.card ^ n := choose_le_pow W_base.card n
      _ ≤ (n * m ^ 2) ^ n := Nat.pow_le_pow_left hW_base_card n
  have hR_spec : ∀ S : Finset (Fin (n + 1) → ℝ),
      S ⊆ W_base → S.card = n → LinearIndependent ℝ (fun w : S => w.1) →
      ∃ r ∈ R, r ≠ 0 ∧ ∀ w ∈ S, dot w r = 0 := by
    intro S hsub hcard hli
    have hS_in : S ∈ LinSubs :=
      Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩, hli⟩
    exact ⟨(hex_ray S hS_in).choose, Finset.mem_image.mpr ⟨⟨S, hS_in⟩, Finset.mem_attach _ _, rfl⟩,
      (hex_ray S hS_in).choose_spec⟩
  -- Step 5: Product set A = E 0 × ⋯ × E (n - 1) (|A| = (m / 2) ^ n), cones K_i, and I⁻(v), I⁺(v)
  let A : Finset (Fin n → Fin m) := Fintype.piFinset E
  have hA_card : A.card = (m / 2) ^ n := by
    simp [A, Fintype.card_piFinset, hE_card]
  let inK : (Fin n → Fin m) → (Fin (n + 1) → ℝ) → Prop := fun i u =>
    ∀ k : Fin n, ∀ b ∈ O k, dot u (x k b) < dot u (x k (i k))
  let Iminus : (Fin (n + 1) → ℝ) → Finset (Fin n → Fin m) := fun v =>
    A.filter fun i => ∃ u, inK i u ∧ dot u v < 0
  let Iplus : (Fin (n + 1) → ℝ) → Finset (Fin n → Fin m) := fun v =>
    A.filter fun i => ∃ w, inK i w ∧ 0 < dot w v
  -- Step 6: signMap R v determines Iminus v and Iplus v!
  have hsign_det : ∀ v v' : Fin (n + 1) → ℝ, signMap R v = signMap R v' →
      Iminus v = Iminus v' ∧ Iplus v = Iplus v' := by
    intro v v' hsign
    have h_for_i : ∀ i ∈ A,
        ((∃ u, inK i u ∧ dot u v < 0) ↔ (∃ u, inK i u ∧ dot u v' < 0)) ∧
        ((∃ w, inK i w ∧ 0 < dot w v) ↔ (∃ w, inK i w ∧ 0 < dot w v')) := by
      intro i hiA
      let Wi : Finset (Fin (n + 1) → ℝ) :=
        ((Finset.univ : Finset (Fin n × Fin m)).filter fun q => q.2 ∈ O q.1).image
          fun q => x q.1 (i q.1) - x q.1 q.2
      have hWi_sub : ∀ w ∈ Wi, w ∈ W_base ∨ -w ∈ W_base := by
        intro w hw
        rcases Finset.mem_image.mp hw with ⟨⟨k, b⟩, _, rfl⟩
        left; exact Finset.mem_image.mpr ⟨(k, i k, b), Finset.mem_univ _, rfl⟩
      have hWi_span : Submodule.span ℝ (Wi : Set (Fin (n + 1) → ℝ)) = ⊤ := by
        rw [← hWO_top]
        refine le_antisymm (le_top.trans (le_of_eq hWO_top.symm)) ?_
        rw [Submodule.span_le]
        rintro _ ⟨k, b, hbO, rfl⟩
        have hmem_b : x k (i k) - x k b ∈ Submodule.span ℝ (Wi : Set (Fin (n + 1) → ℝ)) :=
          Submodule.subset_span (Finset.mem_image.mpr ⟨(k, b),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbO⟩, rfl⟩)
        have hmem_b0 : x k (i k) - x k (b0 k) ∈ Submodule.span ℝ (Wi : Set (Fin (n + 1) → ℝ)) :=
          Submodule.subset_span (Finset.mem_image.mpr ⟨(k, b0 k),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb0_mem k⟩, rfl⟩)
        have heq : x k b - x k (b0 k) = (x k (i k) - x k (b0 k)) - (x k (i k) - x k b) := by abel
        rw [heq]
        exact Submodule.sub_mem _ hmem_b0 hmem_b
      have hinK_iff : ∀ u, inK i u ↔ ∀ w ∈ Wi, 0 < dot u w := by
        intro u
        constructor
        · intro hu w hw
          rcases Finset.mem_image.mp hw with ⟨⟨k, b⟩, hkb, rfl⟩
          rw [dot_sub_right]
          linarith [hu k b (Finset.mem_filter.mp hkb).2]
        · intro hu k b hbO
          have hmem : x k (i k) - x k b ∈ Wi :=
            Finset.mem_image.mpr ⟨(k, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbO⟩, rfl⟩
          have := hu _ hmem
          rw [dot_sub_right] at this
          linarith
      have hN_ne : ∃ u, ∀ w ∈ Wi, 0 < dot u w := by
        obtain ⟨u, hu⟩ := hall_sv i
        refine ⟨u, (hinK_iff u).mp fun k b hbO => hu k b ?_⟩
        intro heq
        have hiE : i k ∈ E k := Fintype.mem_piFinset.mp hiA k
        rw [heq] at hbO
        exact (Finset.mem_sdiff.mp hbO).2 hiE
      have hneg := cone_neg_determined_by_rays W_base R hR_spec Wi hWi_sub hWi_span hN_ne hsign
      have hsign_neg : signMap R (-v) = signMap R (-v') := by
        ext r
        by_cases hr : r ∈ R
        · have h0 := congrFun hsign r
          simp only [signMap, if_pos hr, dot_neg_right, signOf] at h0 ⊢
          rcases lt_trichotomy (dot r v) 0 with h1 | h1 | h1 <;>
            rcases lt_trichotomy (dot r v') 0 with h2 | h2 | h2 <;>
            simp_all [not_lt_of_gt]
        · simp [signMap, hr]
      have hpos := cone_neg_determined_by_rays W_base R hR_spec Wi hWi_sub hWi_span hN_ne hsign_neg
      refine ⟨?_, ?_⟩
      · simpa only [hinK_iff] using hneg
      · have hrew : ∀ (z : Fin (n + 1) → ℝ),
            (∃ w, inK i w ∧ 0 < dot w z) ↔ (∃ w, (∀ a ∈ Wi, 0 < dot w a) ∧ dot w (-z) < 0) := by
          intro z
          constructor <;> (rintro ⟨w, hw1, hw2⟩; refine ⟨w, ?_, ?_⟩)
          · exact (hinK_iff w).mp hw1
          · rw [dot_neg_right]; linarith
          · exact (hinK_iff w).mpr hw1
          · rw [dot_neg_right] at hw2; linarith
        rw [hrew v, hrew v']; exact hpos
    refine ⟨?_, ?_⟩
    · ext i; simp only [Iminus, Finset.mem_filter]; exact and_congr_right fun hiA => (h_for_i i hiA).1
    · ext i; simp only [Iplus, Finset.mem_filter]; exact and_congr_right fun hiA => (h_for_i i hiA).2
  -- Step 7: For every v ≠ 0, (Iminus v ∩ Iplus v).card ≤ 4 * t * 36^n * m^(n - 1) via shallow_tuples_le!
  have hinter_le : ∀ v : Fin (n + 1) → ℝ, v ≠ 0 →
      (Iminus v ∩ Iplus v).card ≤ 4 * t * 36 ^ n * m ^ (n - 1) := by
    intro v hv
    let fv : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun u => dot u v
        map_add' := fun u1 u2 => dot_add_left u1 u2 v
        map_smul' := fun c u => by simp [dot_smul_left] }
    let Vorth : Submodule ℝ (Fin (n + 1) → ℝ) := LinearMap.ker fv
    have hVorth_rank : Module.finrank ℝ Vorth = n := by
      have hrange_top : LinearMap.range fv = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        have hle : Module.finrank ℝ (LinearMap.range fv) ≤ 1 := by
          simpa using Submodule.finrank_le (LinearMap.range fv)
        have hne_bot : LinearMap.range fv ≠ ⊥ := by
          intro hbot
          have hmem : fv v ∈ (⊥ : Submodule ℝ ℝ) := hbot ▸ LinearMap.mem_range_self fv v
          rw [Submodule.mem_bot] at hmem
          exact hv (dot_self_eq_zero hmem)
        have hpos : 0 < Module.finrank ℝ (LinearMap.range fv) :=
          Nat.pos_of_ne_zero fun h0 => hne_bot (Submodule.finrank_eq_zero.mp h0)
        simp; omega
      have hrk := LinearMap.finrank_range_add_finrank_ker fv
      rw [hrange_top, finrank_top] at hrk
      simp only [Module.finrank_self, Module.finrank_pi, Fintype.card_fin] at hrk
      change Module.finrank ℝ (LinearMap.ker fv) = n
      omega
    let BV : Module.Basis (Fin n) ℝ Vorth :=
      (Module.finBasis ℝ Vorth).reindex (finCongr hVorth_rank)
    let Qv : Fin n → Fin m → (Fin n → ℝ) := fun k j c => dot (BV c).1 (x k j)
    have hsub_sh : Iminus v ∩ Iplus v ⊆ Finset.univ.filter (fun i : Fin n → Fin m =>
        ∃ u : Fin n → ℝ, ∀ k : Fin n,
          (Finset.univ.filter (fun j : Fin m => j ≠ i k ∧ dot u (Qv k (i k)) ≤ dot u (Qv k j))).card < t) := by
      intro i hi
      rw [Finset.mem_inter] at hi
      obtain ⟨u, huK, huv⟩ := (Finset.mem_filter.mp hi.1).2
      obtain ⟨w, hwK, hwv⟩ := (Finset.mem_filter.mp hi.2).2
      let u0 : Fin (n + 1) → ℝ := (dot w v) • u + (-dot u v) • w
      have hu0_orth : u0 ∈ Vorth := by
        change dot u0 v = 0; simp only [u0, dot_add_left, dot_smul_left]; ring
      have hu0_K : inK i u0 := by
        intro k b hbO
        simp only [u0, dot_add_left, dot_smul_left]
        have h1 := mul_lt_mul_of_pos_left (huK k b hbO) hwv
        have h2 := mul_lt_mul_of_pos_left (hwK k b hbO) (by linarith : 0 < -dot u v)
        linarith
      let coeffs : Fin n → ℝ := BV.repr ⟨u0, hu0_orth⟩
      have hdot_eq : ∀ z : Fin (n + 1) → ℝ, dot coeffs (fun c => dot (BV c).1 z) = dot u0 z := by
        intro z
        have hrep : (⟨u0, hu0_orth⟩ : Vorth) = ∑ c : Fin n, coeffs c • BV c :=
          (BV.sum_repr ⟨u0, hu0_orth⟩).symm
        have hu0_sum : u0 = ∑ c : Fin n, coeffs c • (BV c).1 := by
          calc u0 = (⟨u0, hu0_orth⟩ : Vorth).1 := rfl
            _ = (∑ c : Fin n, coeffs c • BV c).1 := congrArg Subtype.val hrep
            _ = ∑ c : Fin n, coeffs c • (BV c).1 := by rw [AddSubmonoidClass.coe_finsetSum]; rfl
        rw [hu0_sum, dot_sum_left]
        simp only [dot_smul_left]
        rfl
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, coeffs, fun k => ?_⟩
      -- Every j with dot u0 (x k (i k)) ≤ dot u0 (x k j) strictly beats all of O k, so must be in E k!
      have hsub_E : Finset.univ.filter (fun j : Fin m => j ≠ i k ∧ dot coeffs (Qv k (i k)) ≤ dot coeffs (Qv k j)) ⊆
          (E k).filter (fun a => ∀ b : Fin m, b ∉ E k → dot u0 (x k b) < dot u0 (x k a)) := by
        intro j hj
        have hle := (Finset.mem_filter.mp hj).2.2
        change dot coeffs (fun c => dot (BV c).1 (x k (i k))) ≤
          dot coeffs (fun c => dot (BV c).1 (x k j)) at hle
        rw [hdot_eq, hdot_eq] at hle
        have hj_beats : ∀ b : Fin m, b ∉ E k → dot u0 (x k b) < dot u0 (x k j) := by
          intro b hbE
          have hbO : b ∈ O k := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hbE⟩
          linarith [hu0_K k b hbO]
        have hjE : j ∈ E k := by
          by_contra hj_not
          exact lt_irrefl _ (hj_beats j hj_not)
        exact Finset.mem_filter.mpr ⟨hjE, hj_beats⟩
      exact lt_of_le_of_lt (Finset.card_le_card hsub_E) (hE_shallow k u0)
    exact le_trans (Finset.card_le_card hsub_sh) (shallow_tuples_le hn ht_ge2 hmt Qv)
  -- Step 8: Master Dual Separation for every subset B ⊆ A!
  have hmaster : ∀ B : Finset (Fin n → Fin m), B ⊆ A →
      ∃ v : Fin (n + 1) → ℝ, v ≠ 0 ∧ B ⊆ Iminus v ∧ A \ B ⊆ Iplus v := by
    intro B hBA
    let SB : Set (Fin n → Fin m) := { r | r ∉ B }
    let TB : Set (Fin n → Fin m) := { r | r ∉ A \ B }
    let v : Fin (n + 1) → ℝ := y TB - y SB
    have hv_ne : v ≠ 0 := by
      intro h0
      have hy_eq : y TB = y SB := sub_eq_zero.mp h0
      have hA_ne : A.Nonempty := Finset.card_pos.mp (by rw [hA_card]; exact pow_pos (by omega) n)
      obtain ⟨i0, hi0⟩ := hA_ne
      by_cases hB0 : i0 ∈ B
      · have h1 : y SB + p i0 ∉ C := fun hm => (hxy i0 SB).1 hm hB0
        have h2 : y TB + p i0 ∈ C := (hxy i0 TB).2 (by simp [TB, hB0])
        rw [hy_eq] at h2; exact h1 h2
      · have h1 : y SB + p i0 ∈ C := (hxy i0 SB).2 hB0
        have h2 : y TB + p i0 ∉ C := fun hm => (hxy i0 TB).1 hm (Finset.mem_sdiff.mpr ⟨hi0, hB0⟩)
        rw [hy_eq] at h2; exact h2 h1
    have hupd_notA : ∀ (i : Fin n → Fin m) (k : Fin n) (b : Fin m), b ∈ O k →
        Function.update i k b ∉ A := by
      intro i k b hbO hm
      have hbE : Function.update i k b k ∈ E k := Fintype.mem_piFinset.mp hm k
      simp only [Function.update_self] at hbE
      exact (Finset.mem_sdiff.mp hbO).2 hbE
    refine ⟨v, hv_ne, ?_, ?_⟩
    · intro i hiB
      have hiA : i ∈ A := hBA hiB
      have hi_not : y SB + p i ∉ C := fun hm => (hxy i SB).1 hm hiB
      let F : Finset (Fin (n + 1) → ℝ) :=
        insert (y TB + p i) ((Finset.univ.filter fun r => r ∉ B).image fun r => y SB + p r)
      have hF_C : ∀ q ∈ F, q ∈ C := by
        intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq'
        · exact (hxy i TB).2 (by simp [TB, hiB])
        · rcases Finset.mem_image.mp hq' with ⟨r, hr, rfl⟩
          exact (hxy r SB).2 (Finset.mem_filter.mp hr).2
      obtain ⟨u, hu⟩ := strict_separate_finset hC hi_not hF_C
      refine Finset.mem_filter.mpr ⟨hiA, u, fun k b hbO => ?_, ?_⟩
      · let r := Function.update i k b
        have hr_notB : r ∉ B := fun hm => hupd_notA i k b hbO (hBA hm)
        have hlt := hu (y SB + p r) (Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr_notB⟩, rfl⟩))
        simp only [dot_add_right] at hlt
        have hp_diff : p i - p r = x k (i k) - x k b := by
          simp only [p]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
              ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
          have hrest : ∑ k' ∈ Finset.univ.erase k, x k' (r k') =
              ∑ k' ∈ Finset.univ.erase k, x k' (i k') :=
            Finset.sum_congr rfl fun k' hk' => by simp [r, (Finset.mem_erase.mp hk').1]
          rw [hrest]
          simp only [r, Function.update_self]
          abel
        have hdot_diff : dot u (p i) - dot u (p r) = dot u (x k (i k)) - dot u (x k b) := by
          rw [← dot_sub_right, hp_diff, dot_sub_right]
        linarith
      · have hlt := hu (y TB + p i) (Finset.mem_insert_self _ _)
        simp only [dot_add_right, v, dot_sub_right] at hlt ⊢
        linarith
    · intro j hjAB
      have hjA : j ∈ A := (Finset.mem_sdiff.mp hjAB).1
      have hj_notB : j ∉ B := (Finset.mem_sdiff.mp hjAB).2
      have hj_not : y TB + p j ∉ C := fun hm => (hxy j TB).1 hm hjAB
      let F : Finset (Fin (n + 1) → ℝ) :=
        insert (y SB + p j) ((Finset.univ.filter fun r => r ∉ A \ B).image fun r => y TB + p r)
      have hF_C : ∀ q ∈ F, q ∈ C := by
        intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq'
        · exact (hxy j SB).2 hj_notB
        · rcases Finset.mem_image.mp hq' with ⟨r, hr, rfl⟩
          exact (hxy r TB).2 (Finset.mem_filter.mp hr).2
      obtain ⟨w, hw⟩ := strict_separate_finset hC hj_not hF_C
      refine Finset.mem_filter.mpr ⟨hjA, w, fun k b hbO => ?_, ?_⟩
      · let r := Function.update j k b
        have hr_notAB : r ∉ A \ B := fun hm => hupd_notA j k b hbO (Finset.mem_sdiff.mp hm).1
        have hlt := hw (y TB + p r) (Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr_notAB⟩, rfl⟩))
        simp only [dot_add_right] at hlt
        have hp_diff : p j - p r = x k (j k) - x k b := by
          simp only [p]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
              ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
          have hrest : ∑ k' ∈ Finset.univ.erase k, x k' (r k') =
              ∑ k' ∈ Finset.univ.erase k, x k' (j k') :=
            Finset.sum_congr rfl fun k' hk' => by simp [r, (Finset.mem_erase.mp hk').1]
          rw [hrest]
          simp only [r, Function.update_self]
          abel
        have hdot_diff : dot w (p j) - dot w (p r) = dot w (x k (j k)) - dot w (x k b) := by
          rw [← dot_sub_right, hp_diff, dot_sub_right]
        linarith
      · have hlt := hw (y SB + p j) (Finset.mem_insert_self _ _)
        simp only [dot_add_right, v, dot_sub_right] at hlt ⊢
        linarith
  -- Step 9: Pigeonhole cardinality contradiction!
  obtain ⟨SignSet, hSignSet_mem, hSignSet_card⟩ :=
    card_sign_patterns_le (⊤ : Submodule ℝ (Fin (n + 1) → ℝ)) R
  have hSignSet_le : SignSet.card ≤ (2 * (n * m ^ 2) ^ n + 1) ^ (n + 1) := by
    have hfr : Module.finrank ℝ (⊤ : Submodule ℝ (Fin (n + 1) → ℝ)) = n + 1 := by simp
    rw [hfr] at hSignSet_card
    calc SignSet.card
        ≤ ∑ j ∈ Finset.range (n + 1 + 1), 2 ^ j * R.card.choose j := hSignSet_card
      _ ≤ (2 * R.card + 1) ^ (n + 1) := sum_two_pow_mul_choose_le R.card (n + 1)
      _ ≤ (2 * (n * m ^ 2) ^ n + 1) ^ (n + 1) := by gcongr
  let vOf : ∀ B : Finset (Fin n → Fin m), B ∈ A.powerset → Fin (n + 1) → ℝ :=
    fun B hB => (hmaster B (Finset.mem_powerset.mp hB)).choose
  have hvOf_spec : ∀ (B : Finset (Fin n → Fin m)) (hB : B ∈ A.powerset),
      vOf B hB ≠ 0 ∧ B ⊆ Iminus (vOf B hB) ∧ A \ B ⊆ Iplus (vOf B hB) :=
    fun B hB => (hmaster B (Finset.mem_powerset.mp hB)).choose_spec
  -- Group B ∈ A.powerset by s = signMap R (vOf B hB) ∈ SignSet
  have hfiber_B : ∀ s ∈ SignSet,
      (A.powerset.attach.filter fun B => signMap R (vOf B.1 B.2) = s).card ≤
        2 ^ (4 * t * 36 ^ n * m ^ (n - 1)) := by
    intro s _
    by_cases hempty : (A.powerset.attach.filter fun B => signMap R (vOf B.1 B.2) = s).Nonempty
    · obtain ⟨B0, hB0⟩ := hempty
      set v0 := vOf B0.1 B0.2
      have hv0_ne : v0 ≠ 0 := (hvOf_spec B0.1 B0.2).1
      have hs0 : signMap R v0 = s := (Finset.mem_filter.mp hB0).2
      have hcard_inter : (Iminus v0 ∩ Iplus v0).card ≤ 4 * t * 36 ^ n * m ^ (n - 1) :=
        hinter_le v0 hv0_ne
      have hinj : Set.InjOn (fun B : { x // x ∈ A.powerset } => B.1 ∩ (Iminus v0 ∩ Iplus v0))
          ((A.powerset.attach.filter fun B => signMap R (vOf B.1 B.2) = s) : Set _) := by
        intro B1 hB1 B2 hB2 heq
        ext : 1
        have hs1 : signMap R (vOf B1.1 B1.2) = signMap R v0 := by
          rw [(Finset.mem_filter.mp hB1).2, hs0]
        have hs2 : signMap R (vOf B2.1 B2.2) = signMap R v0 := by
          rw [(Finset.mem_filter.mp hB2).2, hs0]
        have hdet1 := hsign_det _ _ hs1
        have hdet2 := hsign_det _ _ hs2
        have hB1_rec : B1.1 = (A \ Iplus v0) ∪ (B1.1 ∩ (Iminus v0 ∩ Iplus v0)) := by
          ext i
          simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
          constructor
          · intro hi
            have hiA : i ∈ A := Finset.mem_powerset.mp B1.2 hi
            have hiM : i ∈ Iminus v0 := hdet1.1 ▸ (hvOf_spec B1.1 B1.2).2.1 hi
            by_cases hiP : i ∈ Iplus v0
            · right; exact ⟨hi, hiM, hiP⟩
            · left; exact ⟨hiA, hiP⟩
          · rintro (⟨hiA, hi_notP⟩ | ⟨hi, _, _⟩)
            · by_contra hi_notB
              have hiP : i ∈ Iplus v0 :=
                hdet1.2 ▸ (hvOf_spec B1.1 B1.2).2.2 (Finset.mem_sdiff.mpr ⟨hiA, hi_notB⟩)
              exact hi_notP hiP
            · exact hi
        have hB2_rec : B2.1 = (A \ Iplus v0) ∪ (B2.1 ∩ (Iminus v0 ∩ Iplus v0)) := by
          ext i
          simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
          constructor
          · intro hi
            have hiA : i ∈ A := Finset.mem_powerset.mp B2.2 hi
            have hiM : i ∈ Iminus v0 := hdet2.1 ▸ (hvOf_spec B2.1 B2.2).2.1 hi
            by_cases hiP : i ∈ Iplus v0
            · right; exact ⟨hi, hiM, hiP⟩
            · left; exact ⟨hiA, hiP⟩
          · rintro (⟨hiA, hi_notP⟩ | ⟨hi, _, _⟩)
            · by_contra hi_notB
              have hiP : i ∈ Iplus v0 :=
                hdet2.2 ▸ (hvOf_spec B2.1 B2.2).2.2 (Finset.mem_sdiff.mpr ⟨hiA, hi_notB⟩)
              exact hi_notP hiP
            · exact hi
        dsimp only at heq
        rw [hB1_rec, hB2_rec, heq]
      calc (A.powerset.attach.filter fun B => signMap R (vOf B.1 B.2) = s).card
          ≤ (Iminus v0 ∩ Iplus v0).powerset.card := by
            refine Finset.card_le_card_of_injOn (fun B => B.1 ∩ (Iminus v0 ∩ Iplus v0)) ?_ hinj
            intro B _; exact Finset.mem_powerset.mpr Finset.inter_subset_right
        _ = 2 ^ (Iminus v0 ∩ Iplus v0).card := Finset.card_powerset _
        _ ≤ 2 ^ (4 * t * 36 ^ n * m ^ (n - 1)) := Nat.pow_le_pow_right (by norm_num) hcard_inter
    · rw [Finset.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
  have hpow_le : 2 ^ ((m / 2) ^ n) ≤
      (2 * (n * m ^ 2) ^ n + 1) ^ (n + 1) * 2 ^ (4 * t * 36 ^ n * m ^ (n - 1)) := by
    have hcov : A.powerset.attach ⊆
        SignSet.biUnion fun s => A.powerset.attach.filter fun B => signMap R (vOf B.1 B.2) = s := by
      intro B _
      exact Finset.mem_biUnion.mpr ⟨signMap R (vOf B.1 B.2), hSignSet_mem _ trivial,
        Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, rfl⟩⟩
    calc 2 ^ ((m / 2) ^ n) = 2 ^ A.card := by rw [hA_card]
      _ = A.powerset.card := (Finset.card_powerset A).symm
      _ = A.powerset.attach.card := (Finset.card_attach).symm
      _ ≤ (SignSet.biUnion fun s => A.powerset.attach.filter fun B => signMap R (vOf B.1 B.2) = s).card :=
          Finset.card_le_card hcov
      _ ≤ ∑ s ∈ SignSet, (A.powerset.attach.filter fun B => signMap R (vOf B.1 B.2) = s).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _s ∈ SignSet, 2 ^ (4 * t * 36 ^ n * m ^ (n - 1)) := Finset.sum_le_sum hfiber_B
      _ = SignSet.card * 2 ^ (4 * t * 36 ^ n * m ^ (n - 1)) := by simp
      _ ≤ (2 * (n * m ^ 2) ^ n + 1) ^ (n + 1) * 2 ^ (4 * t * 36 ^ n * m ^ (n - 1)) :=
          Nat.mul_le_mul_right _ hSignSet_le
  exact absurd hpow_le (not_le.mpr (final_exp_ineq n hn))

end VCDimConvexExpProof

theorem OMA.solution :
    type_of% @VCDimConvex.exists_exponential_bound_hasAddVCNDimAtMost_n_of_convex_rn_add_one :=
  ⟨65536, by norm_num, fun n hn C hC => VCDimConvexExpProof.hasAddVCNDimAtMost_65536_pow n hn C hC⟩

