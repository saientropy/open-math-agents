import FormalConjectures.ErdosProblems.«252»

/-!
Unconditional proof of `Erdos252.erdos_252`: for every `k ≥ 1`,
`∑' n, σ k n / n!` is irrational.

Proof overview:
1. If `α = ∑' n, σ k n / n! = a / b` is rational (`b > 0`), then for every `n ≥ b` the scaled
   factorial tail `T n = ∑' j, σ k (n + 1 + j) * n! / (n + 1 + j)!` is an integer.
2. Letting `ρ k m = σ k m / m^k`, pairing divisors above and below `√m` yields `ρ k m ≤ 2 √m`,
   so truncating `T n` at `h = k + 1` leaves an `O_k(n^{-3/2})` tail. Euclidean division of
   `X (X + h)^k` by `∏_{j=1}^h (X + j)` in `ℝ[X]` decomposes each rational weight into a
   polynomial `P_{k,h}(n)` of degree `≤ k - h`, a `c_{k,h} / n` term (`P_{k,k+1} = 0`,
   `c_{k,k+1} = 1`), and an `O_k(n^{-2})` remainder.
3. On the `k`-dimensional grid `e ∈ {0, ..., k+1}^k` with `M = (k+2)^k`, `D = M!`,
   `p(e) = 1 + D (k(k+1)M + ∑ (k+2)^{s-1} e_s)`, and `t(e) = ∑ s D (k+2)^{s-1} e_s`:
   - all `p(e)` are pairwise coprime and coprime to `1, ..., k+1`,
   - for each `1 ≤ h ≤ k`, the shift `r_h(e) = h p(e) - t(e)` is independent of `e_h`, while
     `p(e)^k P_{k,h}((N - t(e))/p(e))` has degree `≤ k` in `e_h`, so the order-`(k+1)`
     alternating binomial weights `w(e) = ∏ (-1)^{e_s} C(k+1, e_s)` annihilate all `h ≤ k`
     polynomial parts identically,
   - the maximal shift `r_* = r_{k+1}(k+1, ..., k+1)` is strictly greater than all other shifts
     and has coefficient `c_* = p(e^*)^{k+1} > 0`.
4. Along the CRT progression `N ≡ t(e) (mod p(e)^2)`, `∑_e w(e) σ_k(p(e)) T((N - t(e))/p(e))`
   is an integer tending to `0`, hence eventually `0`, forcing `R(N) = ∑_i c_i ρ_k(N + r_i) → 0`.
5. Choosing a fresh prime `L` and comparing two sub-progressions mod `L Q` (one where `L` divides
   no `N + r_i`, one where `L` divides only `N + r_*`) via elementary Cesàro averages contradicts
   `R(N) → 0`.
-/

namespace Erdos252Proof

open scoped Nat ArithmeticFunction.sigma BigOperators
open Filter Polynomial

/- ### Part 1: Elementary bounds on `σ_k` and `ρ_k` -/

private noncomputable def rho (k m : ℕ) : ℝ :=
  if m = 0 then 0 else (σ k m : ℝ) / (m : ℝ) ^ k

private lemma rho_eq_sum_divisors {k m : ℕ} (hm : 0 < m) :
    rho k m = ∑ d ∈ m.divisors, (1 : ℝ) / (d : ℝ) ^ k := by
  unfold rho
  simp only [hm.ne', ↓reduceIte, ArithmeticFunction.sigma_apply, Nat.cast_sum, Nat.cast_pow]
  rw [Finset.sum_div]
  refine Finset.sum_bij (fun d _ => m / d) ?_ ?_ ?_ ?_
  · intro d hd
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hm.ne'⟩
  · intro a ha b hb hab
    have hda : a ∣ m := Nat.dvd_of_mem_divisors ha
    have hdb : b ∣ m := Nat.dvd_of_mem_divisors hb
    have hpos : 0 < m / a := Nat.div_pos (Nat.le_of_dvd hm hda) (Nat.pos_of_mem_divisors ha)
    have hmul : a * (m / a) = b * (m / a) := by
      rw [Nat.mul_div_cancel' hda, hab, Nat.mul_div_cancel' hdb]
    exact Nat.eq_of_mul_eq_mul_right hpos hmul
  · intro d hd
    exact ⟨m / d, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hm.ne'⟩,
      Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hm.ne'⟩
  · intro d hd
    have hda : d ∣ m := Nat.dvd_of_mem_divisors hd
    have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_mem_divisors hd)
    have hdiv : ((m / d : ℕ) : ℝ) = (m : ℝ) / (d : ℝ) := by
      rw [eq_div_iff hdpos.ne', ← Nat.cast_mul, Nat.div_mul_cancel hda]
    rw [hdiv, div_pow, one_div, inv_div]

private lemma rho_nonneg (k m : ℕ) : 0 ≤ rho k m := by
  unfold rho
  split_ifs
  · exact le_rfl
  · positivity

private lemma rho_mul_of_coprime {k a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b) :
    rho k (a * b) = rho k a * rho k b := by
  have hab : 0 < a * b := Nat.mul_pos ha hb
  unfold rho
  simp only [ha.ne', hb.ne', hab.ne', ↓reduceIte]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop]
  push_cast
  rw [mul_pow, mul_div_mul_comm]

private lemma rho_le_two_sqrt {k m : ℕ} (hk : 1 ≤ k) (hm : 0 < m) :
    rho k m ≤ 2 * Real.sqrt (m : ℝ) := by
  rw [rho_eq_sum_divisors hm]
  set s := Real.sqrt (m : ℝ)
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)
  have hs_ge1 : 1 ≤ s := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt m := Real.sqrt_le_sqrt hm1
  let A : Finset ℕ := m.divisors.filter (fun d : ℕ => (d : ℝ) ≤ s)
  let B : Finset ℕ := m.divisors.filter (fun d : ℕ => ¬ (d : ℝ) ≤ s)
  have hsplit : ∑ d ∈ m.divisors, (1 : ℝ) / (d : ℝ) ^ k =
      (∑ d ∈ A, (1 : ℝ) / (d : ℝ) ^ k) + (∑ d ∈ B, (1 : ℝ) / (d : ℝ) ^ k) := by
    rw [← Finset.sum_union]
    · congr 1
      ext d
      simp only [Finset.mem_union, Finset.mem_filter, A, B]
      tauto
    · rw [Finset.disjoint_left]
      intro d h1 h2
      simp only [Finset.mem_filter, A, B] at h1 h2
      exact h2.2 h1.2
  have hA_card : (A.card : ℝ) ≤ s := by
    have hsub : A ⊆ Finset.Icc 1 (Nat.floor s) := by
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_Icc, A] at hd ⊢
      exact ⟨Nat.pos_of_mem_divisors hd.1, Nat.le_floor hd.2⟩
    calc (A.card : ℝ) ≤ ((Finset.Icc 1 (Nat.floor s)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ = (Nat.floor s : ℝ) := by simp
      _ ≤ s := Nat.floor_le hs_pos.le
  have hA_sum : ∑ d ∈ A, (1 : ℝ) / (d : ℝ) ^ k ≤ s := by
    calc ∑ d ∈ A, (1 : ℝ) / (d : ℝ) ^ k
        ≤ ∑ _d ∈ A, (1 : ℝ) := Finset.sum_le_sum fun d hd => by
          have hdpos : 1 ≤ d := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
          have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
          exact div_le_one_of_le₀ (one_le_pow₀ hd1) (by positivity)
      _ = (A.card : ℝ) := by simp
      _ ≤ s := hA_card
  have hB_card : (B.card : ℝ) ≤ s := by
    have hinj : B.card ≤ (Finset.Icc 1 (Nat.floor s)).card := by
      refine Finset.card_le_card_of_injOn (fun d => m / d) ?_ ?_
      · intro d hd
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.coe_Icc, Set.mem_Icc, B] at hd ⊢
        have hda : d ∣ m := Nat.dvd_of_mem_divisors hd.1
        have hdpos : 0 < d := Nat.pos_of_mem_divisors hd.1
        refine ⟨Nat.div_pos (Nat.le_of_dvd hm hda) hdpos, Nat.le_floor ?_⟩
        have hgt : s < (d : ℝ) := lt_of_not_ge hd.2
        have hdiv : ((m / d : ℕ) : ℝ) = (m : ℝ) / (d : ℝ) := by
          rw [eq_div_iff (Nat.cast_pos.mpr hdpos).ne', ← Nat.cast_mul, Nat.div_mul_cancel hda]
        rw [hdiv, div_le_iff₀ (Nat.cast_pos.mpr hdpos)]
        have hsq : s * s = (m : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg m)
        nlinarith
      · intro a ha b hb hab
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, B] at ha hb
        have hda : a ∣ m := Nat.dvd_of_mem_divisors ha.1
        have hdb : b ∣ m := Nat.dvd_of_mem_divisors hb.1
        have hpos : 0 < m / a := Nat.div_pos (Nat.le_of_dvd hm hda) (Nat.pos_of_mem_divisors ha.1)
        have hmul : a * (m / a) = b * (m / a) := by
          dsimp only at hab
          rw [Nat.mul_div_cancel' hda, hab, Nat.mul_div_cancel' hdb]
        exact Nat.eq_of_mul_eq_mul_right hpos hmul
    calc (B.card : ℝ) ≤ ((Finset.Icc 1 (Nat.floor s)).card : ℝ) := by exact_mod_cast hinj
      _ = (Nat.floor s : ℝ) := by simp
      _ ≤ s := Nat.floor_le hs_pos.le
  have hB_sum : ∑ d ∈ B, (1 : ℝ) / (d : ℝ) ^ k ≤ 1 := by
    calc ∑ d ∈ B, (1 : ℝ) / (d : ℝ) ^ k
        ≤ ∑ _d ∈ B, (1 : ℝ) / s := Finset.sum_le_sum fun d hd => by
          have hdgt : s < (d : ℝ) := lt_of_not_ge (Finset.mem_filter.mp hd).2
          have hd1 : (1 : ℝ) ≤ d := by linarith
          have hpow : s ≤ (d : ℝ) ^ k := by
            calc s ≤ (d : ℝ) := hdgt.le
              _ = (d : ℝ) ^ 1 := (pow_one _).symm
              _ ≤ (d : ℝ) ^ k := pow_le_pow_right₀ hd1 hk
          exact one_div_le_one_div_of_le hs_pos hpow
      _ = (B.card : ℝ) / s := by rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
      _ ≤ s / s := div_le_div_of_nonneg_right hB_card hs_pos.le
      _ = 1 := div_self hs_pos.ne'
  rw [hsplit]
  linarith

private lemma sigma_le_two_pow_sqrt {k m : ℕ} (hk : 1 ≤ k) (hm : 0 < m) :
    (σ k m : ℝ) ≤ 2 * (m : ℝ) ^ k * Real.sqrt (m : ℝ) := by
  have h := rho_le_two_sqrt hk hm
  unfold rho at h
  simp only [hm.ne', ↓reduceIte] at h
  have hpos : (0 : ℝ) < (m : ℝ) ^ k := pow_pos (Nat.cast_pos.mpr hm) k
  rw [div_le_iff₀ hpos] at h
  linarith

private lemma sigma_le_pow_succ (k m : ℕ) : (σ k m : ℝ) ≤ (m : ℝ) ^ (k + 1) := by
  rcases m.eq_zero_or_pos with rfl | hm
  · simp
  · rw [ArithmeticFunction.sigma_apply, Nat.cast_sum]
    have hcard : m.divisors.card ≤ m := by
      calc m.divisors.card ≤ (Finset.Icc 1 m).card := Finset.card_le_card fun d hd =>
            Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
              Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors hd)⟩
        _ = m := by simp
    calc ∑ d ∈ m.divisors, ((d ^ k : ℕ) : ℝ)
        ≤ ∑ _d ∈ m.divisors, (m : ℝ) ^ k := Finset.sum_le_sum fun d hd => by
          push_cast
          exact pow_le_pow_left₀ (Nat.cast_nonneg d)
            (by exact_mod_cast Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors hd)) k
      _ = (m.divisors.card : ℝ) * (m : ℝ) ^ k := by simp
      _ ≤ (m : ℝ) * (m : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = (m : ℝ) ^ (k + 1) := by rw [pow_succ']

/- ### Part 2: Summability, scaled tail `tailT`, and integrality -/

private lemma summable_erdos252 (k : ℕ) :
    Summable (fun n : ℕ => (σ k n : ℝ) / (n ! : ℝ)) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (Real.summable_pow_div_factorial ((2 : ℝ) ^ (k + 1)))
  gcongr
  calc (σ k n : ℝ) ≤ (n : ℝ) ^ (k + 1) := sigma_le_pow_succ k n
    _ ≤ ((2 : ℝ) ^ n) ^ (k + 1) := pow_le_pow_left₀ (Nat.cast_nonneg n)
        (by exact_mod_cast Nat.le_of_lt Nat.lt_two_pow_self) _
    _ = ((2 : ℝ) ^ (k + 1)) ^ n := by rw [← pow_mul, mul_comm, pow_mul]

private noncomputable def tailT (k n : ℕ) : ℝ :=
  ∑' j : ℕ, (σ k (n + 1 + j) : ℝ) * ((n ! : ℝ) / ((n + 1 + j) ! : ℝ))

private lemma summable_tailT (k n : ℕ) :
    Summable (fun j : ℕ => (σ k (n + 1 + j) : ℝ) * ((n ! : ℝ) / ((n + 1 + j) ! : ℝ))) := by
  have h1 : Summable (fun j : ℕ => (σ k (j + (n + 1)) : ℝ) / ((j + (n + 1)) ! : ℝ)) :=
    (summable_erdos252 k).comp_injective (add_left_injective (n + 1))
  have h2 := h1.mul_left (n ! : ℝ)
  refine h2.congr fun j => ?_
  rw [add_comm j (n + 1)]
  ring

private lemma tailT_eq_sub (k n : ℕ) :
    tailT k n = (n ! : ℝ) * Erdos252.erdos_252_sum k -
      ∑ m ∈ Finset.range (n + 1), (σ k m : ℝ) * ((n ! : ℝ) / (m ! : ℝ)) := by
  have hsplit := (summable_erdos252 k).sum_add_tsum_nat_add (n + 1)
  have hmul : (n ! : ℝ) * Erdos252.erdos_252_sum k =
      (n ! : ℝ) * (∑ m ∈ Finset.range (n + 1), (σ k m : ℝ) / (m ! : ℝ)) +
      (n ! : ℝ) * (∑' j : ℕ, (σ k (j + (n + 1)) : ℝ) / ((j + (n + 1)) ! : ℝ)) := by
    unfold Erdos252.erdos_252_sum
    rw [← hsplit, mul_add]
  have hsum_eq : (n ! : ℝ) * (∑ m ∈ Finset.range (n + 1), (σ k m : ℝ) / (m ! : ℝ)) =
      ∑ m ∈ Finset.range (n + 1), (σ k m : ℝ) * ((n ! : ℝ) / (m ! : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have htsum_eq : (n ! : ℝ) * (∑' j : ℕ, (σ k (j + (n + 1)) : ℝ) / ((j + (n + 1)) ! : ℝ)) =
      tailT k n := by
    rw [← tsum_mul_left]
    unfold tailT
    refine tsum_congr fun j => ?_
    rw [add_comm j (n + 1)]
    ring
  linarith

private lemma tailT_isInt {k : ℕ} {q : ℚ} (hq : (q : ℝ) = Erdos252.erdos_252_sum k)
    {n : ℕ} (hn : q.den ≤ n) : ∃ z : ℤ, tailT k n = (z : ℝ) := by
  have hqden_dvd : q.den ∣ n ! := Nat.dvd_factorial q.pos hn
  obtain ⟨c, hc⟩ := hqden_dvd
  have hfirst : (n ! : ℝ) * Erdos252.erdos_252_sum k = ((c : ℤ) * q.num : ℤ) := by
    rw [← hq, Rat.cast_def]
    have hqpos : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.pos.ne'
    have hnc : (n ! : ℝ) = (q.den : ℝ) * (c : ℝ) := by exact_mod_cast hc
    rw [hnc]
    push_cast
    field_simp [hqpos]
  have hsecond : ∑ m ∈ Finset.range (n + 1), (σ k m : ℝ) * ((n ! : ℝ) / (m ! : ℝ)) =
      ((∑ m ∈ Finset.range (n + 1), σ k m * (n ! / m !) : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmn : m ≤ n := by have := Finset.mem_range.mp hm; omega
    have hdvd : m ! ∣ n ! := Nat.factorial_dvd_factorial hmn
    have hmpos : (m ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos m).ne'
    rw [Nat.cast_mul]
    congr 1
    rw [div_eq_iff hmpos, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]
  refine ⟨(c : ℤ) * q.num - (∑ m ∈ Finset.range (n + 1), σ k m * (n ! / m !) : ℕ), ?_⟩
  rw [tailT_eq_sub, hfirst, hsecond]
  push_cast
  rfl

/- ### Part 3: Truncating `tailT` at `h = k + 1` with `O_k(n^{-3/2})` tail -/

private lemma factorial_div_eq_prod (n h : ℕ) :
    ((n + h) ! : ℝ) / (n ! : ℝ) = ∏ j ∈ Finset.Icc 1 h, ((n : ℝ) + (j : ℝ)) := by
  induction h with
  | zero =>
    have hne : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    simp [div_self hne]
  | succ h ih =>
    have hIcc : Finset.Icc 1 (h + 1) = insert (h + 1) (Finset.Icc 1 h) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : h + 1 ∉ Finset.Icc 1 h := by simp
    rw [hIcc, Finset.prod_insert hnot, ← ih, show n + (h + 1) = (n + h) + 1 by omega,
      Nat.factorial_succ, Nat.cast_mul, mul_div_assoc]
    push_cast
    ring

private lemma factorial_ratio_eq_inv_prod (n h : ℕ) :
    (n ! : ℝ) / ((n + h) ! : ℝ) = 1 / ∏ j ∈ Finset.Icc 1 h, ((n : ℝ) + (j : ℝ)) := by
  rw [← factorial_div_eq_prod n h, one_div_div]

private lemma factorial_ratio_le_pow (n h : ℕ) (hn : 1 ≤ n) :
    (n ! : ℝ) / ((n + h) ! : ℝ) ≤ 1 / (n : ℝ) ^ h := by
  rw [factorial_ratio_eq_inv_prod]
  have hprod_ge : (n : ℝ) ^ h ≤ ∏ j ∈ Finset.Icc 1 h, ((n : ℝ) + (j : ℝ)) := by
    calc (n : ℝ) ^ h = ∏ _j ∈ Finset.Icc 1 h, (n : ℝ) := by simp
      _ ≤ ∏ j ∈ Finset.Icc 1 h, ((n : ℝ) + (j : ℝ)) :=
          Finset.prod_le_prod (fun _ _ => by positivity)
            (fun j _ => by linarith [Nat.cast_nonneg (α := ℝ) j])
  exact one_div_le_one_div_of_le (pow_pos (Nat.cast_pos.mpr hn) h) hprod_ge

private lemma tailT_truncation_bound {k n : ℕ} (hk : 1 ≤ k) (hn : 2 ^ (k + 2) ≤ n) :
    |tailT k n - ∑ h ∈ Finset.Icc 1 (k + 1),
        (σ k (n + h) : ℝ) / ∏ j ∈ Finset.Icc 1 h, ((n : ℝ) + (j : ℝ))| ≤
      (2 : ℝ) ^ (k + 3) / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
  have hn1 : 1 ≤ n := by
    have : 1 ≤ 2 ^ (k + 2) := Nat.one_le_pow _ _ (by decide)
    omega
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hsplit := (summable_tailT k n).sum_add_tsum_nat_add (k + 1)
  have hhead : ∑ j ∈ Finset.range (k + 1),
        (σ k (n + 1 + j) : ℝ) * ((n ! : ℝ) / ((n + 1 + j) ! : ℝ)) =
      ∑ h ∈ Finset.Icc 1 (k + 1),
        (σ k (n + h) : ℝ) / ∏ j ∈ Finset.Icc 1 h, ((n : ℝ) + (j : ℝ)) := by
    refine Finset.sum_bij (fun j _ => j + 1) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢; omega
    · intro a _ b _ hab; omega
    · intro h hh; simp only [Finset.mem_Icc] at hh
      exact ⟨h - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro j _
      rw [show n + 1 + j = n + (j + 1) by omega, factorial_ratio_eq_inv_prod, mul_one_div]
  have htail_eq : tailT k n - ∑ h ∈ Finset.Icc 1 (k + 1),
        (σ k (n + h) : ℝ) / ∏ j ∈ Finset.Icc 1 h, ((n : ℝ) + (j : ℝ)) =
      ∑' j : ℕ, (σ k (n + 1 + (j + (k + 1))) : ℝ) *
        ((n ! : ℝ) / ((n + 1 + (j + (k + 1))) ! : ℝ)) := by
    unfold tailT
    rw [← hsplit, hhead]
    ring
  rw [htail_eq]
  have hterm_nonneg : ∀ j : ℕ,
      0 ≤ (σ k (n + 1 + (j + (k + 1))) : ℝ) * ((n ! : ℝ) / ((n + 1 + (j + (k + 1))) ! : ℝ)) :=
    fun j => by positivity
  have hterm_le : ∀ j : ℕ,
      (σ k (n + 1 + (j + (k + 1))) : ℝ) * ((n ! : ℝ) / ((n + 1 + (j + (k + 1))) ! : ℝ)) ≤
        ((2 : ℝ) ^ (k + 2) / ((n : ℝ) * Real.sqrt (n : ℝ))) * (1 / 2 : ℝ) ^ j := by
    intro j
    set m := n + 1 + (j + (k + 1))
    have hm_eq : m = n + (k + 2 + j) := by dsimp [m]; omega
    have hm_pos : 0 < m := by omega
    have h2j : 2 + j ≤ 2 ^ (j + 1) := by
      induction j with
      | zero => decide
      | succ i ih =>
        rw [pow_succ]
        have : 1 ≤ 2 ^ (i + 1) := Nat.one_le_pow _ _ (by decide)
        omega
    have hk2_le_n : k + 2 ≤ n := by
      have : k + 2 < 2 ^ (k + 2) := Nat.lt_two_pow_self
      omega
    have hm_le_nat : m ≤ 2 ^ (j + 1) * n := by
      have h1 : m ≤ (2 + j) * n := by
        have : k + 2 + j ≤ (1 + j) * n := by
          calc k + 2 + j ≤ n + j * 1 := by omega
            _ ≤ n + j * n := Nat.add_le_add_left (Nat.mul_le_mul_left j hn1) n
            _ = (1 + j) * n := by ring
        calc m = n + (k + 2 + j) := hm_eq
          _ ≤ n + (1 + j) * n := Nat.add_le_add_left this n
          _ = (2 + j) * n := by ring
      exact le_trans h1 (Nat.mul_le_mul_right n h2j)
    have hm_le : (m : ℝ) ≤ (2 : ℝ) ^ (j + 1) * (n : ℝ) := by exact_mod_cast hm_le_nat
    have hsqrt_m : Real.sqrt (m : ℝ) ≤ (2 : ℝ) ^ (j + 1) * Real.sqrt (n : ℝ) := by
      have h1 : Real.sqrt (m : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ (j + 1) * (n : ℝ)) :=
        Real.sqrt_le_sqrt hm_le
      rw [Real.sqrt_mul (by positivity)] at h1
      have hsq2 : Real.sqrt ((2 : ℝ) ^ (j + 1)) ≤ (2 : ℝ) ^ (j + 1) := by
        have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := one_le_pow₀ (by norm_num)
        calc Real.sqrt ((2 : ℝ) ^ (j + 1))
            ≤ Real.sqrt (((2 : ℝ) ^ (j + 1)) * ((2 : ℝ) ^ (j + 1))) :=
              Real.sqrt_le_sqrt (le_mul_of_one_le_right (by positivity) hge1)
          _ = (2 : ℝ) ^ (j + 1) := Real.sqrt_mul_self (by positivity)
      exact le_trans h1 (mul_le_mul_of_nonneg_right hsq2 (Real.sqrt_nonneg _))
    have hsig : (σ k m : ℝ) ≤ 2 * ((2 : ℝ) ^ (j + 1)) ^ (k + 1) * (n : ℝ) ^ k * Real.sqrt (n : ℝ) := by
      calc (σ k m : ℝ) ≤ 2 * (m : ℝ) ^ k * Real.sqrt (m : ℝ) := sigma_le_two_pow_sqrt hk hm_pos
        _ ≤ 2 * ((2 : ℝ) ^ (j + 1) * (n : ℝ)) ^ k * ((2 : ℝ) ^ (j + 1) * Real.sqrt (n : ℝ)) := by
            gcongr
        _ = 2 * ((2 : ℝ) ^ (j + 1)) ^ (k + 1) * (n : ℝ) ^ k * Real.sqrt (n : ℝ) := by
            rw [mul_pow, pow_succ]; ring
    have hrat : (n ! : ℝ) / (m ! : ℝ) ≤ 1 / ((n : ℝ) ^ (k + 2) * ((2 : ℝ) ^ (k + 2)) ^ j) := by
      rw [hm_eq]
      calc (n ! : ℝ) / ((n + (k + 2 + j)) ! : ℝ)
          ≤ 1 / (n : ℝ) ^ (k + 2 + j) := factorial_ratio_le_pow n (k + 2 + j) hn1
        _ = 1 / ((n : ℝ) ^ (k + 2) * (n : ℝ) ^ j) := by rw [pow_add]
        _ ≤ 1 / ((n : ℝ) ^ (k + 2) * ((2 : ℝ) ^ (k + 2)) ^ j) := by
            apply one_div_le_one_div_of_le (by positivity)
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hn) j
    have hcomb := mul_le_mul hsig hrat (by positivity) (by positivity)
    refine le_trans hcomb ?_
    have hpow_id : 2 * ((2 : ℝ) ^ (j + 1)) ^ (k + 1) = (2 : ℝ) ^ (k + 2) * ((2 : ℝ) ^ (k + 1)) ^ j := by
      rw [← pow_mul, ← pow_mul, ← pow_succ', ← pow_add]
      congr 1
      ring
    have hpow2 : ((2 : ℝ) ^ (k + 1)) ^ j / ((2 : ℝ) ^ (k + 2)) ^ j = (1 / 2 : ℝ) ^ j := by
      rw [← div_pow]
      congr 1
      rw [show (2 : ℝ) ^ (k + 2) = (2 : ℝ) ^ (k + 1) * 2 by rw [pow_succ]]
      field_simp
    have hsqn : Real.sqrt (n : ℝ) / (n : ℝ) ^ 2 = 1 / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
      have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
      field_simp [hn_pos.ne', hsqrt_pos.ne']
      nlinarith [hsq]
    rw [hpow_id]
    have hnk2 : (n : ℝ) ^ (k + 2) = (n : ℝ) ^ k * (n : ℝ) ^ 2 := by rw [pow_add]
    rw [hnk2]
    have hsimp :
        (2 : ℝ) ^ (k + 2) * ((2 : ℝ) ^ (k + 1)) ^ j * (n : ℝ) ^ k * Real.sqrt (n : ℝ) *
          (1 / ((n : ℝ) ^ k * (n : ℝ) ^ 2 * ((2 : ℝ) ^ (k + 2)) ^ j)) =
        (2 : ℝ) ^ (k + 2) * (Real.sqrt (n : ℝ) / (n : ℝ) ^ 2) *
          (((2 : ℝ) ^ (k + 1)) ^ j / ((2 : ℝ) ^ (k + 2)) ^ j) := by
      have hnk_ne : (n : ℝ) ^ k ≠ 0 := (pow_pos hn_pos k).ne'
      have h2j_ne : ((2 : ℝ) ^ (k + 2)) ^ j ≠ 0 := by positivity
      field_simp [hn_pos.ne', hnk_ne, h2j_ne]
    rw [hsimp, hsqn, hpow2]
    ring_nf
    exact le_rfl
  have hsum_ge0 : 0 ≤ ∑' j : ℕ, (σ k (n + 1 + (j + (k + 1))) : ℝ) *
      ((n ! : ℝ) / ((n + 1 + (j + (k + 1))) ! : ℝ)) :=
    tsum_nonneg hterm_nonneg
  rw [abs_of_nonneg hsum_ge0]
  have hsumm_lhs : Summable (fun j : ℕ => (σ k (n + 1 + (j + (k + 1))) : ℝ) *
      ((n ! : ℝ) / ((n + 1 + (j + (k + 1))) ! : ℝ))) :=
    (summable_tailT k n).comp_injective (add_left_injective (k + 1))
  have hsumm_rhs : Summable (fun j : ℕ =>
      ((2 : ℝ) ^ (k + 2) / ((n : ℝ) * Real.sqrt (n : ℝ))) * (1 / 2 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  calc ∑' j : ℕ, (σ k (n + 1 + (j + (k + 1))) : ℝ) * ((n ! : ℝ) / ((n + 1 + (j + (k + 1))) ! : ℝ))
      ≤ ∑' j : ℕ, ((2 : ℝ) ^ (k + 2) / ((n : ℝ) * Real.sqrt (n : ℝ))) * (1 / 2 : ℝ) ^ j :=
        Summable.tsum_le_tsum hterm_le hsumm_lhs hsumm_rhs
    _ = ((2 : ℝ) ^ (k + 2) / ((n : ℝ) * Real.sqrt (n : ℝ))) * ∑' j : ℕ, (1 / 2 : ℝ) ^ j :=
        tsum_mul_left
    _ = ((2 : ℝ) ^ (k + 2) / ((n : ℝ) * Real.sqrt (n : ℝ))) * 2 := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
    _ = (2 : ℝ) ^ (k + 3) / ((n : ℝ) * Real.sqrt (n : ℝ)) := by rw [pow_succ]; ring

/- ### Part 4: Polynomial Euclidean division for rational factorial weights -/

private noncomputable def denPoly (h : ℕ) : Polynomial ℝ :=
  ∏ j ∈ Finset.Icc 1 h, (X + C (j : ℝ))

private lemma denPoly_monic (h : ℕ) : (denPoly h).Monic := by
  unfold denPoly
  exact Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_add_C (j : ℝ)

private lemma denPoly_natDegree (h : ℕ) : (denPoly h).natDegree = h := by
  unfold denPoly
  rw [Polynomial.natDegree_prod_of_monic (s := Finset.Icc 1 h)
    (f := fun j : ℕ => X + C (j : ℝ)) (fun j _ => Polynomial.monic_X_add_C (j : ℝ))]
  have hdeg1 : ∀ j ∈ Finset.Icc 1 h, (X + C (j : ℝ)).natDegree = 1 :=
    fun j _ => Polynomial.natDegree_X_add_C (j : ℝ)
  rw [Finset.sum_congr rfl hdeg1]
  simp

private lemma denPoly_eval (h : ℕ) (x : ℝ) :
    (denPoly h).eval x = ∏ j ∈ Finset.Icc 1 h, (x + (j : ℝ)) := by
  unfold denPoly
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun j _ => by simp

private noncomputable def numPoly (k h : ℕ) : Polynomial ℝ :=
  X * (X + C (h : ℝ)) ^ k

private lemma numPoly_monic (k h : ℕ) : (numPoly k h).Monic := by
  unfold numPoly
  exact Polynomial.monic_X.mul ((Polynomial.monic_X_add_C (h : ℝ)).pow k)

private lemma numPoly_natDegree (k h : ℕ) : (numPoly k h).natDegree = k + 1 := by
  unfold numPoly
  have h1 : (X : Polynomial ℝ) ≠ 0 := Polynomial.X_ne_zero
  have h2 : ((X + C (h : ℝ)) ^ k : Polynomial ℝ) ≠ 0 :=
    ((Polynomial.monic_X_add_C (h : ℝ)).pow k).ne_zero
  rw [Polynomial.natDegree_mul h1 h2, Polynomial.natDegree_X,
    (Polynomial.monic_X_add_C (h : ℝ)).natDegree_pow, Polynomial.natDegree_X_add_C]
  omega

private noncomputable def Qpoly (k h : ℕ) : Polynomial ℝ :=
  numPoly k h /ₘ denPoly h

private noncomputable def Rpoly (k h : ℕ) : Polynomial ℝ :=
  numPoly k h %ₘ denPoly h

private noncomputable def Ppoly (k h : ℕ) : Polynomial ℝ :=
  (Qpoly k h).divX

private noncomputable def cConst (k h : ℕ) : ℝ :=
  (Qpoly k h).coeff 0

private lemma Qpoly_natDegree (k h : ℕ) :
    (Qpoly k h).natDegree = k + 1 - h := by
  unfold Qpoly
  rw [Polynomial.natDegree_divByMonic _ (denPoly_monic h), numPoly_natDegree, denPoly_natDegree]

private lemma Qpoly_top (k : ℕ) : Qpoly k (k + 1) = 1 := by
  have hdeg : (Qpoly k (k + 1)).natDegree = 0 := by
    rw [Qpoly_natDegree]; omega
  have hQeq : Qpoly k (k + 1) = C ((Qpoly k (k + 1)).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hdiv : Rpoly k (k + 1) + denPoly (k + 1) * Qpoly k (k + 1) = numPoly k (k + 1) :=
    Polynomial.modByMonic_add_div (numPoly k (k + 1)) (denPoly (k + 1))
  have hR_lt : (Rpoly k (k + 1)).degree < ((k + 1 : ℕ) : WithBot ℕ) := by
    have h1 := Polynomial.degree_modByMonic_lt (numPoly k (k + 1)) (denPoly_monic (k + 1))
    rwa [Polynomial.degree_eq_natDegree (denPoly_monic (k + 1)).ne_zero, denPoly_natDegree] at h1
  have hR0 : (Rpoly k (k + 1)).coeff (k + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt hR_lt
  have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff (k + 1)) hdiv
  rw [Polynomial.coeff_add, hR0, zero_add, hQeq, Polynomial.coeff_mul_C] at hcoeff
  have hden1 : (denPoly (k + 1)).coeff (k + 1) = 1 := by
    have h1 := (denPoly_monic (k + 1)).leadingCoeff
    rwa [Polynomial.leadingCoeff, denPoly_natDegree] at h1
  have hnum1 : (numPoly k (k + 1)).coeff (k + 1) = 1 := by
    have h1 := (numPoly_monic k (k + 1)).leadingCoeff
    rwa [Polynomial.leadingCoeff, numPoly_natDegree] at h1
  rw [hden1, hnum1, one_mul] at hcoeff
  rw [hQeq, hcoeff, map_one]

private lemma Ppoly_top (k : ℕ) : Ppoly k (k + 1) = 0 := by
  unfold Ppoly
  rw [Qpoly_top]
  ext n
  simp

private lemma cConst_top (k : ℕ) : cConst k (k + 1) = 1 := by
  unfold cConst
  rw [Qpoly_top]
  simp

private lemma Ppoly_natDegree_le {k h : ℕ} (hh : h ≤ k) :
    (Ppoly k h).natDegree ≤ k - h := by
  unfold Ppoly
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro d hd
  rw [Polynomial.coeff_divX]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [Qpoly_natDegree]
  omega

private lemma rational_weight_decomp {k h n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) + (h : ℝ)) ^ k / (∏ j ∈ Finset.Icc 1 h, ((n : ℝ) + (j : ℝ))) =
      (Ppoly k h).eval (n : ℝ) + cConst k h / (n : ℝ) +
      (Rpoly k h).eval (n : ℝ) / ((n : ℝ) * ∏ j ∈ Finset.Icc 1 h, ((n : ℝ) + (j : ℝ))) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hden_pos : (0 : ℝ) < ∏ j ∈ Finset.Icc 1 h, ((n : ℝ) + (j : ℝ)) :=
    Finset.prod_pos fun j _ => by positivity
  have hdiv := Polynomial.modByMonic_add_div (numPoly k h) (denPoly h)
  have hQsplit : X * Ppoly k h + C (cConst k h) = Qpoly k h :=
    Polynomial.X_mul_divX_add (Qpoly k h)
  have heval := congrArg (Polynomial.eval (n : ℝ)) hdiv
  have hevalQ := congrArg (Polynomial.eval (n : ℝ)) hQsplit
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_pow, numPoly, denPoly_eval] at heval hevalQ
  change (Rpoly k h).eval (n : ℝ) +
      (∏ j ∈ Finset.Icc 1 h, ((n : ℝ) + (j : ℝ))) * (Qpoly k h).eval (n : ℝ) =
    (n : ℝ) * ((n : ℝ) + (h : ℝ)) ^ k at heval
  rw [← hevalQ] at heval
  field_simp [hn_pos.ne', hden_pos.ne']
  linarith

private lemma Rpoly_remainder_bound (k h : ℕ) (hh : 1 ≤ h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      |(Rpoly k h).eval (n : ℝ) / ((n : ℝ) * ∏ j ∈ Finset.Icc 1 h, ((n : ℝ) + (j : ℝ)))| ≤
        C / (n : ℝ) ^ 2 := by
  let C : ℝ := ∑ i ∈ Finset.range h, |(Rpoly k h).coeff i|
  refine ⟨C, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_ge1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hden_ge : (n : ℝ) ^ (h + 1) ≤ (n : ℝ) * ∏ j ∈ Finset.Icc 1 h, ((n : ℝ) + (j : ℝ)) := by
    rw [pow_succ']
    apply mul_le_mul_of_nonneg_left _ hn_pos.le
    calc (n : ℝ) ^ h = ∏ _j ∈ Finset.Icc 1 h, (n : ℝ) := by simp
      _ ≤ ∏ j ∈ Finset.Icc 1 h, ((n : ℝ) + (j : ℝ)) :=
          Finset.prod_le_prod (fun _ _ => hn_pos.le)
            (fun j _ => by linarith [Nat.cast_nonneg (α := ℝ) j])
  have hR_lt : (Rpoly k h).degree < (h : WithBot ℕ) := by
    have hlt := Polynomial.degree_modByMonic_lt (numPoly k h) (denPoly_monic h)
    rwa [Polynomial.degree_eq_natDegree (denPoly_monic h).ne_zero, denPoly_natDegree] at hlt
  have hR_eval : (Rpoly k h).eval (n : ℝ) =
      ∑ i ∈ Finset.range h, (Rpoly k h).coeff i * (n : ℝ) ^ i := by
    rw [Polynomial.eval_eq_sum_range' (n := h)]
    by_cases hR0 : Rpoly k h = 0
    · rw [hR0, Polynomial.natDegree_zero]; omega
    · rw [Polynomial.degree_eq_natDegree hR0] at hR_lt
      exact_mod_cast hR_lt
  have hR_abs : |(Rpoly k h).eval (n : ℝ)| ≤ C * (n : ℝ) ^ (h - 1) := by
    rw [hR_eval]
    calc |∑ i ∈ Finset.range h, (Rpoly k h).coeff i * (n : ℝ) ^ i|
        ≤ ∑ i ∈ Finset.range h, |(Rpoly k h).coeff i * (n : ℝ) ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range h, |(Rpoly k h).coeff i| * (n : ℝ) ^ (h - 1) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [abs_mul, abs_of_nonneg (pow_nonneg hn_pos.le i)]
          have hile : i ≤ h - 1 := by have := Finset.mem_range.mp hi; omega
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn_ge1 hile) (abs_nonneg _)
      _ = C * (n : ℝ) ^ (h - 1) := (Finset.sum_mul _ _ _).symm
  have hden_pos : (0 : ℝ) < (n : ℝ) * ∏ j ∈ Finset.Icc 1 h, ((n : ℝ) + (j : ℝ)) :=
    mul_pos hn_pos (Finset.prod_pos fun j _ => by positivity)
  rw [abs_div, abs_of_pos hden_pos]
  calc |(Rpoly k h).eval (n : ℝ)| / ((n : ℝ) * ∏ j ∈ Finset.Icc 1 h, ((n : ℝ) + (j : ℝ)))
      ≤ (C * (n : ℝ) ^ (h - 1)) / (n : ℝ) ^ (h + 1) :=
        div_le_div₀ (by positivity) hR_abs (pow_pos hn_pos (h + 1)) hden_ge
    _ = C / (n : ℝ) ^ 2 := by
        have hpow_eq : (n : ℝ) ^ (h + 1) = (n : ℝ) ^ (h - 1) * (n : ℝ) ^ 2 := by
          rw [← pow_add]; congr 1; omega
        rw [hpow_eq]
        have hne : (n : ℝ) ^ (h - 1) ≠ 0 := (pow_pos hn_pos _).ne'
        field_simp [hne, hn_pos.ne']

/- ### Part 5: Alternating binomial finite-difference vanishing -/

private lemma alt_binom_sum_pow_eq_zero :
    ∀ (n d : ℕ), d < n →
      ∑ m ∈ Finset.range (n + 1), ((-1 : ℝ) ^ m * (n.choose m : ℝ)) * (m : ℝ) ^ d = 0
  | 0, d, hd => by omega
  | n + 1, d, hd => by
    have hsplit :
        ∑ m ∈ Finset.range (n + 2), ((-1 : ℝ) ^ m * ((n + 1).choose m : ℝ)) * (m : ℝ) ^ d =
        ∑ m ∈ Finset.range (n + 1), ((-1 : ℝ) ^ m * (n.choose m : ℝ)) *
          ((m : ℝ) ^ d - ((m + 1 : ℕ) : ℝ) ^ d) := by
      have h1 : ∑ m ∈ Finset.range (n + 2),
            ((-1 : ℝ) ^ m * ((n + 1).choose m : ℝ)) * (m : ℝ) ^ d =
          ((0 : ℕ) : ℝ) ^ d +
            ∑ m ∈ Finset.range (n + 1),
              ((-1 : ℝ) ^ (m + 1) * ((n + 1).choose (m + 1) : ℝ)) * ((m + 1 : ℕ) : ℝ) ^ d := by
        rw [Finset.sum_range_succ']
        simp [add_comm]
      have h2 : ∑ m ∈ Finset.range (n + 1),
            ((-1 : ℝ) ^ (m + 1) * ((n + 1).choose (m + 1) : ℝ)) * ((m + 1 : ℕ) : ℝ) ^ d =
          (∑ m ∈ Finset.range (n + 1),
              ((-1 : ℝ) ^ (m + 1) * (n.choose m : ℝ)) * ((m + 1 : ℕ) : ℝ) ^ d) +
          (∑ m ∈ Finset.range (n + 1),
              ((-1 : ℝ) ^ (m + 1) * (n.choose (m + 1) : ℝ)) * ((m + 1 : ℕ) : ℝ) ^ d) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Nat.choose_succ_succ, Nat.cast_add]
        ring
      have h3 : ((0 : ℕ) : ℝ) ^ d +
          ∑ m ∈ Finset.range (n + 1),
            ((-1 : ℝ) ^ (m + 1) * (n.choose (m + 1) : ℝ)) * ((m + 1 : ℕ) : ℝ) ^ d =
          ∑ m ∈ Finset.range (n + 1), ((-1 : ℝ) ^ m * (n.choose m : ℝ)) * (m : ℝ) ^ d := by
        have hlast : ((-1 : ℝ) ^ (n + 1) * (n.choose (n + 1) : ℝ)) * ((n + 1 : ℕ) : ℝ) ^ d = 0 := by
          rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)]; simp
        have hshift := Finset.sum_range_succ'
          (fun m => ((-1 : ℝ) ^ m * (n.choose m : ℝ)) * (m : ℝ) ^ d) (n + 1)
        rw [Finset.sum_range_succ] at hshift
        simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul] at hshift
        linarith
      rw [h1, h2]
      have hcomb : (∑ m ∈ Finset.range (n + 1), ((-1 : ℝ) ^ m * (n.choose m : ℝ)) * (m : ℝ) ^ d) +
          (∑ m ∈ Finset.range (n + 1),
            ((-1 : ℝ) ^ (m + 1) * (n.choose m : ℝ)) * ((m + 1 : ℕ) : ℝ) ^ d) =
          ∑ m ∈ Finset.range (n + 1), ((-1 : ℝ) ^ m * (n.choose m : ℝ)) *
            ((m : ℝ) ^ d - ((m + 1 : ℕ) : ℝ) ^ d) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [pow_succ]
        ring
      linarith
    rw [hsplit]
    have hdiff : ∀ m : ℕ, (m : ℝ) ^ d - ((m + 1 : ℕ) : ℝ) ^ d =
        - ∑ j ∈ Finset.range d, (d.choose j : ℝ) * (m : ℝ) ^ j := by
      intro m
      rw [Nat.cast_add, Nat.cast_one, add_pow, Finset.sum_range_succ]
      simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one]
      have hcongr : ∑ j ∈ Finset.range d, (m : ℝ) ^ j * (d.choose j : ℝ) =
          ∑ j ∈ Finset.range d, (d.choose j : ℝ) * (m : ℝ) ^ j :=
        Finset.sum_congr rfl fun _ _ => mul_comm _ _
      rw [hcongr]
      ring
    simp_rw [hdiff, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hzero : ∀ j ∈ Finset.range d,
        ∑ m ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ m * (n.choose m : ℝ) * ((d.choose j : ℝ) * (m : ℝ) ^ j) = 0 := by
      intro j hj
      have hjlt : j < n := by have := Finset.mem_range.mp hj; omega
      have hpull : ∑ m ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ m * (n.choose m : ℝ) * ((d.choose j : ℝ) * (m : ℝ) ^ j) =
          (d.choose j : ℝ) *
            ∑ m ∈ Finset.range (n + 1), ((-1 : ℝ) ^ m * (n.choose m : ℝ)) * (m : ℝ) ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => by ring
      rw [hpull, alt_binom_sum_pow_eq_zero n j hjlt, mul_zero]
    rw [Finset.sum_eq_zero hzero, neg_zero]

private lemma alt_binom_sum_poly_eq_zero (n : ℕ) (f : Polynomial ℝ)
    (hf : f = 0 ∨ f.natDegree < n) :
    ∑ m ∈ Finset.range (n + 1), ((-1 : ℝ) ^ m * (n.choose m : ℝ)) * f.eval (m : ℝ) = 0 := by
  rcases hf with rfl | hdeg
  · simp
  · have heval : ∀ m : ℕ, f.eval (m : ℝ) = ∑ d ∈ Finset.range n, f.coeff d * (m : ℝ) ^ d :=
      fun m => Polynomial.eval_eq_sum_range' hdeg (m : ℝ)
    simp_rw [heval, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun d hd => ?_
    have hpull : ∑ m ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ m * (n.choose m : ℝ) * (f.coeff d * (m : ℝ) ^ d) =
        f.coeff d * ∑ m ∈ Finset.range (n + 1), ((-1 : ℝ) ^ m * (n.choose m : ℝ)) * (m : ℝ) ^ d := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => by ring
    rw [hpull, alt_binom_sum_pow_eq_zero n d (Finset.mem_range.mp hd), mul_zero]

/- ### Part 6: Coprime `k`-dimensional dilation grid and cancellation -/

private abbrev Grid (k : ℕ) : Type := Fin k → Fin (k + 2)

private def Mgrid (k : ℕ) : ℕ := (k + 2) ^ k

private def Dgrid (k : ℕ) : ℕ := (Mgrid k) !

private def aStep (k : ℕ) (s : Fin k) : ℕ := Dgrid k * (k + 2) ^ s.val

private def Sgrid (k : ℕ) (e : Grid k) : ℕ :=
  ∑ s : Fin k, (k + 2) ^ s.val * (e s).val

private def P0grid (k : ℕ) : ℕ := 1 + Dgrid k * (k * (k + 1) * Mgrid k)

private def pGrid (k : ℕ) (e : Grid k) : ℕ :=
  P0grid k + ∑ s : Fin k, aStep k s * (e s).val

private def tGrid (k : ℕ) (e : Grid k) : ℕ :=
  ∑ s : Fin k, (s.val + 1) * aStep k s * (e s).val

private def rShift (k h : ℕ) (e : Grid k) : ℕ :=
  h * pGrid k e - tGrid k e

private def wGrid (k : ℕ) (e : Grid k) : ℤ :=
  ∏ s : Fin k, (-1 : ℤ) ^ (e s).val * ((k + 1).choose (e s).val : ℤ)

private def eStar (k : ℕ) : Grid k := fun _ => ⟨k + 1, by omega⟩

private lemma base_repr_lt_and_inj (B : ℕ) (hB : 2 ≤ B) :
    ∀ (m : ℕ),
      (∀ f : Fin m → Fin B, ∑ s : Fin m, B ^ s.val * (f s).val < B ^ m) ∧
      Function.Injective (fun f : Fin m → Fin B => ∑ s : Fin m, B ^ s.val * (f s).val)
  | 0 => by
    constructor
    · intro _; simp
    · intro f g _; ext s; exact Fin.elim0 s
  | m + 1 => by
    obtain ⟨ih_lt, ih_inj⟩ := base_repr_lt_and_inj B hB m
    have hsplit : ∀ f : Fin (m + 1) → Fin B,
        ∑ s : Fin (m + 1), B ^ s.val * (f s).val =
          (f 0).val + B * ∑ s : Fin m, B ^ s.val * (f s.succ).val := by
      intro f
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun s _ => by rw [pow_succ']; ring
    constructor
    · intro f
      rw [hsplit f]
      have h1 : (f 0).val < B := (f 0).isLt
      have h2 : ∑ s : Fin m, B ^ s.val * (f s.succ).val < B ^ m := ih_lt (fun s => f s.succ)
      have h3 : B * (∑ s : Fin m, B ^ s.val * (f s.succ).val + 1) ≤ B ^ (m + 1) := by
        rw [pow_succ']
        exact Nat.mul_le_mul_left B h2
      rw [mul_add, mul_one] at h3
      omega
    · intro f g hfg
      dsimp only at hfg
      rw [hsplit f, hsplit g] at hfg
      have hmod : (f 0).val = (g 0).val := by
        have h1 := congrArg (· % B) hfg
        rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (f 0).isLt, Nat.mod_eq_of_lt (g 0).isLt] at h1
        exact h1
      have hdiv : ∑ s : Fin m, B ^ s.val * (f s.succ).val =
          ∑ s : Fin m, B ^ s.val * (g s.succ).val := by
        have hBpos : 0 < B := by omega
        have hmul : B * ∑ s : Fin m, B ^ s.val * (f s.succ).val =
            B * ∑ s : Fin m, B ^ s.val * (g s.succ).val := by omega
        exact Nat.eq_of_mul_eq_mul_left hBpos hmul
      have htail : (fun s : Fin m => f s.succ) = (fun s : Fin m => g s.succ) := ih_inj hdiv
      ext s
      cases s using Fin.cases with
      | zero => exact hmod
      | succ i => exact congrArg Fin.val (congrFun htail i)

private lemma Sgrid_lt (k : ℕ) (e : Grid k) : Sgrid k e < Mgrid k :=
  (base_repr_lt_and_inj (k + 2) (by omega) k).1 e

private lemma Sgrid_inj (k : ℕ) : Function.Injective (Sgrid k) :=
  (base_repr_lt_and_inj (k + 2) (by omega) k).2

private lemma pGrid_eq_one_add (k : ℕ) (e : Grid k) :
    pGrid k e = 1 + Dgrid k * (k * (k + 1) * Mgrid k + Sgrid k e) := by
  unfold pGrid P0grid Sgrid aStep
  have hsum : ∑ s : Fin k, Dgrid k * (k + 2) ^ s.val * (e s).val =
      Dgrid k * ∑ s : Fin k, (k + 2) ^ s.val * (e s).val := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => by ring
  rw [hsum]
  ring

private lemma pGrid_pos (k : ℕ) (e : Grid k) : 0 < pGrid k e := by
  rw [pGrid_eq_one_add]; omega

private lemma pGrid_coprime_Dgrid (k : ℕ) (e : Grid k) : Nat.Coprime (pGrid k e) (Dgrid k) := by
  apply Nat.coprime_of_dvd
  intro q hq hq1 hq2
  rw [pGrid_eq_one_add] at hq1
  have : q ∣ 1 := (Nat.dvd_add_left (dvd_mul_of_dvd_left hq2 _)).mp hq1
  exact hq.not_dvd_one this

private lemma pGrid_coprime_small {k h : ℕ} (hk : 1 ≤ k) (hh1 : 1 ≤ h) (hh2 : h ≤ k + 1)
    (e : Grid k) : Nat.Coprime (pGrid k e) h := by
  have hle : h ≤ Mgrid k := by
    unfold Mgrid
    have : k + 2 ≤ (k + 2) ^ k := Nat.le_self_pow (by omega) (k + 2)
    omega
  have hdvd : h ∣ Dgrid k := Nat.dvd_factorial hh1 hle
  exact (pGrid_coprime_Dgrid k e).coprime_dvd_right hdvd

private lemma pGrid_pairwise_coprime (k : ℕ) {e₁ e₂ : Grid k} (hne : e₁ ≠ e₂) :
    Nat.Coprime (pGrid k e₁) (pGrid k e₂) := by
  have hSne : Sgrid k e₁ ≠ Sgrid k e₂ := fun h => hne (Sgrid_inj k h)
  have hcopD : Nat.Coprime (pGrid k e₁) (Dgrid k) := pGrid_coprime_Dgrid k e₁
  have hcopD2 : Nat.Coprime (pGrid k e₁) (Dgrid k * Dgrid k) := hcopD.mul_right hcopD
  rcases lt_or_gt_of_ne hSne with hlt | hgt
  · have hdiff_le : Sgrid k e₂ - Sgrid k e₁ ≤ Mgrid k := by
      have := Sgrid_lt k e₂; omega
    have hdiff_pos : 1 ≤ Sgrid k e₂ - Sgrid k e₁ := by omega
    have hdvd1 : (Sgrid k e₂ - Sgrid k e₁) ∣ Dgrid k := Nat.dvd_factorial hdiff_pos hdiff_le
    have hpeq : pGrid k e₂ = pGrid k e₁ + Dgrid k * (Sgrid k e₂ - Sgrid k e₁) := by
      rw [pGrid_eq_one_add, pGrid_eq_one_add]
      have : Dgrid k * (k * (k + 1) * Mgrid k + Sgrid k e₂) =
          Dgrid k * (k * (k + 1) * Mgrid k + Sgrid k e₁) + Dgrid k * (Sgrid k e₂ - Sgrid k e₁) := by
        rw [← mul_add]; congr 1; omega
      omega
    rw [hpeq, Nat.coprime_self_add_right]
    exact hcopD2.coprime_dvd_right (mul_dvd_mul_left (Dgrid k) hdvd1)
  · have hdiff_le : Sgrid k e₁ - Sgrid k e₂ ≤ Mgrid k := by
      have := Sgrid_lt k e₁; omega
    have hdiff_pos : 1 ≤ Sgrid k e₁ - Sgrid k e₂ := by omega
    have hdvd1 : (Sgrid k e₁ - Sgrid k e₂) ∣ Dgrid k := Nat.dvd_factorial hdiff_pos hdiff_le
    have hpeq : pGrid k e₁ = pGrid k e₂ + Dgrid k * (Sgrid k e₁ - Sgrid k e₂) := by
      rw [pGrid_eq_one_add, pGrid_eq_one_add]
      have : Dgrid k * (k * (k + 1) * Mgrid k + Sgrid k e₁) =
          Dgrid k * (k * (k + 1) * Mgrid k + Sgrid k e₂) + Dgrid k * (Sgrid k e₁ - Sgrid k e₂) := by
        rw [← mul_add]; congr 1; omega
      omega
    have hcopD' : Nat.Coprime (pGrid k e₂) (Dgrid k) := pGrid_coprime_Dgrid k e₂
    have hcopD2' : Nat.Coprime (pGrid k e₂) (Dgrid k * Dgrid k) := hcopD'.mul_right hcopD'
    rw [Nat.coprime_comm, hpeq, Nat.coprime_self_add_right]
    exact hcopD2'.coprime_dvd_right (mul_dvd_mul_left (Dgrid k) hdvd1)

private lemma sum_aStep_lt (k : ℕ) :
    ∑ s : Fin k, aStep k s < Dgrid k * Mgrid k := by
  unfold aStep Mgrid
  rw [← Finset.mul_sum]
  apply Nat.mul_lt_mul_of_pos_left _ (Nat.factorial_pos _)
  have h1 : ∀ m : ℕ, ∑ s : Fin m, (k + 2) ^ s.val < (k + 2) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Fin.sum_univ_castSucc, pow_succ]
      simp only [Fin.val_castSucc, Fin.val_last]
      have h2 : (k + 2) ^ m * 1 + (k + 2) ^ m ≤ (k + 2) ^ m * (k + 2) := by
        have : 2 ≤ k + 2 := by omega
        calc (k + 2) ^ m * 1 + (k + 2) ^ m = (k + 2) ^ m * 2 := by ring
          _ ≤ (k + 2) ^ m * (k + 2) := Nat.mul_le_mul_left _ this
      omega
  exact h1 k

private lemma tGrid_lt_pGrid (k : ℕ) (e : Grid k) : tGrid k e < pGrid k e := by
  have ht_le : tGrid k e ≤ k * (k + 1) * ∑ s : Fin k, aStep k s := by
    unfold tGrid
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have hs1 : s.val + 1 ≤ k := s.isLt
    have he1 : (e s).val ≤ k + 1 := by have := (e s).isLt; omega
    calc (s.val + 1) * aStep k s * (e s).val
        = (s.val + 1) * (e s).val * aStep k s := by ring
      _ ≤ k * (k + 1) * aStep k s := Nat.mul_le_mul_right _ (Nat.mul_le_mul hs1 he1)
  have hP0 : k * (k + 1) * ∑ s : Fin k, aStep k s < P0grid k := by
    unfold P0grid
    have hlt := sum_aStep_lt k
    have hle : k * (k + 1) * ∑ s : Fin k, aStep k s ≤ k * (k + 1) * (Dgrid k * Mgrid k) :=
      Nat.mul_le_mul_left _ hlt.le
    calc k * (k + 1) * ∑ s : Fin k, aStep k s
        ≤ k * (k + 1) * (Dgrid k * Mgrid k) := hle
      _ = Dgrid k * (k * (k + 1) * Mgrid k) := by ring
      _ < 1 + Dgrid k * (k * (k + 1) * Mgrid k) := by omega
  have hp_ge : P0grid k ≤ pGrid k e := Nat.le_add_right _ _
  omega

private lemma rShift_pos {k h : ℕ} (hh : 1 ≤ h) (e : Grid k) : 0 < rShift k h e := by
  unfold rShift
  have h1 := tGrid_lt_pGrid k e
  have h2 : pGrid k e ≤ h * pGrid k e := Nat.le_mul_of_pos_left _ hh
  omega

private lemma rShift_strict_max {k h : ℕ} (hh1 : 1 ≤ h) (hh2 : h ≤ k + 1) (e : Grid k)
    (hne : ¬ (h = k + 1 ∧ e = eStar k)) :
    rShift k h e < rShift k (k + 1) (eStar k) := by
  have ht1 := tGrid_lt_pGrid k e
  have ht2 := tGrid_lt_pGrid k (eStar k)
  have h1p : pGrid k e ≤ h * pGrid k e := Nat.le_mul_of_pos_left _ hh1
  have h2p : pGrid k (eStar k) ≤ (k + 1) * pGrid k (eStar k) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hformula : ∀ (hh : ℕ) (ee : Grid k),
      (hh * pGrid k ee : ℤ) - (tGrid k ee : ℤ) =
        (hh : ℤ) * (P0grid k : ℤ) +
          ∑ s : Fin k, ((hh : ℤ) - ((s.val + 1 : ℕ) : ℤ)) * (aStep k s : ℤ) * ((ee s).val : ℤ) := by
    intro hh ee
    unfold pGrid tGrid
    push_cast
    rw [mul_add, Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun s _ => by ring
  have hcast : ∀ (hh : ℕ) (ee : Grid k), 1 ≤ hh →
      (rShift k hh ee : ℤ) = (hh * pGrid k ee : ℤ) - (tGrid k ee : ℤ) := by
    intro hh ee hge
    unfold rShift
    have hlt := tGrid_lt_pGrid k ee
    have hmul : pGrid k ee ≤ hh * pGrid k ee := Nat.le_mul_of_pos_left _ hge
    omega
  suffices hZ : (rShift k h e : ℤ) < (rShift k (k + 1) (eStar k) : ℤ) by exact_mod_cast hZ
  rw [hcast h e hh1, hcast (k + 1) (eStar k) (by omega), hformula h e, hformula (k + 1) (eStar k)]
  by_cases htop : h = k + 1
  · subst htop
    have hene : e ≠ eStar k := fun heq => hne ⟨rfl, heq⟩
    have hex : ∃ s : Fin k, (e s).val < k + 1 := by
      by_contra hall
      push Not at hall
      apply hene
      ext s
      have hlt := (e s).isLt
      have hge := hall s
      dsimp [eStar]
      omega
    obtain ⟨s₀, hs₀⟩ := hex
    have hsum_lt :
        ∑ s : Fin k, (((k + 1 : ℕ) : ℤ) - ((s.val + 1 : ℕ) : ℤ)) * (aStep k s : ℤ) * ((e s).val : ℤ) <
        ∑ s : Fin k, (((k + 1 : ℕ) : ℤ) - ((s.val + 1 : ℕ) : ℤ)) * (aStep k s : ℤ) * ((eStar k s).val : ℤ) := by
      refine Finset.sum_lt_sum ?_ ⟨s₀, Finset.mem_univ s₀, ?_⟩
      · intro s _
        have hcoef : (0 : ℤ) ≤ (((k + 1 : ℕ) : ℤ) - ((s.val + 1 : ℕ) : ℤ)) * (aStep k s : ℤ) := by
          have hs : s.val < k := s.isLt
          have : (0 : ℤ) ≤ ((k + 1 : ℕ) : ℤ) - ((s.val + 1 : ℕ) : ℤ) := by omega
          exact mul_nonneg this (Nat.cast_nonneg _)
        have hele : ((e s).val : ℤ) ≤ ((eStar k s).val : ℤ) := by
          have := (e s).isLt; dsimp [eStar]; omega
        exact mul_le_mul_of_nonneg_left hele hcoef
      · have hs : s₀.val < k := s₀.isLt
        have ha_pos : (0 : ℤ) < (aStep k s₀ : ℤ) := by
          unfold aStep Dgrid
          exact Nat.cast_pos.mpr (Nat.mul_pos (Nat.factorial_pos _) (Nat.pow_pos (by omega)))
        have hcoef : (0 : ℤ) < (((k + 1 : ℕ) : ℤ) - ((s₀.val + 1 : ℕ) : ℤ)) * (aStep k s₀ : ℤ) :=
          mul_pos (by omega) ha_pos
        have hlt' : ((e s₀).val : ℤ) < ((eStar k s₀).val : ℤ) := by dsimp [eStar]; omega
        exact mul_lt_mul_of_pos_left hlt' hcoef
    linarith
  · have hle_k : h ≤ k := by omega
    have hsum_star_nonneg :
        (0 : ℤ) ≤ ∑ s : Fin k, (((k + 1 : ℕ) : ℤ) - ((s.val + 1 : ℕ) : ℤ)) *
          (aStep k s : ℤ) * ((eStar k s).val : ℤ) := by
      refine Finset.sum_nonneg fun s _ => ?_
      have hs : s.val < k := s.isLt
      have h1 : (0 : ℤ) ≤ ((k + 1 : ℕ) : ℤ) - ((s.val + 1 : ℕ) : ℤ) := by omega
      positivity
    have hsum_e_le :
        ∑ s : Fin k, ((h : ℤ) - ((s.val + 1 : ℕ) : ℤ)) * (aStep k s : ℤ) * ((e s).val : ℤ) ≤
          (k * (k + 1) * ∑ s : Fin k, aStep k s : ℕ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      have h1 : (h : ℤ) - ((s.val + 1 : ℕ) : ℤ) ≤ (k : ℤ) := by omega
      have h2 : ((e s).val : ℤ) ≤ ((k + 1 : ℕ) : ℤ) := by have := (e s).isLt; omega
      have h3 : (0 : ℤ) ≤ (aStep k s : ℤ) * ((e s).val : ℤ) := by positivity
      calc ((h : ℤ) - ((s.val + 1 : ℕ) : ℤ)) * (aStep k s : ℤ) * ((e s).val : ℤ)
          = ((h : ℤ) - ((s.val + 1 : ℕ) : ℤ)) * ((aStep k s : ℤ) * ((e s).val : ℤ)) := by ring
        _ ≤ (k : ℤ) * ((aStep k s : ℤ) * ((e s).val : ℤ)) := mul_le_mul_of_nonneg_right h1 h3
        _ ≤ (k : ℤ) * ((aStep k s : ℤ) * ((k + 1 : ℕ) : ℤ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)
        _ = (k : ℤ) * ((k : ℤ) + 1) * (aStep k s : ℤ) := by push_cast; ring
    have hP0_gt : ((k * (k + 1) * ∑ s : Fin k, aStep k s : ℕ) : ℤ) < (P0grid k : ℤ) := by
      have hlt := sum_aStep_lt k
      unfold P0grid
      have hnat : k * (k + 1) * ∑ s : Fin k, aStep k s < 1 + Dgrid k * (k * (k + 1) * Mgrid k) := by
        have hle := Nat.mul_le_mul_left (k * (k + 1)) hlt.le
        calc k * (k + 1) * ∑ s : Fin k, aStep k s
            ≤ k * (k + 1) * (Dgrid k * Mgrid k) := hle
          _ = Dgrid k * (k * (k + 1) * Mgrid k) := by ring
          _ < 1 + Dgrid k * (k * (k + 1) * Mgrid k) := by omega
      exact_mod_cast hnat
    have hP_diff : (P0grid k : ℤ) ≤ (((k + 1 : ℕ) : ℤ) - (h : ℤ)) * (P0grid k : ℤ) := by
      have h1 : (1 : ℤ) ≤ ((k + 1 : ℕ) : ℤ) - (h : ℤ) := by omega
      nlinarith
    linarith

private lemma wGrid_eStar (k : ℕ) : wGrid k (eStar k) = 1 := by
  unfold wGrid eStar
  simp only [Nat.choose_self, Nat.cast_one, mul_one, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← pow_mul]
  have heven : Even ((k + 1) * k) := by
    rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact ⟨(m + m + 1) * m, by ring⟩
    · exact ⟨(m + 1) * (2 * m + 1), by ring⟩
  exact heven.neg_one_pow

private lemma rShift_update_eq (k : ℕ) (s₀ : Fin k) (e : Grid k) (m : Fin (k + 2)) :
    rShift k (s₀.val + 1) (Function.update e s₀ m) = rShift k (s₀.val + 1) e := by
  have h1 : ∀ ee : Grid k, (rShift k (s₀.val + 1) ee : ℤ) =
      ((s₀.val + 1 : ℕ) : ℤ) * (P0grid k : ℤ) +
        ∑ s : Fin k, (((s₀.val + 1 : ℕ) : ℤ) - ((s.val + 1 : ℕ) : ℤ)) *
          (aStep k s : ℤ) * ((ee s).val : ℤ) := by
    intro ee
    unfold rShift
    have hlt := tGrid_lt_pGrid k ee
    have hmul : pGrid k ee ≤ (s₀.val + 1) * pGrid k ee := Nat.le_mul_of_pos_left _ (by omega)
    have hsub : ((s₀.val + 1) * pGrid k ee - tGrid k ee : ℕ) =
        (((s₀.val + 1) * pGrid k ee : ℕ) : ℤ) - (tGrid k ee : ℤ) := by omega
    rw [hsub]
    unfold pGrid tGrid
    push_cast
    rw [mul_add, Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun s _ => by ring
  suffices hZ : (rShift k (s₀.val + 1) (Function.update e s₀ m) : ℤ) =
      (rShift k (s₀.val + 1) e : ℤ) by exact_mod_cast hZ
  rw [h1, h1]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s = s₀
  · subst hs; simp
  · rw [Function.update_of_ne hs]

private lemma poly_part_annihilation {k : ℕ} (s₀ : Fin k) (N : ℕ) :
    ∑ e : Grid k, (wGrid k e : ℝ) * (pGrid k e : ℝ) ^ k *
        (Ppoly k (s₀.val + 1)).eval (((N : ℝ) - (tGrid k e : ℝ)) / (pGrid k e : ℝ)) *
        rho k (N + rShift k (s₀.val + 1) e) = 0 := by
  let h := s₀.val + 1
  have hh_le : h ≤ k := s₀.isLt
  have hdegP : (Ppoly k h).natDegree ≤ k - h := Ppoly_natDegree_le hh_le
  -- Split the sum over Grid k along coordinate s₀ using Equiv.piSplitAt
  let equiv := (Equiv.piSplitAt s₀ (fun _ : Fin k => Fin (k + 2))).symm
  rw [← Fintype.sum_equiv equiv
    (fun pair =>
      let e := equiv pair
      (wGrid k e : ℝ) * (pGrid k e : ℝ) ^ k *
        (Ppoly k h).eval (((N : ℝ) - (tGrid k e : ℝ)) / (pGrid k e : ℝ)) *
        rho k (N + rShift k h e))
    (fun e =>
      (wGrid k e : ℝ) * (pGrid k e : ℝ) ^ k *
        (Ppoly k h).eval (((N : ℝ) - (tGrid k e : ℝ)) / (pGrid k e : ℝ)) *
        rho k (N + rShift k h e))
    (fun _ => rfl)]
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_eq_zero fun erest _ => ?_
  let e0 : Grid k := equiv (⟨0, by omega⟩, erest)
  have he_eq : ∀ m : Fin (k + 2), equiv (m, erest) = Function.update e0 s₀ m := by
    intro m
    ext s
    by_cases hs : s = s₀
    · subst hs
      simp [equiv, e0]
    · simp [equiv, e0, hs]
  have hrho_const : ∀ m : Fin (k + 2),
      rho k (N + rShift k h (equiv (m, erest))) = rho k (N + rShift k h e0) := by
    intro m
    rw [he_eq m]
    congr 2
    exact rShift_update_eq k s₀ e0 m
  -- Factor out the s ≠ s₀ part of wGrid
  let wRest : ℝ := ∏ s ∈ Finset.univ.erase s₀,
    ((-1 : ℝ) ^ (e0 s).val * ((k + 1).choose (e0 s).val : ℝ))
  have hw_factor : ∀ m : Fin (k + 2),
      (wGrid k (equiv (m, erest)) : ℝ) =
        ((-1 : ℝ) ^ m.val * ((k + 1).choose m.val : ℝ)) * wRest := by
    intro m
    rw [he_eq m]
    unfold wGrid
    push_cast
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ s₀)]
    rw [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun s hs => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
  -- Express pGrid^k * Ppoly((N - tGrid) / pGrid) as a polynomial of degree ≤ k in m
  let pRest : ℝ := (P0grid k : ℝ) + ∑ s ∈ Finset.univ.erase s₀, (aStep k s : ℝ) * (e0 s).val
  let tRest : ℝ := ∑ s ∈ Finset.univ.erase s₀, ((s.val + 1 : ℕ) : ℝ) * (aStep k s : ℝ) * (e0 s).val
  let pPoly : Polynomial ℝ := C pRest + C (aStep k s₀ : ℝ) * X
  let ntPoly : Polynomial ℝ := C ((N : ℝ) - tRest) - C ((h : ℝ) * (aStep k s₀ : ℝ)) * X
  have hp_eval : ∀ m : Fin (k + 2), (pGrid k (equiv (m, erest)) : ℝ) = pPoly.eval (m.val : ℝ) := by
    intro m
    rw [he_eq m]
    unfold pGrid
    push_cast
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s₀), Function.update_self]
    have hrest : ∑ s ∈ Finset.univ.erase s₀, (aStep k s : ℝ) * ((Function.update e0 s₀ m s).val : ℝ) =
        ∑ s ∈ Finset.univ.erase s₀, (aStep k s : ℝ) * (e0 s).val :=
      Finset.sum_congr rfl fun s hs => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
    rw [hrest]
    simp only [pPoly, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
    dsimp only [pRest]
    ring
  have hnt_eval : ∀ m : Fin (k + 2),
      (N : ℝ) - (tGrid k (equiv (m, erest)) : ℝ) = ntPoly.eval (m.val : ℝ) := by
    intro m
    rw [he_eq m]
    unfold tGrid
    push_cast
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s₀), Function.update_self]
    have hrest : ∑ s ∈ Finset.univ.erase s₀,
          (((s.val : ℝ) + 1) * (aStep k s : ℝ) * ((Function.update e0 s₀ m s).val : ℝ)) =
        tRest := by
      unfold tRest
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
      push_cast
      rfl
    rw [hrest]
    simp [ntPoly, h]
    ring
  let Fpoly : Polynomial ℝ :=
    ∑ j ∈ Finset.range (k + 1), C ((Ppoly k h).coeff j) * pPoly ^ (k - j) * ntPoly ^ j
  have hF_eval : ∀ m : Fin (k + 2),
      (pGrid k (equiv (m, erest)) : ℝ) ^ k *
        (Ppoly k h).eval (((N : ℝ) - (tGrid k (equiv (m, erest)) : ℝ)) /
          (pGrid k (equiv (m, erest)) : ℝ)) =
      Fpoly.eval (m.val : ℝ) := by
    intro m
    have hp_pos : (0 : ℝ) < pGrid k (equiv (m, erest)) := Nat.cast_pos.mpr (pGrid_pos k _)
    have hPeval : (Ppoly k h).eval (((N : ℝ) - (tGrid k (equiv (m, erest)) : ℝ)) /
          (pGrid k (equiv (m, erest)) : ℝ)) =
        ∑ j ∈ Finset.range (k + 1), (Ppoly k h).coeff j *
          (((N : ℝ) - (tGrid k (equiv (m, erest)) : ℝ)) / (pGrid k (equiv (m, erest)) : ℝ)) ^ j := by
      apply Polynomial.eval_eq_sum_range'
      omega
    rw [hPeval, Finset.mul_sum]
    simp only [Fpoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, ← hp_eval, ← hnt_eval]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjle : j ≤ k := by have := Finset.mem_range.mp hj; omega
    rw [div_pow]
    have hpow : (pGrid k (equiv (m, erest)) : ℝ) ^ k =
        (pGrid k (equiv (m, erest)) : ℝ) ^ (k - j) * (pGrid k (equiv (m, erest)) : ℝ) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hjle]
    rw [hpow]
    have hpj_ne : (pGrid k (equiv (m, erest)) : ℝ) ^ j ≠ 0 := (pow_pos hp_pos j).ne'
    field_simp [hpj_ne]
  have hF_deg : Fpoly = 0 ∨ Fpoly.natDegree < k + 1 := by
    right
    have hp_deg : pPoly.natDegree ≤ 1 := by
      refine le_trans (Polynomial.natDegree_add_le _ _)
        (max_le (by rw [Polynomial.natDegree_C]; omega) ?_)
      exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by rw [Polynomial.natDegree_X])
    have hnt_deg : ntPoly.natDegree ≤ 1 := by
      refine le_trans (Polynomial.natDegree_sub_le _ _)
        (max_le (by rw [Polynomial.natDegree_C]; omega) ?_)
      exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by rw [Polynomial.natDegree_X])
    have hterm_deg : ∀ j ∈ Finset.range (k + 1),
        (C ((Ppoly k h).coeff j) * pPoly ^ (k - j) * ntPoly ^ j).natDegree ≤ k := by
      intro j hj
      have hjle : j ≤ k := by have := Finset.mem_range.mp hj; omega
      have h1 : (pPoly ^ (k - j)).natDegree ≤ k - j :=
        le_trans (Polynomial.natDegree_pow_le) (by nlinarith)
      have h2 : (ntPoly ^ j).natDegree ≤ j :=
        le_trans (Polynomial.natDegree_pow_le) (by nlinarith)
      have h3 : (C ((Ppoly k h).coeff j) * pPoly ^ (k - j)).natDegree ≤ k - j :=
        le_trans (Polynomial.natDegree_C_mul_le _ _) h1
      exact le_trans (Polynomial.natDegree_mul_le) (by omega)
    have hsum_deg : Fpoly.natDegree ≤ k :=
      Polynomial.natDegree_sum_le_of_forall_le _ _ hterm_deg
    omega
  have hrew :
      ∑ m : Fin (k + 2),
        (wGrid k (equiv (m, erest)) : ℝ) * (pGrid k (equiv (m, erest)) : ℝ) ^ k *
          (Ppoly k h).eval (((N : ℝ) - (tGrid k (equiv (m, erest)) : ℝ)) /
            (pGrid k (equiv (m, erest)) : ℝ)) *
          rho k (N + rShift k h (equiv (m, erest))) =
      wRest * rho k (N + rShift k h e0) *
        ∑ m ∈ Finset.range (k + 2),
          ((-1 : ℝ) ^ m * ((k + 1).choose m : ℝ)) * Fpoly.eval (m : ℝ) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun m : ℕ => ((-1 : ℝ) ^ m * ((k + 1).choose m : ℝ)) * Fpoly.eval (m : ℝ)) (k + 2)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hw_factor m, hrho_const m, ← hF_eval m]
    ring
  rw [hrew, alt_binom_sum_poly_eq_zero (k + 1) Fpoly hF_deg, mul_zero]

/- ### Part 7: CRT progression and vanishing of `R(N)` -/

private lemma exists_crt_list :
    ∀ (L : List (ℕ × ℕ)),
      (∀ p ∈ L, 0 < p.2) →
      L.Pairwise (fun a b => Nat.Coprime a.2 b.2) →
      ∃ A : ℕ, ∀ p ∈ L, A ≡ p.1 [MOD p.2]
  | [], _, _ => ⟨0, by simp⟩
  | (r, m) :: rest, hpos, hpair => by
    have hpair' := List.pairwise_cons.mp hpair
    have hpos_rest : ∀ p ∈ rest, 0 < p.2 := fun p hp => hpos p (List.mem_cons_of_mem _ hp)
    obtain ⟨A0, hA0⟩ := exists_crt_list rest hpos_rest hpair'.2
    let M : ℕ := (rest.map Prod.snd).prod
    have hcop : Nat.Coprime m M := by
      have hcop_all : ∀ q ∈ rest.map Prod.snd, Nat.Coprime m q := by
        intro q hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        exact hpair'.1 p hp
      have hcop_prod : ∀ qs : List ℕ, (∀ q ∈ qs, Nat.Coprime m q) → Nat.Coprime m qs.prod := by
        intro qs
        induction qs with
        | nil => intro _; simp
        | cons a as ih =>
          intro hq
          rw [List.prod_cons]
          exact (hq a (List.mem_cons_self ..)).mul_right
            (ih fun q hq' => hq q (List.mem_cons_of_mem _ hq'))
      exact hcop_prod (rest.map Prod.snd) hcop_all
    let cr := Nat.chineseRemainder hcop r A0
    refine ⟨cr.val, fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact cr.property.1
    · have hdvd : p.2 ∣ M := List.dvd_prod (List.mem_map_of_mem hp')
      exact (cr.property.2.of_dvd hdvd).trans (hA0 p hp')

private noncomputable def Rcomb (k N : ℕ) : ℝ :=
  ∑ e : Grid k, ∑ h ∈ Finset.Icc 1 (k + 1),
    (wGrid k e : ℝ) * cConst k h * (pGrid k e : ℝ) ^ (k + 1) * rho k (N + rShift k h e)

private lemma Rcomb_tendsto_zero {k : ℕ} (hk : 1 ≤ k) {q : ℚ}
    (hq : (q : ℝ) = Erdos252.erdos_252_sum k) :
    ∃ (A Q : ℕ), 0 < Q ∧
      Tendsto (fun m : ℕ => Rcomb k (A + m * Q)) atTop (nhds 0) := by
  let L : List (ℕ × ℕ) := (Finset.univ : Finset (Grid k)).toList.map
    (fun e => (tGrid k e, (pGrid k e) ^ 2))
  have hpos : ∀ p ∈ L, 0 < p.2 := by
    intro p hp
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hp
    exact pow_pos (pGrid_pos k e) 2
  have hnodup : (Finset.univ : Finset (Grid k)).toList.Nodup := Finset.nodup_toList _
  have hpair : L.Pairwise (fun a b => Nat.Coprime a.2 b.2) := by
    rw [List.pairwise_map]
    exact hnodup.imp fun {e₁ e₂} hne =>
      ((pGrid_pairwise_coprime k hne).pow_left 2).pow_right 2
  obtain ⟨A, hA⟩ := exists_crt_list L hpos hpair
  let Q : ℕ := ∏ e : Grid k, (pGrid k e) ^ 2
  have hQpos : 0 < Q := Finset.prod_pos fun e _ => pow_pos (pGrid_pos k e) 2
  have hA_mod : ∀ e : Grid k, A ≡ tGrid k e [MOD (pGrid k e) ^ 2] := by
    intro e
    apply hA (tGrid k e, (pGrid k e) ^ 2)
    exact List.mem_map.mpr ⟨e, Finset.mem_toList.mpr (Finset.mem_univ e), rfl⟩
  refine ⟨A, Q, hQpos, ?_⟩
  -- Build uniform O(1 / √N) bound on |W(N) - Rcomb(N)/N|
  have hRem : ∀ h ∈ Finset.Icc 1 (k + 1), ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      |(Rpoly k h).eval (n : ℝ) / ((n : ℝ) * ∏ j ∈ Finset.Icc 1 h, ((n : ℝ) + (j : ℝ)))| ≤
        C / (n : ℝ) ^ 2 :=
    fun h hh => Rpoly_remainder_bound k h (Finset.mem_Icc.mp hh).1
  let CR : ℕ → ℝ := fun h => if hh : h ∈ Finset.Icc 1 (k + 1) then (hRem h hh).choose else 0
  have hCR_nonneg : ∀ h ∈ Finset.Icc 1 (k + 1), 0 ≤ CR h := by
    intro h hh; simp only [CR, dif_pos hh]; exact (hRem h hh).choose_spec.1
  have hCR_bound : ∀ h ∈ Finset.Icc 1 (k + 1), ∀ n : ℕ, 1 ≤ n →
      |(Rpoly k h).eval (n : ℝ) / ((n : ℝ) * ∏ j ∈ Finset.Icc 1 h, ((n : ℝ) + (j : ℝ)))| ≤
        CR h / (n : ℝ) ^ 2 := by
    intro h hh; simp only [CR, dif_pos hh]; exact (hRem h hh).choose_spec.2
  -- Choose threshold N0 large enough that for all e and N ≥ N0:
  --   N ≥ 2 * tGrid k e, n_e = (N - t_e) / p_e ≥ max q.den (2^(k+2)), N ≥ 2 * rShift
  let maxP : ℕ := (Finset.univ : Finset (Grid k)).sup (pGrid k)
  let maxT : ℕ := (Finset.univ : Finset (Grid k)).sup (tGrid k)
  let maxR : ℕ := (Finset.univ : Finset (Grid k)).sup (fun e => rShift k (k + 1) e)
  have hmaxP_pos : 0 < maxP := by
    have h1 := pGrid_pos k (eStar k)
    have h2 : pGrid k (eStar k) ≤ maxP := Finset.le_sup (Finset.mem_univ _)
    omega
  let N0 : ℕ := max (2 * maxT + 2 * maxR + 2) (maxT + maxP * (max q.den (2 ^ (k + 2)) + 1))
  -- Main error constant C_err so |W(N) - Rcomb(N) / N| ≤ C_err / (N * √N) for N ≡ A [MOD Q], N ≥ N0
  let C_err : ℝ := ∑ e : Grid k, |(wGrid k e : ℝ)| * (σ k (pGrid k e) : ℝ) *
    ((2 : ℝ) ^ (k + 3) * (2 * (pGrid k e : ℝ)) ^ 2 +
      ∑ h ∈ Finset.Icc 1 (k + 1),
        (CR h * (2 * (pGrid k e : ℝ)) ^ 2 * (4 * Real.sqrt 2) +
          |cConst k h| * (pGrid k e : ℝ) * (2 * (tGrid k e : ℝ)) * (4 * Real.sqrt 2)))
  have hC_err_nonneg : 0 ≤ C_err := by
    refine Finset.sum_nonneg fun e _ => mul_nonneg (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) ?_
    refine add_nonneg (by positivity) (Finset.sum_nonneg fun h hh => add_nonneg ?_ ?_)
    · have := hCR_nonneg h hh; positivity
    · positivity
  have hW_approx : ∀ N : ℕ, N0 ≤ N → (∀ e : Grid k, N ≡ tGrid k e [MOD (pGrid k e) ^ 2]) →
      ∃ z : ℤ, |(z : ℝ) - Rcomb k N / (N : ℝ)| ≤ C_err / ((N : ℝ) * Real.sqrt (N : ℝ)) := by
    intro N hN hNmod
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN_pos
    let nOf : Grid k → ℕ := fun e => (N - tGrid k e) / pGrid k e
    have hn_prop : ∀ e : Grid k,
        pGrid k e ∣ nOf e ∧
        pGrid k e * nOf e = N - tGrid k e ∧
        max q.den (2 ^ (k + 2)) ≤ nOf e ∧
        (N : ℝ) / (2 * (pGrid k e : ℝ)) ≤ (nOf e : ℝ) ∧
        (nOf e : ℝ) ≤ (N : ℝ) / (pGrid k e : ℝ) := by
      intro e
      have ht_le : tGrid k e ≤ maxT := Finset.le_sup (f := tGrid k) (Finset.mem_univ e)
      have hp_le : pGrid k e ≤ maxP := Finset.le_sup (f := pGrid k) (Finset.mem_univ e)
      have hp_pos : 0 < pGrid k e := pGrid_pos k e
      have hN_ge_t : tGrid k e ≤ N := by omega
      have hdvd2 : (pGrid k e) ^ 2 ∣ (N - tGrid k e) := by
        have hmod := hNmod e
        exact (Nat.modEq_iff_dvd' hN_ge_t).mp hmod.symm
      obtain ⟨u, hu⟩ := hdvd2
      have hne_eq : nOf e = pGrid k e * u := by
        dsimp [nOf]
        rw [hu, sq, mul_assoc, Nat.mul_div_cancel_left _ hp_pos]
      have hmul : pGrid k e * nOf e = N - tGrid k e := by
        rw [hne_eq, ← mul_assoc, ← sq, hu]
      have hn_ge : max q.den (2 ^ (k + 2)) ≤ nOf e := by
        have h0 : pGrid k e * max q.den (2 ^ (k + 2)) ≤
            pGrid k e * (max q.den (2 ^ (k + 2)) + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
        have h1 : pGrid k e * (max q.den (2 ^ (k + 2)) + 1) ≤
            maxP * (max q.den (2 ^ (k + 2)) + 1) := Nat.mul_le_mul_right _ hp_le
        have h2 : maxT + maxP * (max q.den (2 ^ (k + 2)) + 1) ≤ N :=
          le_trans (le_max_right _ _) hN
        have h3 : pGrid k e * max q.den (2 ^ (k + 2)) ≤ pGrid k e * nOf e := by
          rw [hmul]; omega
        exact Nat.le_of_mul_le_mul_left h3 hp_pos
      have hN_half : (N : ℝ) / 2 ≤ ((N - tGrid k e : ℕ) : ℝ) := by
        have : 2 * maxT ≤ N := by
          have := le_trans (le_max_left _ _) hN; omega
        have hnat : N ≤ 2 * (N - tGrid k e) := by omega
        have hreal : (N : ℝ) ≤ 2 * ((N - tGrid k e : ℕ) : ℝ) := by exact_mod_cast hnat
        linarith
      have hcast_eq : (pGrid k e : ℝ) * (nOf e : ℝ) = ((N - tGrid k e : ℕ) : ℝ) := by
        exact_mod_cast hmul
      have hp_posR : (0 : ℝ) < pGrid k e := Nat.cast_pos.mpr hp_pos
      have hlb : (N : ℝ) / (2 * (pGrid k e : ℝ)) ≤ (nOf e : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      have hub : (nOf e : ℝ) ≤ (N : ℝ) / (pGrid k e : ℝ) := by
        rw [le_div_iff₀ hp_posR]
        have : ((N - tGrid k e : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N (tGrid k e)
        linarith
      exact ⟨⟨u, hne_eq⟩, hmul, hn_ge, hlb, hub⟩
    have hT_int : ∀ e : Grid k, ∃ z : ℤ, tailT k (nOf e) = (z : ℝ) := fun e =>
      tailT_isInt hq (le_trans (le_max_left _ _) (hn_prop e).2.2.1)
    let zOf : Grid k → ℤ := fun e => (hT_int e).choose
    have hzOf : ∀ e : Grid k, tailT k (nOf e) = (zOf e : ℝ) := fun e => (hT_int e).choose_spec
    let Wint : ℤ := ∑ e : Grid k, wGrid k e * (σ k (pGrid k e) : ℤ) * zOf e
    refine ⟨Wint, ?_⟩
    have hW_eq : (Wint : ℝ) = ∑ e : Grid k, (wGrid k e : ℝ) * (σ k (pGrid k e) : ℝ) * tailT k (nOf e) := by
      unfold Wint
      push_cast
      refine Finset.sum_congr rfl fun e _ => by rw [hzOf e]
    rw [hW_eq]
    -- For each e and h ∈ [1, k+1], prove σ_k(p_e) * σ_k(n_e + h) / ∏ = p_e^k * (...) * ρ_k(N + r_h(e))
    have hmain_id : ∀ e : Grid k, ∀ h ∈ Finset.Icc 1 (k + 1),
        (σ k (pGrid k e) : ℝ) * ((σ k (nOf e + h) : ℝ) /
            ∏ j ∈ Finset.Icc 1 h, ((nOf e : ℝ) + (j : ℝ))) =
          (pGrid k e : ℝ) ^ k * (Ppoly k h).eval (((N : ℝ) - (tGrid k e : ℝ)) / (pGrid k e : ℝ)) *
            rho k (N + rShift k h e) +
          cConst k h * (pGrid k e : ℝ) ^ (k + 1) / (N : ℝ) * rho k (N + rShift k h e) +
          (σ k (pGrid k e) : ℝ) *
            ((Rpoly k h).eval (nOf e : ℝ) /
                ((nOf e : ℝ) * ∏ j ∈ Finset.Icc 1 h, ((nOf e : ℝ) + (j : ℝ))) *
              rho k (nOf e + h) +
              cConst k h * (1 / (nOf e : ℝ) - (pGrid k e : ℝ) / (N : ℝ)) * rho k (nOf e + h)) := by
      intro e h hh
      have hh1 : 1 ≤ h := (Finset.mem_Icc.mp hh).1
      have hh2 : h ≤ k + 1 := (Finset.mem_Icc.mp hh).2
      have hnp := hn_prop e
      have hn1 : 1 ≤ nOf e := by
        have : 1 ≤ 2 ^ (k + 2) := Nat.one_le_pow _ _ (by decide)
        have := le_trans (le_max_right _ _) hnp.2.2.1
        omega
      have hp_pos : 0 < pGrid k e := pGrid_pos k e
      have hp_posR : (0 : ℝ) < pGrid k e := Nat.cast_pos.mpr hp_pos
      have hcop : Nat.Coprime (pGrid k e) (nOf e + h) := by
        obtain ⟨u, hu⟩ := hnp.1
        rw [hu, Nat.coprime_mul_left_add_right]
        exact pGrid_coprime_small hk hh1 hh2 e
      have hprod_arg : pGrid k e * (nOf e + h) = N + rShift k h e := by
        have ht_le_N : tGrid k e ≤ N := by
          have : tGrid k e ≤ maxT := Finset.le_sup (f := tGrid k) (Finset.mem_univ e)
          have := le_trans (le_max_left _ _) hN; omega
        have ht_lt_hp : tGrid k e < h * pGrid k e := by
          have := tGrid_lt_pGrid k e
          have : pGrid k e ≤ h * pGrid k e := Nat.le_mul_of_pos_left _ hh1
          omega
        unfold rShift
        rw [mul_add, hnp.2.1, mul_comm (pGrid k e) h]
        omega
      have hrho_prod : (σ k (pGrid k e) : ℝ) * rho k (nOf e + h) =
          (pGrid k e : ℝ) ^ k * rho k (N + rShift k h e) := by
        rw [← hprod_arg, rho_mul_of_coprime hp_pos (by omega) hcop]
        unfold rho
        simp only [hp_pos.ne', ↓reduceIte]
        have hpk_ne : (pGrid k e : ℝ) ^ k ≠ 0 := (pow_pos hp_posR k).ne'
        field_simp [hpk_ne]
      have hsig_nh : (σ k (nOf e + h) : ℝ) = ((nOf e : ℝ) + (h : ℝ)) ^ k * rho k (nOf e + h) := by
        unfold rho
        have hpos_nh : 0 < nOf e + h := by omega
        simp only [hpos_nh.ne', ↓reduceIte]
        push_cast
        have hne : ((nOf e : ℝ) + (h : ℝ)) ^ k ≠ 0 := by positivity
        field_simp [hne]
      have hne_eq_R : (nOf e : ℝ) = ((N : ℝ) - (tGrid k e : ℝ)) / (pGrid k e : ℝ) := by
        have ht_le_N : tGrid k e ≤ N := by
          have : tGrid k e ≤ maxT := Finset.le_sup (f := tGrid k) (Finset.mem_univ e)
          have := le_trans (le_max_left _ _) hN; omega
        have h1 : (pGrid k e : ℝ) * (nOf e : ℝ) = (N : ℝ) - (tGrid k e : ℝ) := by
          have : (pGrid k e : ℝ) * (nOf e : ℝ) = ((N - tGrid k e : ℕ) : ℝ) := by exact_mod_cast hnp.2.1
          rw [this, Nat.cast_sub ht_le_N]
        rw [eq_div_iff hp_posR.ne', mul_comm, h1]
      rw [hsig_nh,
        show (σ k (pGrid k e) : ℝ) * (((nOf e : ℝ) + (h : ℝ)) ^ k * rho k (nOf e + h) /
            ∏ j ∈ Finset.Icc 1 h, ((nOf e : ℝ) + (j : ℝ))) =
          (σ k (pGrid k e) : ℝ) * ((((nOf e : ℝ) + (h : ℝ)) ^ k /
            ∏ j ∈ Finset.Icc 1 h, ((nOf e : ℝ) + (j : ℝ))) * rho k (nOf e + h)) by ring,
        rational_weight_decomp hn1, ← hne_eq_R]
      have halg : (σ k (pGrid k e) : ℝ) *
            (((Ppoly k h).eval (nOf e : ℝ) + cConst k h / (nOf e : ℝ) +
              (Rpoly k h).eval (nOf e : ℝ) /
                ((nOf e : ℝ) * ∏ j ∈ Finset.Icc 1 h, ((nOf e : ℝ) + (j : ℝ)))) *
              rho k (nOf e + h)) =
          (Ppoly k h).eval (nOf e : ℝ) * ((σ k (pGrid k e) : ℝ) * rho k (nOf e + h)) +
          cConst k h * ((pGrid k e : ℝ) / (N : ℝ)) * ((σ k (pGrid k e) : ℝ) * rho k (nOf e + h)) +
          (σ k (pGrid k e) : ℝ) *
            ((Rpoly k h).eval (nOf e : ℝ) /
                ((nOf e : ℝ) * ∏ j ∈ Finset.Icc 1 h, ((nOf e : ℝ) + (j : ℝ))) *
              rho k (nOf e + h) +
              cConst k h * (1 / (nOf e : ℝ) - (pGrid k e : ℝ) / (N : ℝ)) * rho k (nOf e + h)) := by
        ring
      rw [halg, hrho_prod]
      rw [pow_succ]
      ring
    -- Sum of polynomial parts vanishes identically!
    have hpoly_zero :
        ∑ e : Grid k, ∑ h ∈ Finset.Icc 1 (k + 1),
          (wGrid k e : ℝ) * (pGrid k e : ℝ) ^ k *
            (Ppoly k h).eval (((N : ℝ) - (tGrid k e : ℝ)) / (pGrid k e : ℝ)) *
            rho k (N + rShift k h e) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun h hh => ?_
      have hh1 := (Finset.mem_Icc.mp hh).1
      have hh2 := (Finset.mem_Icc.mp hh).2
      by_cases htop : h = k + 1
      · subst htop
        simp [Ppoly_top]
      · have hlt : h - 1 < k := by omega
        have heq : (⟨h - 1, hlt⟩ : Fin k).val + 1 = h := by dsimp; omega
        rw [← heq]
        exact poly_part_annihilation ⟨h - 1, hlt⟩ N
    -- Combine W(N) - Rcomb(N) / N into tail + Rpoly + (1/n_e - p_e/N) errors
    have hdiff_eq :
        (∑ e : Grid k, (wGrid k e : ℝ) * (σ k (pGrid k e) : ℝ) * tailT k (nOf e)) -
          Rcomb k N / (N : ℝ) =
        ∑ e : Grid k, (wGrid k e : ℝ) * (σ k (pGrid k e) : ℝ) *
          ((tailT k (nOf e) - ∑ h ∈ Finset.Icc 1 (k + 1),
              (σ k (nOf e + h) : ℝ) / ∏ j ∈ Finset.Icc 1 h, ((nOf e : ℝ) + (j : ℝ))) +
            ∑ h ∈ Finset.Icc 1 (k + 1),
              ((Rpoly k h).eval (nOf e : ℝ) /
                  ((nOf e : ℝ) * ∏ j ∈ Finset.Icc 1 h, ((nOf e : ℝ) + (j : ℝ))) *
                rho k (nOf e + h) +
                cConst k h * (1 / (nOf e : ℝ) - (pGrid k e : ℝ) / (N : ℝ)) *
                rho k (nOf e + h))) := by
      have htrunc : ∀ e : Grid k,
          (wGrid k e : ℝ) * (σ k (pGrid k e) : ℝ) * tailT k (nOf e) =
          (wGrid k e : ℝ) * (σ k (pGrid k e) : ℝ) *
            (tailT k (nOf e) - ∑ h ∈ Finset.Icc 1 (k + 1),
              (σ k (nOf e + h) : ℝ) / ∏ j ∈ Finset.Icc 1 h, ((nOf e : ℝ) + (j : ℝ))) +
          ∑ h ∈ Finset.Icc 1 (k + 1),
            (wGrid k e : ℝ) * ((σ k (pGrid k e) : ℝ) *
              ((σ k (nOf e + h) : ℝ) / ∏ j ∈ Finset.Icc 1 h, ((nOf e : ℝ) + (j : ℝ)))) := by
        intro e
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring
      have hsum_all :
          ∑ e : Grid k, (wGrid k e : ℝ) * (σ k (pGrid k e) : ℝ) * tailT k (nOf e) =
          (∑ e : Grid k, (wGrid k e : ℝ) * (σ k (pGrid k e) : ℝ) *
            ((tailT k (nOf e) - ∑ h ∈ Finset.Icc 1 (k + 1),
                (σ k (nOf e + h) : ℝ) / ∏ j ∈ Finset.Icc 1 h, ((nOf e : ℝ) + (j : ℝ))) +
              ∑ h ∈ Finset.Icc 1 (k + 1),
                ((Rpoly k h).eval (nOf e : ℝ) /
                    ((nOf e : ℝ) * ∏ j ∈ Finset.Icc 1 h, ((nOf e : ℝ) + (j : ℝ))) *
                  rho k (nOf e + h) +
                  cConst k h * (1 / (nOf e : ℝ) - (pGrid k e : ℝ) / (N : ℝ)) *
                  rho k (nOf e + h)))) +
          (∑ e : Grid k, ∑ h ∈ Finset.Icc 1 (k + 1),
            (wGrid k e : ℝ) * (pGrid k e : ℝ) ^ k *
              (Ppoly k h).eval (((N : ℝ) - (tGrid k e : ℝ)) / (pGrid k e : ℝ)) *
              rho k (N + rShift k h e)) +
          Rcomb k N / (N : ℝ) := by
        unfold Rcomb
        rw [Finset.sum_div]
        simp_rw [Finset.sum_div, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [htrunc e]
        have hinner : ∑ h ∈ Finset.Icc 1 (k + 1),
              (wGrid k e : ℝ) * ((σ k (pGrid k e) : ℝ) *
                ((σ k (nOf e + h) : ℝ) / ∏ j ∈ Finset.Icc 1 h, ((nOf e : ℝ) + (j : ℝ)))) =
            (∑ h ∈ Finset.Icc 1 (k + 1),
              (wGrid k e : ℝ) * (pGrid k e : ℝ) ^ k *
                (Ppoly k h).eval (((N : ℝ) - (tGrid k e : ℝ)) / (pGrid k e : ℝ)) *
                rho k (N + rShift k h e)) +
            (∑ h ∈ Finset.Icc 1 (k + 1),
              (wGrid k e : ℝ) * cConst k h * (pGrid k e : ℝ) ^ (k + 1) *
                rho k (N + rShift k h e) / (N : ℝ)) +
            (∑ h ∈ Finset.Icc 1 (k + 1),
              (wGrid k e : ℝ) * (σ k (pGrid k e) : ℝ) *
                ((Rpoly k h).eval (nOf e : ℝ) /
                    ((nOf e : ℝ) * ∏ j ∈ Finset.Icc 1 h, ((nOf e : ℝ) + (j : ℝ))) *
                  rho k (nOf e + h) +
                  cConst k h * (1 / (nOf e : ℝ) - (pGrid k e : ℝ) / (N : ℝ)) *
                  rho k (nOf e + h))) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun h hh => ?_
          rw [hmain_id e h hh]
          ring
        rw [hinner, mul_add, Finset.mul_sum]
        ring
      rw [hsum_all, hpoly_zero]
      ring
    rw [hdiff_eq]
    -- Bound each e-term by its corresponding term in C_err / (N * √N)
    rw [show C_err / ((N : ℝ) * Real.sqrt (N : ℝ)) =
        ∑ e : Grid k, |(wGrid k e : ℝ)| * (σ k (pGrid k e) : ℝ) *
          ((2 : ℝ) ^ (k + 3) * (2 * (pGrid k e : ℝ)) ^ 2 +
            ∑ h ∈ Finset.Icc 1 (k + 1),
              (CR h * (2 * (pGrid k e : ℝ)) ^ 2 * (4 * Real.sqrt 2) +
                |cConst k h| * (pGrid k e : ℝ) * (2 * (tGrid k e : ℝ)) * (4 * Real.sqrt 2))) /
          ((N : ℝ) * Real.sqrt (N : ℝ)) by unfold C_err; rw [Finset.sum_div]]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun e _ => ?_)
    have hnp := hn_prop e
    have hp_pos : (0 : ℝ) < pGrid k e := Nat.cast_pos.mpr (pGrid_pos k e)
    have hn_ge_pow : 2 ^ (k + 2) ≤ nOf e := le_trans (le_max_right _ _) hnp.2.2.1
    have hn1 : 1 ≤ nOf e := by
      have : 1 ≤ 2 ^ (k + 2) := Nat.one_le_pow _ _ (by decide)
      omega
    have hn_pos : (0 : ℝ) < nOf e := Nat.cast_pos.mpr hn1
    have hinv_n : 1 / (nOf e : ℝ) ≤ (2 * (pGrid k e : ℝ)) / (N : ℝ) := by
      rw [div_le_div_iff₀ hn_pos hN_pos, one_mul]
      have h1 := hnp.2.2.2.1
      rw [div_le_iff₀ (by positivity)] at h1
      linarith
    have hinv_nsqrt : 1 / ((nOf e : ℝ) * Real.sqrt (nOf e : ℝ)) ≤
        (2 * (pGrid k e : ℝ)) ^ 2 / ((N : ℝ) * Real.sqrt (N : ℝ)) := by
      have h2p_ge1 : (1 : ℝ) ≤ 2 * (pGrid k e : ℝ) := by
        have : (1 : ℝ) ≤ pGrid k e := by exact_mod_cast pGrid_pos k e
        linarith
      have hsqrt_lb : Real.sqrt (N : ℝ) / (2 * (pGrid k e : ℝ)) ≤ Real.sqrt (nOf e : ℝ) := by
        have h1 : Real.sqrt ((N : ℝ) / (2 * (pGrid k e : ℝ))) ≤ Real.sqrt (nOf e : ℝ) :=
          Real.sqrt_le_sqrt hnp.2.2.2.1
        rw [Real.sqrt_div hN_pos.le] at h1
        have hsq : Real.sqrt (2 * (pGrid k e : ℝ)) ≤ 2 * (pGrid k e : ℝ) := by
          calc Real.sqrt (2 * (pGrid k e : ℝ))
              ≤ Real.sqrt ((2 * (pGrid k e : ℝ)) * (2 * (pGrid k e : ℝ))) :=
                Real.sqrt_le_sqrt (le_mul_of_one_le_right (by positivity) h2p_ge1)
            _ = 2 * (pGrid k e : ℝ) := Real.sqrt_mul_self (by positivity)
        exact le_trans (div_le_div_of_nonneg_left hsqrtN_pos.le
          (Real.sqrt_pos.mpr (by positivity)) hsq) h1
      have hprod : ((N : ℝ) * Real.sqrt (N : ℝ)) / (2 * (pGrid k e : ℝ)) ^ 2 ≤
          (nOf e : ℝ) * Real.sqrt (nOf e : ℝ) := by
        calc ((N : ℝ) * Real.sqrt (N : ℝ)) / (2 * (pGrid k e : ℝ)) ^ 2
            = ((N : ℝ) / (2 * (pGrid k e : ℝ))) * (Real.sqrt (N : ℝ) / (2 * (pGrid k e : ℝ))) := by
              ring
          _ ≤ (nOf e : ℝ) * Real.sqrt (nOf e : ℝ) :=
              mul_le_mul hnp.2.2.2.1 hsqrt_lb (by positivity) hn_pos.le
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      rw [div_le_iff₀ (by positivity)] at hprod
      linarith
    have htail_bd : |tailT k (nOf e) - ∑ h ∈ Finset.Icc 1 (k + 1),
          (σ k (nOf e + h) : ℝ) / ∏ j ∈ Finset.Icc 1 h, ((nOf e : ℝ) + (j : ℝ))| ≤
        (2 : ℝ) ^ (k + 3) * (2 * (pGrid k e : ℝ)) ^ 2 / ((N : ℝ) * Real.sqrt (N : ℝ)) := by
      calc |tailT k (nOf e) - _|
          ≤ (2 : ℝ) ^ (k + 3) / ((nOf e : ℝ) * Real.sqrt (nOf e : ℝ)) :=
            tailT_truncation_bound hk hn_ge_pow
        _ = (2 : ℝ) ^ (k + 3) * (1 / ((nOf e : ℝ) * Real.sqrt (nOf e : ℝ))) := by ring
        _ ≤ (2 : ℝ) ^ (k + 3) * ((2 * (pGrid k e : ℝ)) ^ 2 / ((N : ℝ) * Real.sqrt (N : ℝ))) :=
            mul_le_mul_of_nonneg_left hinv_nsqrt (by positivity)
        _ = (2 : ℝ) ^ (k + 3) * (2 * (pGrid k e : ℝ)) ^ 2 / ((N : ℝ) * Real.sqrt (N : ℝ)) := by ring
    have hrho_nh_bd : ∀ h ∈ Finset.Icc 1 (k + 1),
        rho k (nOf e + h) ≤ (4 * Real.sqrt 2) * Real.sqrt (N : ℝ) := by
      intro h hh
      have hh2 := (Finset.mem_Icc.mp hh).2
      have hnh_le : (nOf e + h : ℝ) ≤ 2 * (N : ℝ) := by
        have h1 : (nOf e : ℝ) ≤ (N : ℝ) := by
          calc (nOf e : ℝ) ≤ (N : ℝ) / (pGrid k e : ℝ) := hnp.2.2.2.2
            _ ≤ (N : ℝ) / 1 := div_le_div_of_nonneg_left hN_pos.le zero_lt_one
                (by exact_mod_cast pGrid_pos k e)
            _ = (N : ℝ) := div_one _
        have h2 : (h : ℝ) ≤ (N : ℝ) := by
          have h2pow : k + 1 ≤ 2 ^ (k + 2) := by
            have : k + 2 < 2 ^ (k + 2) := Nat.lt_two_pow_self; omega
          have : h ≤ nOf e := by omega
          exact le_trans (by exact_mod_cast this) h1
        linarith
      calc rho k (nOf e + h) ≤ 2 * Real.sqrt ((nOf e + h : ℕ) : ℝ) :=
            rho_le_two_sqrt hk (by omega)
        _ = 2 * Real.sqrt ((nOf e : ℝ) + (h : ℝ)) := by push_cast; rfl
        _ ≤ 2 * Real.sqrt (2 * (N : ℝ)) := by gcongr
        _ = 2 * (Real.sqrt 2 * Real.sqrt (N : ℝ)) := by rw [Real.sqrt_mul (by norm_num)]
        _ ≤ (4 * Real.sqrt 2) * Real.sqrt (N : ℝ) := by
            have : 0 ≤ Real.sqrt 2 * Real.sqrt (N : ℝ) := by positivity
            linarith
    have hdiff_inv : |1 / (nOf e : ℝ) - (pGrid k e : ℝ) / (N : ℝ)| ≤
        (pGrid k e : ℝ) * (2 * (tGrid k e : ℝ)) / (N : ℝ) ^ 2 := by
      have ht_le_N : tGrid k e ≤ N := by
        have : tGrid k e ≤ maxT := Finset.le_sup (f := tGrid k) (Finset.mem_univ e)
        have := le_trans (le_max_left _ _) hN; omega
      have h1 : (pGrid k e : ℝ) * (nOf e : ℝ) = (N : ℝ) - (tGrid k e : ℝ) := by
        have : (pGrid k e : ℝ) * (nOf e : ℝ) = ((N - tGrid k e : ℕ) : ℝ) := by exact_mod_cast hnp.2.1
        rw [this, Nat.cast_sub ht_le_N]
      have hsub_eq : 1 / (nOf e : ℝ) - (pGrid k e : ℝ) / (N : ℝ) =
          (pGrid k e : ℝ) * (tGrid k e : ℝ) / ((N : ℝ) * ((pGrid k e : ℝ) * (nOf e : ℝ))) := by
        have hpne : (pGrid k e : ℝ) ≠ 0 := hp_pos.ne'
        field_simp [hn_pos.ne', hN_pos.ne', hpne]
        linarith
      rw [hsub_eq, abs_of_nonneg (by positivity)]
      have hden_lb : (N : ℝ) / 2 ≤ (pGrid k e : ℝ) * (nOf e : ℝ) := by
        have h1' := hnp.2.2.2.1
        rw [div_le_iff₀ (by positivity)] at h1'
        linarith
      calc (pGrid k e : ℝ) * (tGrid k e : ℝ) / ((N : ℝ) * ((pGrid k e : ℝ) * (nOf e : ℝ)))
          ≤ (pGrid k e : ℝ) * (tGrid k e : ℝ) / ((N : ℝ) * ((N : ℝ) / 2)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity)
              (mul_le_mul_of_nonneg_left hden_lb hN_pos.le)
        _ = (pGrid k e : ℝ) * (2 * (tGrid k e : ℝ)) / (N : ℝ) ^ 2 := by field_simp [hN_pos.ne']
    have hsqrt_div_sq : Real.sqrt (N : ℝ) / (N : ℝ) ^ 2 = 1 / ((N : ℝ) * Real.sqrt (N : ℝ)) := by
      have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hN_pos.le
      field_simp [hN_pos.ne', hsqrtN_pos.ne']
      nlinarith [hsq]
    have hsum_h_bd :
        |∑ h ∈ Finset.Icc 1 (k + 1),
            ((Rpoly k h).eval (nOf e : ℝ) /
                ((nOf e : ℝ) * ∏ j ∈ Finset.Icc 1 h, ((nOf e : ℝ) + (j : ℝ))) *
              rho k (nOf e + h) +
              cConst k h * (1 / (nOf e : ℝ) - (pGrid k e : ℝ) / (N : ℝ)) *
              rho k (nOf e + h))| ≤
        (∑ h ∈ Finset.Icc 1 (k + 1),
            (CR h * (2 * (pGrid k e : ℝ)) ^ 2 * (4 * Real.sqrt 2) +
              |cConst k h| * (pGrid k e : ℝ) * (2 * (tGrid k e : ℝ)) * (4 * Real.sqrt 2))) /
          ((N : ℝ) * Real.sqrt (N : ℝ)) := by
      rw [Finset.sum_div]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun h hh => ?_)
      have hrho_nn : 0 ≤ rho k (nOf e + h) := rho_nonneg k _
      have hRbd : |(Rpoly k h).eval (nOf e : ℝ) /
            ((nOf e : ℝ) * ∏ j ∈ Finset.Icc 1 h, ((nOf e : ℝ) + (j : ℝ)))| ≤
          CR h * (2 * (pGrid k e : ℝ)) ^ 2 / (N : ℝ) ^ 2 := by
        have h1 := hCR_bound h hh (nOf e) hn1
        have h2 : 1 / (nOf e : ℝ) ^ 2 ≤ (2 * (pGrid k e : ℝ)) ^ 2 / (N : ℝ) ^ 2 := by
          rw [show (1 : ℝ) / (nOf e : ℝ) ^ 2 = (1 / (nOf e : ℝ)) ^ 2 by rw [div_pow, one_pow],
            ← div_pow]
          exact pow_le_pow_left₀ (by positivity) hinv_n 2
        calc |(Rpoly k h).eval (nOf e : ℝ) / _| ≤ CR h / (nOf e : ℝ) ^ 2 := h1
          _ = CR h * (1 / (nOf e : ℝ) ^ 2) := by ring
          _ ≤ CR h * ((2 * (pGrid k e : ℝ)) ^ 2 / (N : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_left h2 (hCR_nonneg h hh)
          _ = CR h * (2 * (pGrid k e : ℝ)) ^ 2 / (N : ℝ) ^ 2 := by ring
      have hterm1 : |(Rpoly k h).eval (nOf e : ℝ) /
            ((nOf e : ℝ) * ∏ j ∈ Finset.Icc 1 h, ((nOf e : ℝ) + (j : ℝ))) *
            rho k (nOf e + h)| ≤
          CR h * (2 * (pGrid k e : ℝ)) ^ 2 * (4 * Real.sqrt 2) / ((N : ℝ) * Real.sqrt (N : ℝ)) := by
        rw [abs_mul, abs_of_nonneg hrho_nn]
        calc _ ≤ (CR h * (2 * (pGrid k e : ℝ)) ^ 2 / (N : ℝ) ^ 2) *
              ((4 * Real.sqrt 2) * Real.sqrt (N : ℝ)) :=
              mul_le_mul hRbd (hrho_nh_bd h hh) hrho_nn (by have := hCR_nonneg h hh; positivity)
          _ = CR h * (2 * (pGrid k e : ℝ)) ^ 2 * (4 * Real.sqrt 2) *
              (Real.sqrt (N : ℝ) / (N : ℝ) ^ 2) := by ring
          _ = CR h * (2 * (pGrid k e : ℝ)) ^ 2 * (4 * Real.sqrt 2) /
              ((N : ℝ) * Real.sqrt (N : ℝ)) := by rw [hsqrt_div_sq]; ring
      have hterm2 : |cConst k h * (1 / (nOf e : ℝ) - (pGrid k e : ℝ) / (N : ℝ)) *
            rho k (nOf e + h)| ≤
          |cConst k h| * (pGrid k e : ℝ) * (2 * (tGrid k e : ℝ)) * (4 * Real.sqrt 2) /
            ((N : ℝ) * Real.sqrt (N : ℝ)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hrho_nn]
        calc _ ≤ (|cConst k h| * ((pGrid k e : ℝ) * (2 * (tGrid k e : ℝ)) / (N : ℝ) ^ 2)) *
              ((4 * Real.sqrt 2) * Real.sqrt (N : ℝ)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hdiff_inv (abs_nonneg _))
                (hrho_nh_bd h hh) hrho_nn (by positivity)
          _ = |cConst k h| * (pGrid k e : ℝ) * (2 * (tGrid k e : ℝ)) * (4 * Real.sqrt 2) *
              (Real.sqrt (N : ℝ) / (N : ℝ) ^ 2) := by ring
          _ = |cConst k h| * (pGrid k e : ℝ) * (2 * (tGrid k e : ℝ)) * (4 * Real.sqrt 2) /
              ((N : ℝ) * Real.sqrt (N : ℝ)) := by rw [hsqrt_div_sq]; ring
      exact le_trans (abs_add_le _ _) (by rw [add_div]; exact add_le_add hterm1 hterm2)
    rw [abs_mul, abs_mul, abs_of_nonneg (a := (σ k (pGrid k e) : ℝ)) (Nat.cast_nonneg _)]
    have hcomb := abs_add_le
      (tailT k (nOf e) - ∑ h ∈ Finset.Icc 1 (k + 1),
        (σ k (nOf e + h) : ℝ) / ∏ j ∈ Finset.Icc 1 h, ((nOf e : ℝ) + (j : ℝ)))
      (∑ h ∈ Finset.Icc 1 (k + 1),
        ((Rpoly k h).eval (nOf e : ℝ) /
            ((nOf e : ℝ) * ∏ j ∈ Finset.Icc 1 h, ((nOf e : ℝ) + (j : ℝ))) *
          rho k (nOf e + h) +
          cConst k h * (1 / (nOf e : ℝ) - (pGrid k e : ℝ) / (N : ℝ)) *
          rho k (nOf e + h)))
    have hinner_le := le_trans hcomb (add_le_add htail_bd hsum_h_bd)
    rw [← add_div] at hinner_le
    exact (mul_le_mul_of_nonneg_left hinner_le
      (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))).trans_eq (by ring)
  -- Also bound |Rcomb k N| ≤ C_R * √N so |Rcomb k N / N| ≤ C_R / √N → 0
  let C_R : ℝ := ∑ e : Grid k, ∑ h ∈ Finset.Icc 1 (k + 1),
    |(wGrid k e : ℝ) * cConst k h * (pGrid k e : ℝ) ^ (k + 1)| * (2 * Real.sqrt 2)
  have hCR_abs_bd : ∀ N : ℕ, N0 ≤ N → |Rcomb k N| ≤ C_R * Real.sqrt (N : ℝ) := by
    intro N hN
    unfold Rcomb C_R
    rw [Finset.sum_mul]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun e _ => ?_)
    rw [Finset.sum_mul]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun h hh => ?_)
    rw [abs_mul, abs_of_nonneg (rho_nonneg k _)]
    have hrh_le : rShift k h e ≤ maxR := by
      have hh1 := (Finset.mem_Icc.mp hh).1
      have hh2 := (Finset.mem_Icc.mp hh).2
      have hle1 : rShift k h e ≤ rShift k (k + 1) e := by
        unfold rShift
        exact Nat.sub_le_sub_right (Nat.mul_le_mul_right _ hh2) _
      exact le_trans hle1 (Finset.le_sup (f := fun e => rShift k (k + 1) e) (Finset.mem_univ e))
    have hNr_le : ((N + rShift k h e : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      have : 2 * maxR ≤ N := by have := le_trans (le_max_left _ _) hN; omega
      exact_mod_cast (show N + rShift k h e ≤ 2 * N by omega)
    have hrho_le : rho k (N + rShift k h e) ≤ 2 * Real.sqrt 2 * Real.sqrt (N : ℝ) := by
      calc rho k (N + rShift k h e)
          ≤ 2 * Real.sqrt ((N + rShift k h e : ℕ) : ℝ) :=
            rho_le_two_sqrt hk (by omega)
        _ ≤ 2 * Real.sqrt (2 * (N : ℝ)) := by gcongr
        _ = 2 * Real.sqrt 2 * Real.sqrt (N : ℝ) := by rw [Real.sqrt_mul (by norm_num)]; ring
    calc _ ≤ |(wGrid k e : ℝ) * cConst k h * (pGrid k e : ℝ) ^ (k + 1)| *
          (2 * Real.sqrt 2 * Real.sqrt (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hrho_le (abs_nonneg _)
      _ = _ := by ring
  -- Hence for large m, the integer z equals 0, giving |Rcomb k (A + m * Q)| ≤ C_err / √(A + m * Q) → 0
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Find M_big such that for all m ≥ M_big, N = A + m * Q satisfies N ≥ N0,
  -- C_R / √N < 1/4, C_err / (N * √N) < 1/4, and C_err / √N < ε
  let Kbig : ℝ := max (4 * (C_R + C_err + 1)) ((C_err + 1) / ε)
  obtain ⟨M1, hM1⟩ := exists_nat_gt (Kbig ^ 2)
  refine ⟨max N0 M1, fun m hm => ?_⟩
  rw [Real.dist_eq, sub_zero]
  set N := A + m * Q
  have hN_ge_m : m ≤ N := by
    have : m * 1 ≤ m * Q := Nat.mul_le_mul_left m hQpos
    omega
  have hN_ge_N0 : N0 ≤ N := le_trans (le_trans (le_max_left _ _) hm) hN_ge_m
  have hN_gt_K2 : Kbig ^ 2 < (N : ℝ) := by
    have h1 : (M1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast le_trans (le_trans (le_max_right _ _) hm) hN_ge_m
    linarith
  have hKbig_pos : 0 < Kbig := by
    have hC_R_nn : 0 ≤ C_R := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    exact lt_of_lt_of_le (show (0 : ℝ) < 4 * (C_R + C_err + 1) by linarith) (le_max_left _ _)
  have hsqrtN_gt : Kbig < Real.sqrt (N : ℝ) := by
    rw [← Real.sqrt_sq hKbig_pos.le]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hN_gt_K2
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN_pos
  have hN_ge1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNmod : ∀ e : Grid k, N ≡ tGrid k e [MOD (pGrid k e) ^ 2] := by
    intro e
    have hdvd : (pGrid k e) ^ 2 ∣ Q := Finset.dvd_prod_of_mem _ (Finset.mem_univ e)
    have h1 : A + m * Q ≡ A [MOD (pGrid k e) ^ 2] := by
      rw [Nat.ModEq]
      have : (m * Q) % (pGrid k e) ^ 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hdvd m)
      rw [Nat.add_mod, this, add_zero, Nat.mod_mod]
    exact h1.trans (hA_mod e)
  obtain ⟨z, hz⟩ := hW_approx N hN_ge_N0 hNmod
  have hRdiv : |Rcomb k N / (N : ℝ)| ≤ C_R / Real.sqrt (N : ℝ) := by
    rw [abs_div, abs_of_pos hN_pos]
    have hsq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hN_pos.le
    calc |Rcomb k N| / (N : ℝ) ≤ C_R * Real.sqrt (N : ℝ) / (N : ℝ) :=
          div_le_div_of_nonneg_right (hCR_abs_bd N hN_ge_N0) hN_pos.le
      _ = C_R / Real.sqrt (N : ℝ) := by
          field_simp [hN_pos.ne', hsqrtN_pos.ne']
          rw [hsq]
  have hz_small : |(z : ℝ)| < 1 := by
    have h1 : |(z : ℝ)| ≤ |(z : ℝ) - Rcomb k N / (N : ℝ)| + |Rcomb k N / (N : ℝ)| := by
      calc |(z : ℝ)| = |((z : ℝ) - Rcomb k N / (N : ℝ)) + Rcomb k N / (N : ℝ)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h2 : C_err / ((N : ℝ) * Real.sqrt (N : ℝ)) ≤ C_err / Real.sqrt (N : ℝ) :=
      div_le_div_of_nonneg_left hC_err_nonneg hsqrtN_pos (le_mul_of_one_le_left hsqrtN_pos.le hN_ge1)
    have h3 : (C_R + C_err) / Real.sqrt (N : ℝ) < 1 / 2 := by
      rw [div_lt_iff₀ hsqrtN_pos]
      have hK1 : 4 * (C_R + C_err + 1) ≤ Kbig := le_max_left _ _
      have hC_R_nn : 0 ≤ C_R := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
      linarith
    rw [add_div] at h3
    linarith
  have hz0 : z = 0 := by
    have hlt1 : (z : ℝ) < 1 := (abs_lt.mp hz_small).2
    have hgt1 : (-1 : ℝ) < (z : ℝ) := (abs_lt.mp hz_small).1
    have hzlt : z < 1 := by exact_mod_cast hlt1
    have hzgt : -1 < z := by exact_mod_cast hgt1
    omega
  rw [hz0, Int.cast_zero, zero_sub, abs_neg, abs_div, abs_of_pos hN_pos] at hz
  have hR_le : |Rcomb k N| ≤ C_err / Real.sqrt (N : ℝ) := by
    rw [div_le_iff₀ hN_pos] at hz
    have heq : C_err / ((N : ℝ) * Real.sqrt (N : ℝ)) * (N : ℝ) = C_err / Real.sqrt (N : ℝ) := by
      field_simp [hN_pos.ne', hsqrtN_pos.ne']
    linarith
  have hlt_eps : C_err / Real.sqrt (N : ℝ) < ε := by
    rw [div_lt_iff₀ hsqrtN_pos]
    have hK2 : (C_err + 1) / ε ≤ Kbig := le_max_right _ _
    have hmul : C_err + 1 ≤ Kbig * ε := (div_le_iff₀ hε).mp hK2
    nlinarith
  exact lt_of_le_of_lt hR_le hlt_eps

/- ### Part 8: Elementary Cesàro progression-mean contradiction -/

private lemma count_dvd_ap (a M d X : ℕ) (hd : 1 ≤ d) (_hM : 1 ≤ M) :
    let g := Nat.gcd d M
    |(((Finset.range X).filter (fun m => d ∣ a + m * M)).card : ℝ) -
        (X : ℝ) * (if g ∣ a then (g : ℝ) / (d : ℝ) else 0)| ≤ 1 := by
  intro g
  by_cases hg : g ∣ a
  · simp only [hg, ↓reduceIte]
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left M hd
    let q := d / g
    let M' := M / g
    let a' := a / g
    have hq_pos : 0 < q := Nat.div_pos (Nat.le_of_dvd hd (Nat.gcd_dvd_left d M)) hg_pos
    have hd_eq : g * q = d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d M)
    have hM_eq : g * M' = M := Nat.mul_div_cancel' (Nat.gcd_dvd_right d M)
    have ha_eq : g * a' = a := Nat.mul_div_cancel' hg
    have hcop : Nat.Coprime q M' := Nat.coprime_div_gcd_div_gcd hg_pos
    -- Find unique residue class m₀ < q solving q ∣ a' + m₀ * M'
    have hex_m0 : ∃ m₀ < q, q ∣ a' + m₀ * M' := by
      have hbez : (1 : ℤ) = (q : ℤ) * Nat.gcdA q M' + (M' : ℤ) * Nat.gcdB q M' := by
        have := Nat.gcd_eq_gcd_ab q M'
        rw [hcop.gcd_eq_one, Nat.cast_one] at this
        exact this
      let r : ℤ := (-(a' : ℤ) * Nat.gcdB q M') % (q : ℤ)
      have hqZ_pos : (0 : ℤ) < q := Nat.cast_pos.mpr hq_pos
      have hr_nn : 0 ≤ r := Int.emod_nonneg _ hqZ_pos.ne'
      have hr_lt : r < q := Int.emod_lt_of_pos _ hqZ_pos
      let m₀ : ℕ := r.toNat
      have hm₀_eq : (m₀ : ℤ) = r := Int.toNat_of_nonneg hr_nn
      refine ⟨m₀, by omega, ?_⟩
      have hdvdZ : (q : ℤ) ∣ ((a' + m₀ * M' : ℕ) : ℤ) := by
        push_cast
        rw [hm₀_eq]
        have hmod1 : r ≡ -(a' : ℤ) * Nat.gcdB q M' [ZMOD (q : ℤ)] := Int.mod_modEq _ _
        have hmod2 : (a' : ℤ) + r * (M' : ℤ) ≡ (a' : ℤ) + (-(a' : ℤ) * Nat.gcdB q M') * (M' : ℤ)
            [ZMOD (q : ℤ)] := (Int.ModEq.refl _).add (hmod1.mul_right _)
        have hmod3 : (a' : ℤ) + (-(a' : ℤ) * Nat.gcdB q M') * (M' : ℤ) =
            (q : ℤ) * ((a' : ℤ) * Nat.gcdA q M') := by
          have := congrArg (fun t => (a' : ℤ) * t) hbez
          linarith
        rw [hmod3] at hmod2
        have h0 : (q : ℤ) * ((a' : ℤ) * Nat.gcdA q M') ≡ 0 [ZMOD (q : ℤ)] :=
          Int.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)
        exact Int.modEq_zero_iff_dvd.mp (hmod2.trans h0)
      exact Int.ofNat_dvd.mp hdvdZ
    obtain ⟨m₀, hm₀_lt, hm₀_dvd⟩ := hex_m0
    have hiff : ∀ m : ℕ, d ∣ a + m * M ↔ m % q = m₀ := by
      intro m
      have hstep1 : d ∣ a + m * M ↔ q ∣ a' + m * M' := by
        rw [← hd_eq, ← ha_eq, ← hM_eq, show g * a' + m * (g * M') = g * (a' + m * M') by ring]
        exact mul_dvd_mul_iff_left hg_pos.ne'
      rw [hstep1]
      constructor
      · intro hdm
        have hdvdZ : (q : ℤ) ∣ ((m : ℤ) - (m₀ : ℤ)) * (M' : ℤ) := by
          have h1 : (q : ℤ) ∣ ((a' : ℤ) + (m : ℤ) * (M' : ℤ)) := by exact_mod_cast hdm
          have h2 : (q : ℤ) ∣ ((a' : ℤ) + (m₀ : ℤ) * (M' : ℤ)) := by exact_mod_cast hm₀_dvd
          have heq : ((m : ℤ) - (m₀ : ℤ)) * (M' : ℤ) =
              ((a' : ℤ) + (m : ℤ) * (M' : ℤ)) - ((a' : ℤ) + (m₀ : ℤ) * (M' : ℤ)) := by ring
          rw [heq]
          exact dvd_sub h1 h2
        have hcopZ : IsCoprime (q : ℤ) (M' : ℤ) := (Nat.isCoprime_iff_coprime.mpr hcop)
        have hqm : (q : ℤ) ∣ ((m : ℤ) - (m₀ : ℤ)) := hcopZ.dvd_of_dvd_mul_right hdvdZ
        have hmodeq : m ≡ m₀ [MOD q] := by
          rw [Nat.ModEq, ← Int.natCast_inj]
          push_cast
          exact Int.modEq_iff_dvd.mpr (by simpa using dvd_neg.mpr hqm)
        rw [Nat.ModEq, Nat.mod_eq_of_lt hm₀_lt] at hmodeq
        exact hmodeq
      · intro hmod
        have h1 : m = q * (m / q) + m₀ := by
          have := (Nat.div_add_mod m q).symm
          rwa [hmod] at this
        rw [h1, show a' + (q * (m / q) + m₀) * M' = (a' + m₀ * M') + q * ((m / q) * M') by ring]
        exact dvd_add hm₀_dvd (dvd_mul_right q _)
    let S := (Finset.range X).filter (fun m => d ∣ a + m * M)
    have hlb : X / q ≤ S.card := by
      rw [← Finset.card_range (X / q)]
      refine Finset.card_le_card_of_injOn (fun j => j * q + m₀) ?_ ?_
      · intro j hj
        simp only [Finset.coe_range, Set.mem_Iio, Finset.coe_filter, Set.mem_ofPred_eq,
          Finset.mem_range, S] at hj ⊢
        refine ⟨?_, (hiff _).mpr ?_⟩
        · have hj1 : (j + 1) * q ≤ (X / q) * q := Nat.mul_le_mul_right q hj
          have hdiv_le : (X / q) * q ≤ X := Nat.div_mul_le_self X q
          nlinarith
        · rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hm₀_lt]
      · intro j₁ _ j₂ _ hjeq
        dsimp only at hjeq
        have : j₁ * q = j₂ * q := by omega
        exact Nat.eq_of_mul_eq_mul_right hq_pos this
    have hub : S.card ≤ X / q + 1 := by
      have hcard_eq : (Finset.range (X / q + 1)).card = X / q + 1 := Finset.card_range _
      rw [← hcard_eq]
      refine Finset.card_le_card_of_injOn (fun m => m / q) ?_ ?_
      · intro m hm
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range, Finset.coe_range,
          Set.mem_Iio, S] at hm ⊢
        have : m / q ≤ X / q := Nat.div_le_div_right hm.1.le
        omega
      · intro m₁ hm₁ m₂ hm₂ hdiv
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, S] at hm₁ hm₂
        dsimp only at hdiv
        have h1 : m₁ % q = m₀ := (hiff m₁).mp hm₁.2
        have h2 : m₂ % q = m₀ := (hiff m₂).mp hm₂.2
        have e1 := Nat.div_add_mod m₁ q
        have e2 := Nat.div_add_mod m₂ q
        rw [h1, hdiv] at e1
        rw [h2] at e2
        omega
    have hq_rat : (X : ℝ) * ((g : ℝ) / (d : ℝ)) = (X : ℝ) / (q : ℝ) := by
      have hdR : (d : ℝ) = (g : ℝ) * (q : ℝ) := by exact_mod_cast hd_eq.symm
      rw [hdR]
      have hgne : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hg_pos.ne'
      have hqne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq_pos.ne'
      field_simp [hgne, hqne]
    rw [hq_rat]
    have hq_posR : (0 : ℝ) < q := Nat.cast_pos.mpr hq_pos
    have hdiv_lb : ((X / q : ℕ) : ℝ) ≤ (X : ℝ) / (q : ℝ) := by
      rw [le_div_iff₀ hq_posR]
      exact_mod_cast Nat.div_mul_le_self X q
    have hdiv_ub : (X : ℝ) / (q : ℝ) < ((X / q : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hq_posR]
      have hlt : X < (X / q + 1) * q := by
        have := Nat.div_add_mod X q
        have := Nat.mod_lt X hq_pos
        nlinarith
      exact_mod_cast hlt
    have hSlb : ((X / q : ℕ) : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hlb
    have hSub : (S.card : ℝ) ≤ ((X / q : ℕ) : ℝ) + 1 := by exact_mod_cast hub
    rw [abs_le]
    constructor <;> linarith
  · simp only [hg, ↓reduceIte, mul_zero, sub_zero]
    have hempty : (Finset.range X).filter (fun m => d ∣ a + m * M) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro m hm
      have hdvd : d ∣ a + m * M := (Finset.mem_filter.mp hm).2
      have hg1 : g ∣ a + m * M := dvd_trans (Nat.gcd_dvd_left d M) hdvd
      have hg2 : g ∣ m * M := dvd_mul_of_dvd_right (Nat.gcd_dvd_right d M) m
      exact hg ((Nat.dvd_add_left hg2).mp hg1)
    rw [hempty, Finset.card_empty, Nat.cast_zero, abs_zero]
    norm_num

private lemma harmonic_le_two_sqrt (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
  rcases N.eq_zero_or_pos with rfl | hN
  · simp
  · set s := Real.sqrt (N : ℝ)
    have hs_pos : 0 < s := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
    let A : Finset ℕ := (Finset.Icc 1 N).filter (fun d : ℕ => (d : ℝ) ≤ s)
    let B : Finset ℕ := (Finset.Icc 1 N).filter (fun d : ℕ => ¬ (d : ℝ) ≤ s)
    have hsplit : ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) =
        (∑ d ∈ A, (1 : ℝ) / (d : ℝ)) + (∑ d ∈ B, (1 : ℝ) / (d : ℝ)) := by
      rw [← Finset.sum_union]
      · congr 1; ext d; simp only [Finset.mem_union, Finset.mem_filter, A, B]; tauto
      · rw [Finset.disjoint_left]; intro d h1 h2
        simp only [Finset.mem_filter, A, B] at h1 h2; exact h2.2 h1.2
    have hA : ∑ d ∈ A, (1 : ℝ) / (d : ℝ) ≤ s := by
      have hsub : A ⊆ Finset.Icc 1 (Nat.floor s) := fun d hd => by
        simp only [Finset.mem_filter, Finset.mem_Icc, A] at hd ⊢
        exact ⟨hd.1.1, Nat.le_floor hd.2⟩
      calc ∑ d ∈ A, (1 : ℝ) / (d : ℝ)
          ≤ ∑ _d ∈ A, (1 : ℝ) := Finset.sum_le_sum fun d hd => by
            have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
            exact div_le_one_of_le₀ hd1 (by positivity)
        _ = (A.card : ℝ) := by simp
        _ ≤ ((Finset.Icc 1 (Nat.floor s)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
        _ = (Nat.floor s : ℝ) := by simp
        _ ≤ s := Nat.floor_le hs_pos.le
    have hB : ∑ d ∈ B, (1 : ℝ) / (d : ℝ) ≤ s := by
      have hBcard : (B.card : ℝ) ≤ (N : ℝ) := by
        calc (B.card : ℝ) ≤ ((Finset.Icc 1 N).card : ℝ) := by
              exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
          _ = (N : ℝ) := by simp
      calc ∑ d ∈ B, (1 : ℝ) / (d : ℝ)
          ≤ ∑ _d ∈ B, (1 : ℝ) / s := Finset.sum_le_sum fun d hd =>
            one_div_le_one_div_of_le hs_pos (lt_of_not_ge (Finset.mem_filter.mp hd).2).le
        _ = (B.card : ℝ) / s := by rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
        _ ≤ (N : ℝ) / s := div_le_div_of_nonneg_right hBcard hs_pos.le
        _ = s := by
            have hsq : s * s = (N : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg N)
            rw [div_eq_iff hs_pos.ne', hsq]
    rw [hsplit]
    linarith

private lemma sum_inv_sq_tail_le (B N : ℕ) (hB : 1 ≤ B) :
    ∑ d ∈ Finset.Icc (B + 1) N, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 1 / (B : ℝ) := by
  have hterm : ∀ d ∈ Finset.Icc (B + 1) N,
      (1 : ℝ) / (d : ℝ) ^ 2 ≤ 1 / ((d - 1 : ℕ) : ℝ) - 1 / (d : ℝ) := by
    intro d hd
    have hd2 : 2 ≤ d := by have := (Finset.mem_Icc.mp hd).1; omega
    have hd1 : (0 : ℝ) < (d - 1 : ℕ) := Nat.cast_pos.mpr (by omega)
    have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
    have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ d by omega), Nat.cast_one]
    rw [hcast]
    have hd1' : (0 : ℝ) < (d : ℝ) - 1 := by linarith
    have hdiff : (1 : ℝ) / ((d : ℝ) - 1) - 1 / (d : ℝ) = 1 / (((d : ℝ) - 1) * (d : ℝ)) := by
      field_simp [hd1'.ne', hd0.ne']
      ring
    rw [hdiff]
    exact one_div_le_one_div_of_le (mul_pos hd1' hd0) (by nlinarith)
  have htel : ∀ M : ℕ, ∑ d ∈ Finset.Icc (B + 1) (B + M),
      (1 / ((d - 1 : ℕ) : ℝ) - 1 / (d : ℝ)) = 1 / (B : ℝ) - 1 / ((B + M : ℕ) : ℝ) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      have hIcc : Finset.Icc (B + 1) (B + (M + 1)) =
          insert (B + (M + 1)) (Finset.Icc (B + 1) (B + M)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : B + (M + 1) ∉ Finset.Icc (B + 1) (B + M) := by simp
      rw [hIcc, Finset.sum_insert hnot, ih, show B + (M + 1) - 1 = B + M by omega]
      ring
  by_cases hNB : N ≤ B
  · have hempty : Finset.Icc (B + 1) N = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    positivity
  · have hN_eq : N = B + (N - B) := by omega
    calc ∑ d ∈ Finset.Icc (B + 1) N, (1 : ℝ) / (d : ℝ) ^ 2
        ≤ ∑ d ∈ Finset.Icc (B + 1) N, (1 / ((d - 1 : ℕ) : ℝ) - 1 / (d : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = 1 / (B : ℝ) - 1 / (N : ℝ) := by
          conv_lhs => rw [hN_eq]
          rw [htel (N - B), ← hN_eq]
      _ ≤ 1 / (B : ℝ) := by linarith [show (0 : ℝ) ≤ 1 / (N : ℝ) by positivity]

private noncomputable def muApprox (k M B a : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 B,
    (1 : ℝ) / (d : ℝ) ^ k * (if Nat.gcd d M ∣ a then (Nat.gcd d M : ℝ) / (d : ℝ) else 0)

private lemma cesaro_rho_approx {k M B a X : ℕ} (hk : 1 ≤ k) (hM : 1 ≤ M) (hB : 1 ≤ B)
    (ha : 1 ≤ a) (hX : 1 ≤ X) :
    |(1 / (X : ℝ)) * (∑ m ∈ Finset.range X, rho k (a + m * M)) - muApprox k M B a| ≤
      (B : ℝ) / (X : ℝ) + (M : ℝ) / (B : ℝ) + 2 * Real.sqrt ((a + X * M : ℕ) : ℝ) / (X : ℝ) := by
  have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr hX
  let U := a + X * M
  -- Swap sum over m < X and divisors d ∈ [1, U]
  have hswap : ∑ m ∈ Finset.range X, rho k (a + m * M) =
      ∑ d ∈ Finset.Icc 1 U,
        (1 : ℝ) / (d : ℝ) ^ k * (((Finset.range X).filter (fun m => d ∣ a + m * M)).card : ℝ) := by
    have hstep1 : ∀ m ∈ Finset.range X,
        rho k (a + m * M) = ∑ d ∈ Finset.Icc 1 U,
          if d ∣ a + m * M then (1 : ℝ) / (d : ℝ) ^ k else 0 := by
      intro m hm
      rw [rho_eq_sum_divisors (by omega)]
      rw [← Finset.sum_filter]
      congr 1
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdvd, hne⟩
        have hmle : m < X := Finset.mem_range.mp hm
        have hdpos : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
        have hdle : d ≤ a + m * M := Nat.le_of_dvd (by omega) hdvd
        have hleU : a + m * M ≤ U := by
          dsimp [U]
          exact Nat.add_le_add_left (Nat.mul_le_mul_right M hmle.le) a
        exact ⟨⟨hdpos, le_trans hdle hleU⟩, hdvd⟩
      · rintro ⟨_, hdvd⟩
        exact ⟨hdvd, by omega⟩
    rw [Finset.sum_congr rfl hstep1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hswap, Finset.mul_sum]
  -- Split [1, U] and [1, B] into common part [1, min B U] + extra terms
  let Nmax := max B U
  have hpad1 : ∑ d ∈ Finset.Icc 1 U,
        (1 / (X : ℝ)) * ((1 : ℝ) / (d : ℝ) ^ k *
          (((Finset.range X).filter (fun m => d ∣ a + m * M)).card : ℝ)) =
      ∑ d ∈ Finset.Icc 1 Nmax,
        (1 / (X : ℝ)) * ((1 : ℝ) / (d : ℝ) ^ k *
          (((Finset.range X).filter (fun m => d ∣ a + m * M)).card : ℝ)) := by
    refine Finset.sum_subset (Finset.Icc_subset_Icc_right (le_max_right B U)) fun d hd hdnot => ?_
    have hd_gt : U < d := by
      simp only [Finset.mem_Icc] at hd hdnot
      omega
    have hempty : (Finset.range X).filter (fun m => d ∣ a + m * M) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro m hm
      have hm1 := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
      have hm2 := (Finset.mem_filter.mp hm).2
      have hle : d ≤ a + m * M := Nat.le_of_dvd (by omega) hm2
      have : a + m * M ≤ U := Nat.add_le_add_left (Nat.mul_le_mul_right M hm1.le) a
      omega
    rw [hempty, Finset.card_empty, Nat.cast_zero, mul_zero, mul_zero]
  rw [hpad1]
  have hsplit_Nmax : Finset.Icc 1 Nmax = Finset.Icc 1 B ∪ Finset.Icc (B + 1) Nmax := by
    ext d; simp only [Finset.mem_Icc, Finset.mem_union]
    have hBN : B ≤ Nmax := le_max_left B U
    omega
  have hdisj : Disjoint (Finset.Icc 1 B) (Finset.Icc (B + 1) Nmax) := by
    rw [Finset.disjoint_left]; intro d h1 h2
    simp only [Finset.mem_Icc] at h1 h2; omega
  rw [hsplit_Nmax, Finset.sum_union hdisj, add_sub_right_comm]
  -- Part A: d ∈ [1, B]
  have hpartA :
      |(∑ d ∈ Finset.Icc 1 B,
          (1 / (X : ℝ)) * ((1 : ℝ) / (d : ℝ) ^ k *
            (((Finset.range X).filter (fun m => d ∣ a + m * M)).card : ℝ))) -
        muApprox k M B a| ≤ (B : ℝ) / (X : ℝ) := by
    unfold muApprox
    rw [← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ d ∈ Finset.Icc 1 B,
          |(1 / (X : ℝ)) * ((1 : ℝ) / (d : ℝ) ^ k *
              (((Finset.range X).filter (fun m => d ∣ a + m * M)).card : ℝ)) -
            (1 : ℝ) / (d : ℝ) ^ k *
              (if Nat.gcd d M ∣ a then (Nat.gcd d M : ℝ) / (d : ℝ) else 0)|
        ≤ ∑ _d ∈ Finset.Icc 1 B, (1 : ℝ) / (X : ℝ) := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          have hcnt := count_dvd_ap a M d X hd1 hM
          have hrew : (1 / (X : ℝ)) * ((1 : ℝ) / (d : ℝ) ^ k *
                (((Finset.range X).filter (fun m => d ∣ a + m * M)).card : ℝ)) -
              (1 : ℝ) / (d : ℝ) ^ k *
                (if Nat.gcd d M ∣ a then (Nat.gcd d M : ℝ) / (d : ℝ) else 0) =
              ((1 : ℝ) / (d : ℝ) ^ k / (X : ℝ)) *
                ((((Finset.range X).filter (fun m => d ∣ a + m * M)).card : ℝ) -
                  (X : ℝ) * (if Nat.gcd d M ∣ a then (Nat.gcd d M : ℝ) / (d : ℝ) else 0)) := by
            field_simp [hXpos.ne']
          rw [hrew, abs_mul, abs_of_nonneg (by positivity)]
          have hdk : (1 : ℝ) / (d : ℝ) ^ k ≤ 1 :=
            div_le_one_of_le₀ (one_le_pow₀ (by exact_mod_cast hd1)) (by positivity)
          calc ((1 : ℝ) / (d : ℝ) ^ k / (X : ℝ)) * |_|
              ≤ ((1 : ℝ) / (d : ℝ) ^ k / (X : ℝ)) * 1 :=
                mul_le_mul_of_nonneg_left hcnt (by positivity)
            _ ≤ 1 / (X : ℝ) := by rw [mul_one]; exact div_le_div_of_nonneg_right hdk hXpos.le
      _ = (B : ℝ) / (X : ℝ) := by simp [div_eq_mul_inv]
  -- Part B: d ∈ [B + 1, Nmax] (note terms for d > U are 0)
  have hpartB :
      |∑ d ∈ Finset.Icc (B + 1) Nmax,
          (1 / (X : ℝ)) * ((1 : ℝ) / (d : ℝ) ^ k *
            (((Finset.range X).filter (fun m => d ∣ a + m * M)).card : ℝ))| ≤
        (M : ℝ) / (B : ℝ) + 2 * Real.sqrt (U : ℝ) / (X : ℝ) := by
    rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)]
    have hle_U : ∑ d ∈ Finset.Icc (B + 1) Nmax,
          (1 / (X : ℝ)) * ((1 : ℝ) / (d : ℝ) ^ k *
            (((Finset.range X).filter (fun m => d ∣ a + m * M)).card : ℝ)) =
        ∑ d ∈ Finset.Icc (B + 1) U,
          (1 / (X : ℝ)) * ((1 : ℝ) / (d : ℝ) ^ k *
            (((Finset.range X).filter (fun m => d ∣ a + m * M)).card : ℝ)) := by
      refine (Finset.sum_subset (Finset.Icc_subset_Icc_right (le_max_right B U)) ?_).symm
      intro d hd hdnot
      have hd_gt : U < d := by simp only [Finset.mem_Icc] at hd hdnot; omega
      have hempty : (Finset.range X).filter (fun m => d ∣ a + m * M) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro m hm
        have hm1 := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
        have hm2 := (Finset.mem_filter.mp hm).2
        have hle : d ≤ a + m * M := Nat.le_of_dvd (by omega) hm2
        have : a + m * M ≤ U := Nat.add_le_add_left (Nat.mul_le_mul_right M hm1.le) a
        omega
      rw [hempty, Finset.card_empty, Nat.cast_zero, mul_zero, mul_zero]
    rw [hle_U]
    have hterm_ub : ∀ d ∈ Finset.Icc (B + 1) U,
        (1 / (X : ℝ)) * ((1 : ℝ) / (d : ℝ) ^ k *
          (((Finset.range X).filter (fun m => d ∣ a + m * M)).card : ℝ)) ≤
        (M : ℝ) * ((1 : ℝ) / (d : ℝ) ^ 2) + (1 / (X : ℝ)) * ((1 : ℝ) / (d : ℝ)) := by
      intro d hd
      have hd1 : 1 ≤ d := by have := (Finset.mem_Icc.mp hd).1; omega
      have hcnt := (abs_le.mp (count_dvd_ap a M d X hd1 hM)).2
      have hgcd_le : (if Nat.gcd d M ∣ a then (Nat.gcd d M : ℝ) / (d : ℝ) else 0) ≤
          (M : ℝ) / (d : ℝ) := by
        split_ifs
        · exact div_le_div_of_nonneg_right
            (by exact_mod_cast Nat.le_of_dvd hM (Nat.gcd_dvd_right d M)) (Nat.cast_nonneg d)
        · positivity
      have hcard_ub : (((Finset.range X).filter (fun m => d ∣ a + m * M)).card : ℝ) ≤
          (X : ℝ) * ((M : ℝ) / (d : ℝ)) + 1 := by
        have h1 : (X : ℝ) * (if Nat.gcd d M ∣ a then (Nat.gcd d M : ℝ) / (d : ℝ) else 0) ≤
            (X : ℝ) * ((M : ℝ) / (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hgcd_le hXpos.le
        linarith
      have hdk_le : (1 : ℝ) / (d : ℝ) ^ k ≤ 1 / (d : ℝ) := by
        have hd_ge1 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
        have hpow : (d : ℝ) ≤ (d : ℝ) ^ k := by
          calc (d : ℝ) = (d : ℝ) ^ 1 := (pow_one _).symm
            _ ≤ (d : ℝ) ^ k := pow_le_pow_right₀ hd_ge1 hk
        exact one_div_le_one_div_of_le (Nat.cast_pos.mpr hd1) hpow
      calc (1 / (X : ℝ)) * ((1 : ℝ) / (d : ℝ) ^ k *
            (((Finset.range X).filter (fun m => d ∣ a + m * M)).card : ℝ))
          ≤ (1 / (X : ℝ)) * ((1 : ℝ) / (d : ℝ) * ((X : ℝ) * ((M : ℝ) / (d : ℝ)) + 1)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul hdk_le hcard_ub (Nat.cast_nonneg _) (by positivity)
        _ = (M : ℝ) * ((1 : ℝ) / (d : ℝ) ^ 2) + (1 / (X : ℝ)) * ((1 : ℝ) / (d : ℝ)) := by
            have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            field_simp [hXpos.ne', hdne]
    calc ∑ d ∈ Finset.Icc (B + 1) U, _
        ≤ ∑ d ∈ Finset.Icc (B + 1) U,
            ((M : ℝ) * ((1 : ℝ) / (d : ℝ) ^ 2) + (1 / (X : ℝ)) * ((1 : ℝ) / (d : ℝ))) :=
          Finset.sum_le_sum hterm_ub
      _ = (M : ℝ) * (∑ d ∈ Finset.Icc (B + 1) U, (1 : ℝ) / (d : ℝ) ^ 2) +
          (1 / (X : ℝ)) * (∑ d ∈ Finset.Icc (B + 1) U, (1 : ℝ) / (d : ℝ)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ (M : ℝ) * (1 / (B : ℝ)) +
          (1 / (X : ℝ)) * (∑ d ∈ Finset.Icc 1 U, (1 : ℝ) / (d : ℝ)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (sum_inv_sq_tail_le B U hB) (Nat.cast_nonneg M)
          · apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Icc_subset_Icc_left (by omega)) (fun _ _ _ => by positivity)
      _ ≤ (M : ℝ) * (1 / (B : ℝ)) + (1 / (X : ℝ)) * (2 * Real.sqrt (U : ℝ)) := by
          gcongr
          exact harmonic_le_two_sqrt U
      _ = (M : ℝ) / (B : ℝ) + 2 * Real.sqrt (U : ℝ) / (X : ℝ) := by ring
  exact le_trans (abs_add_le _ _) (by linarith [hpartA, hpartB])

private lemma cesaro_tendsto_zero {f : ℕ → ℝ} (hf : Tendsto f atTop (nhds 0)) :
    Tendsto (fun X : ℕ => (1 / (X : ℝ)) * ∑ m ∈ Finset.range X, f m) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop] at hf ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hf (ε / 2) (by linarith)
  let S_init : ℝ := ∑ m ∈ Finset.range N, |f m|
  obtain ⟨X0, hX0⟩ := exists_nat_gt (2 * S_init / ε)
  refine ⟨max (N + 1) X0, fun X hX => ?_⟩
  rw [Real.dist_eq, sub_zero]
  have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr (by have := le_trans (le_max_left _ _) hX; omega)
  have hNX : N ≤ X := by have := le_trans (le_max_left _ _) hX; omega
  have hsplit : Finset.range X = Finset.range N ∪ Finset.Ico N X := by
    ext m; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.range N) (Finset.Ico N X) := by
    rw [Finset.disjoint_left]; intro m h1 h2
    simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj, abs_mul, abs_of_pos (one_div_pos.mpr hXpos)]
  have htail : |∑ m ∈ Finset.Ico N X, f m| ≤ ((X - N : ℕ) : ℝ) * (ε / 2) := by
    calc |∑ m ∈ Finset.Ico N X, f m|
        ≤ ∑ m ∈ Finset.Ico N X, |f m| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m ∈ Finset.Ico N X, (ε / 2) := Finset.sum_le_sum fun m hm => by
          have := hN m (Finset.mem_Ico.mp hm).1
          rw [Real.dist_eq, sub_zero] at this
          exact this.le
      _ = ((X - N : ℕ) : ℝ) * (ε / 2) := by simp
  have hhead : |∑ m ∈ Finset.range N, f m| ≤ S_init := Finset.abs_sum_le_sum_abs _ _
  have h1 : (1 / (X : ℝ)) * S_init < ε / 2 := by
    have hXgt : 2 * S_init / ε < (X : ℝ) := lt_of_lt_of_le hX0 (by exact_mod_cast le_trans (le_max_right _ _) hX)
    have hmul : 2 * S_init < (X : ℝ) * ε := (div_lt_iff₀ hε).mp hXgt
    rw [one_div, inv_mul_lt_iff₀ hXpos]
    linarith
  have h2 : (1 / (X : ℝ)) * (((X - N : ℕ) : ℝ) * (ε / 2)) ≤ ε / 2 := by
    have hleX : ((X - N : ℕ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast Nat.sub_le X N
    calc (1 / (X : ℝ)) * (((X - N : ℕ) : ℝ) * (ε / 2))
        ≤ (1 / (X : ℝ)) * ((X : ℝ) * (ε / 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hleX (by linarith)) (by positivity)
      _ = ε / 2 := by field_simp [hXpos.ne']
  have habs := abs_add_le (∑ m ∈ Finset.range N, f m) (∑ m ∈ Finset.Ico N X, f m)
  have hcomb : (1 / (X : ℝ)) * |∑ m ∈ Finset.range N, f m + ∑ m ∈ Finset.Ico N X, f m| ≤
      (1 / (X : ℝ)) * S_init + (1 / (X : ℝ)) * (((X - N : ℕ) : ℝ) * (ε / 2)) := by
    calc _ ≤ (1 / (X : ℝ)) * (|∑ m ∈ Finset.range N, f m| + |∑ m ∈ Finset.Ico N X, f m|) :=
          mul_le_mul_of_nonneg_left habs (by positivity)
      _ ≤ (1 / (X : ℝ)) * (S_init + ((X - N : ℕ) : ℝ) * (ε / 2)) :=
          mul_le_mul_of_nonneg_left (add_le_add hhead htail) (by positivity)
      _ = _ := by ring
  linarith

/- ### Part 9: Main theorem -/

theorem irrational_erdos_252_sum (k : ℕ) (hk : 1 ≤ k) :
    Irrational (Erdos252.erdos_252_sum k) := by
  rintro ⟨q, hq⟩
  obtain ⟨A, Q, hQpos, hR_tendsto⟩ := Rcomb_tendsto_zero hk hq
  let rStar : ℕ := rShift k (k + 1) (eStar k)
  let Iset : Finset (Grid k × ℕ) := (Finset.univ : Finset (Grid k)) ×ˢ Finset.Icc 1 (k + 1)
  let iStar : Grid k × ℕ := (eStar k, k + 1)
  have hiStar_mem : iStar ∈ Iset := Finset.mem_product.mpr ⟨Finset.mem_univ _, by simp [iStar]⟩
  let coef : Grid k × ℕ → ℝ := fun p =>
    (wGrid k p.1 : ℝ) * cConst k p.2 * (pGrid k p.1 : ℝ) ^ (k + 1)
  let shift : Grid k × ℕ → ℕ := fun p => rShift k p.2 p.1
  have hR_eq : ∀ N : ℕ, Rcomb k N = ∑ p ∈ Iset, coef p * rho k (N + shift p) := by
    intro N
    unfold Rcomb
    rw [Finset.sum_product]
  have hcStar_pos : 0 < coef iStar := by
    dsimp [coef, iStar]
    rw [wGrid_eStar, Int.cast_one, cConst_top, one_mul, one_mul]
    exact pow_pos (Nat.cast_pos.mpr (pGrid_pos k (eStar k))) (k + 1)
  have hshift_lt : ∀ p ∈ Iset, p ≠ iStar → shift p < rStar := by
    intro p hp hne
    have hp2 := Finset.mem_Icc.mp (Finset.mem_product.mp hp).2
    apply rShift_strict_max hp2.1 hp2.2 p.1
    rintro ⟨h1, h2⟩
    exact hne (Prod.ext h2 h1)
  -- Choose a fresh prime L > max Q (rStar + Iset.card + 2)
  obtain ⟨L, hL_ge, hL_prime⟩ := Nat.exists_infinite_primes (max Q (rStar + Iset.card + 2) + 1)
  have hL_gt_Q : Q < L := lt_of_le_of_lt (le_max_left Q (rStar + Iset.card + 2)) (by omega)
  have hL_gt_r : rStar < L := by have := le_max_right Q (rStar + Iset.card + 2); omega
  have hL_gt_card : Iset.card < L := by have := le_max_right Q (rStar + Iset.card + 2); omega
  have hL_cop_Q : Nat.Coprime L Q :=
    (hL_prime.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt hQpos hL_gt_Q)
  -- Pick residue b0 < L avoiding all (-shift p) mod L
  let badRes : Finset ℕ := Iset.image (fun p => (L - shift p % L) % L)
  have hbad_lt : badRes.card < (Finset.range L).card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt Finset.card_image_le hL_gt_card
  have hex_b0 : ∃ b0 ∈ Finset.range L, b0 ∉ badRes := by
    by_contra hall
    push Not at hall
    have hle : (Finset.range L).card ≤ badRes.card := Finset.card_le_card hall
    omega
  obtain ⟨b0, hb0_range, hb0_notbad⟩ := hex_b0
  have hb0_lt : b0 < L := Finset.mem_range.mp hb0_range
  have hb0_ndvd : ∀ p ∈ Iset, ¬ L ∣ (b0 + shift p) := by
    intro p hp hdvd
    apply hb0_notbad
    refine Finset.mem_image.mpr ⟨p, hp, ?_⟩
    have hmod0 : (b0 + shift p) % L = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have h1 : (b0 + shift p % L) % L = 0 := by rwa [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have h2 : shift p % L < L := Nat.mod_lt _ hL_prime.pos
    by_cases hs0 : shift p % L = 0
    · rw [hs0, Nat.sub_zero, Nat.mod_self]
      rw [hs0, add_zero, Nat.mod_eq_of_lt hb0_lt] at h1
      exact h1.symm
    · have hlt : L - shift p % L < L := by omega
      rw [Nat.mod_eq_of_lt hlt]
      have hsum_eq : b0 + shift p % L = L := by
        have hlt2 : b0 + shift p % L < 2 * L := by omega
        have hdvd2 : L ∣ (b0 + shift p % L) := Nat.dvd_of_mod_eq_zero h1
        obtain ⟨q', hq'⟩ := hdvd2
        have hq'1 : q' = 1 := by
          by_contra hne
          rcases Nat.eq_zero_or_pos q' with rfl | hpos
          · simp at hq'; omega
          · have : 2 ≤ q' := by omega
            nlinarith
        rw [hq'1, mul_one] at hq'
        exact hq'
      omega
  -- Residue b1 = L - rStar < L satisfies L ∣ b1 + rStar and ¬ L ∣ b1 + shift p for p ≠ iStar
  let b1 : ℕ := L - rStar
  have hb1_dvd_star : L ∣ (b1 + rStar) := by
    rw [show b1 + rStar = L by dsimp [b1]; omega]
  have hb1_ndvd_other : ∀ p ∈ Iset, p ≠ iStar → ¬ L ∣ (b1 + shift p) := by
    intro p hp hne hdvd
    have hlt := hshift_lt p hp hne
    have hpos : 0 < b1 + shift p := by dsimp [b1]; omega
    have hltL : b1 + shift p < L := by dsimp [b1]; omega
    exact Nat.not_dvd_of_pos_of_lt hpos hltL hdvd
  -- Construct A0 and A1 via CRT mod (L * Q)
  let cr0 := Nat.chineseRemainder hL_cop_Q b0 A
  let cr1 := Nat.chineseRemainder hL_cop_Q b1 A
  let A0 : ℕ := cr0.val + L * Q
  let A1 : ℕ := cr1.val + L * Q
  have hA0_pos : 1 ≤ A0 := by
    have : 1 ≤ L * Q := Nat.mul_pos hL_prime.pos hQpos
    omega
  have hA1_pos : 1 ≤ A1 := by
    have : 1 ≤ L * Q := Nat.mul_pos hL_prime.pos hQpos
    omega
  have hA0_modL : A0 ≡ b0 [MOD L] := by
    have h1 : A0 ≡ cr0.val [MOD L] := by
      dsimp [A0]; rw [Nat.ModEq, Nat.add_mul_mod_self_left]
    exact h1.trans cr0.property.1
  have hA0_modQ : A0 ≡ A [MOD Q] := by
    have h1 : A0 ≡ cr0.val [MOD Q] := by
      dsimp [A0]; rw [Nat.ModEq, Nat.add_mul_mod_self_right]
    exact h1.trans cr0.property.2
  have hA1_modL : A1 ≡ b1 [MOD L] := by
    have h1 : A1 ≡ cr1.val [MOD L] := by
      dsimp [A1]; rw [Nat.ModEq, Nat.add_mul_mod_self_left]
    exact h1.trans cr1.property.1
  have hA1_modQ : A1 ≡ A [MOD Q] := by
    have h1 : A1 ≡ cr1.val [MOD Q] := by
      dsimp [A1]; rw [Nat.ModEq, Nat.add_mul_mod_self_right]
    exact h1.trans cr1.property.2
  have hA0_ndvd : ∀ p ∈ Iset, ¬ L ∣ (A0 + shift p) := by
    intro p hp hdvd
    have h1 : A0 + shift p ≡ b0 + shift p [MOD L] := hA0_modL.add_right _
    exact hb0_ndvd p hp ((Nat.modEq_zero_iff_dvd.mp (h1.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))))
  have hA1_dvd_star : L ∣ (A1 + rStar) := by
    have h1 : A1 + rStar ≡ b1 + rStar [MOD L] := hA1_modL.add_right _
    exact Nat.modEq_zero_iff_dvd.mp (h1.trans (Nat.modEq_zero_iff_dvd.mpr hb1_dvd_star))
  have hA1_ndvd_other : ∀ p ∈ Iset, p ≠ iStar → ¬ L ∣ (A1 + shift p) := by
    intro p hp hne hdvd
    have h1 : A1 + shift p ≡ b1 + shift p [MOD L] := hA1_modL.add_right _
    exact hb1_ndvd_other p hp hne
      (Nat.modEq_zero_iff_dvd.mp (h1.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd)))
  -- Compare muApprox k (L * Q) B (A1 + shift p) and muApprox k (L * Q) B (A0 + shift p) for B ≥ L
  have hmu_eq_other : ∀ B : ℕ, ∀ p ∈ Iset, p ≠ iStar →
      muApprox k (L * Q) B (A1 + shift p) = muApprox k (L * Q) B (A0 + shift p) := by
    intro B p hp hne
    unfold muApprox
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    by_cases hLd : L ∣ d
    · have hL_dvd_g : L ∣ Nat.gcd d (L * Q) := Nat.dvd_gcd hLd (dvd_mul_right L Q)
      have h1 : ¬ Nat.gcd d (L * Q) ∣ (A1 + shift p) := fun h =>
        hA1_ndvd_other p hp hne (dvd_trans hL_dvd_g h)
      have h2 : ¬ Nat.gcd d (L * Q) ∣ (A0 + shift p) := fun h =>
        hA0_ndvd p hp (dvd_trans hL_dvd_g h)
      simp [h1, h2]
    · have hcop_dL : Nat.Coprime d L := (hL_prime.coprime_iff_not_dvd.mpr hLd).symm
      have hgcd_eq : Nat.gcd d (L * Q) = Nat.gcd d Q := by
        apply Nat.dvd_antisymm
        · refine Nat.dvd_gcd (Nat.gcd_dvd_left d (L * Q)) ?_
          have hcop_gL : Nat.Coprime (Nat.gcd d (L * Q)) L :=
            hcop_dL.coprime_dvd_left (Nat.gcd_dvd_left _ _)
          exact hcop_gL.dvd_of_dvd_mul_left (Nat.gcd_dvd_right d (L * Q))
        · exact Nat.dvd_gcd (Nat.gcd_dvd_left d Q) (dvd_mul_of_dvd_right (Nat.gcd_dvd_right d Q) L)
      have hQ_eq : Nat.gcd d Q ∣ (A1 + shift p) ↔ Nat.gcd d Q ∣ (A0 + shift p) := by
        have hmod : A1 + shift p ≡ A0 + shift p [MOD Q] :=
          (hA1_modQ.trans hA0_modQ.symm).add_right _
        have hmod' : A1 + shift p ≡ A0 + shift p [MOD Nat.gcd d Q] :=
          hmod.of_dvd (Nat.gcd_dvd_right d Q)
        constructor <;> intro h
        · exact Nat.modEq_zero_iff_dvd.mp (hmod'.symm.trans (Nat.modEq_zero_iff_dvd.mpr h))
        · exact Nat.modEq_zero_iff_dvd.mp (hmod'.trans (Nat.modEq_zero_iff_dvd.mpr h))
      rw [hgcd_eq]
      simp [hQ_eq]
  have hmu_star_ge : ∀ B : ℕ, L ≤ B →
      (1 : ℝ) / (L : ℝ) ^ k ≤
        muApprox k (L * Q) B (A1 + rStar) - muApprox k (L * Q) B (A0 + rStar) := by
    intro B hLB
    unfold muApprox
    rw [← Finset.sum_sub_distrib]
    have hL_mem : L ∈ Finset.Icc 1 B := Finset.mem_Icc.mpr ⟨hL_prime.pos, hLB⟩
    have hterm_nn : ∀ d ∈ Finset.Icc 1 B,
        0 ≤ (1 : ℝ) / (d : ℝ) ^ k *
            (if Nat.gcd d (L * Q) ∣ (A1 + rStar) then (Nat.gcd d (L * Q) : ℝ) / (d : ℝ) else 0) -
          (1 : ℝ) / (d : ℝ) ^ k *
            (if Nat.gcd d (L * Q) ∣ (A0 + rStar) then (Nat.gcd d (L * Q) : ℝ) / (d : ℝ) else 0) := by
      intro d _
      by_cases hLd : L ∣ d
      · have hL_dvd_g : L ∣ Nat.gcd d (L * Q) := Nat.dvd_gcd hLd (dvd_mul_right L Q)
        have h0 : ¬ Nat.gcd d (L * Q) ∣ (A0 + rStar) := fun h =>
          hA0_ndvd iStar hiStar_mem (dvd_trans hL_dvd_g h)
        simp only [h0, ↓reduceIte, mul_zero, sub_zero]
        split_ifs <;> positivity
      · have hcop_dL : Nat.Coprime d L := (hL_prime.coprime_iff_not_dvd.mpr hLd).symm
        have hgcd_eq : Nat.gcd d (L * Q) = Nat.gcd d Q := by
          apply Nat.dvd_antisymm
          · refine Nat.dvd_gcd (Nat.gcd_dvd_left d (L * Q)) ?_
            have hcop_gL : Nat.Coprime (Nat.gcd d (L * Q)) L :=
              hcop_dL.coprime_dvd_left (Nat.gcd_dvd_left _ _)
            exact hcop_gL.dvd_of_dvd_mul_left (Nat.gcd_dvd_right d (L * Q))
          · exact Nat.dvd_gcd (Nat.gcd_dvd_left d Q) (dvd_mul_of_dvd_right (Nat.gcd_dvd_right d Q) L)
        have hQ_eq : Nat.gcd d Q ∣ (A1 + rStar) ↔ Nat.gcd d Q ∣ (A0 + rStar) := by
          have hmod : A1 + rStar ≡ A0 + rStar [MOD Q] :=
            (hA1_modQ.trans hA0_modQ.symm).add_right _
          have hmod' : A1 + rStar ≡ A0 + rStar [MOD Nat.gcd d Q] :=
            hmod.of_dvd (Nat.gcd_dvd_right d Q)
          constructor <;> intro h
          · exact Nat.modEq_zero_iff_dvd.mp (hmod'.symm.trans (Nat.modEq_zero_iff_dvd.mpr h))
          · exact Nat.modEq_zero_iff_dvd.mp (hmod'.trans (Nat.modEq_zero_iff_dvd.mpr h))
        rw [hgcd_eq]
        simp [hQ_eq]
    have hL_term :
        (1 : ℝ) / (L : ℝ) ^ k *
            (if Nat.gcd L (L * Q) ∣ (A1 + rStar) then (Nat.gcd L (L * Q) : ℝ) / (L : ℝ) else 0) -
          (1 : ℝ) / (L : ℝ) ^ k *
            (if Nat.gcd L (L * Q) ∣ (A0 + rStar) then (Nat.gcd L (L * Q) : ℝ) / (L : ℝ) else 0) =
        (1 : ℝ) / (L : ℝ) ^ k := by
      have hgcdL : Nat.gcd L (L * Q) = L := Nat.gcd_eq_left (dvd_mul_right L Q)
      have h0 : ¬ L ∣ (A0 + rStar) := hA0_ndvd iStar hiStar_mem
      rw [hgcdL]
      simp only [hA1_dvd_star, h0, ↓reduceIte, mul_zero, sub_zero]
      rw [div_self (Nat.cast_ne_zero.mpr hL_prime.pos.ne'), mul_one]
    calc (1 : ℝ) / (L : ℝ) ^ k
        = (1 : ℝ) / (L : ℝ) ^ k *
            (if Nat.gcd L (L * Q) ∣ (A1 + rStar) then (Nat.gcd L (L * Q) : ℝ) / (L : ℝ) else 0) -
          (1 : ℝ) / (L : ℝ) ^ k *
            (if Nat.gcd L (L * Q) ∣ (A0 + rStar) then (Nat.gcd L (L * Q) : ℝ) / (L : ℝ) else 0) :=
          hL_term.symm
      _ ≤ ∑ d ∈ Finset.Icc 1 B, _ := Finset.single_le_sum hterm_nn hL_mem
  -- Choose B large enough that the M / B tail across both progressions is < δ / 4
  let δ : ℝ := coef iStar / (L : ℝ) ^ k
  have hδ_pos : 0 < δ := div_pos hcStar_pos (pow_pos (Nat.cast_pos.mpr hL_prime.pos) k)
  let Cabs : ℝ := ∑ p ∈ Iset, |coef p|
  have hCabs_pos : 0 < Cabs :=
    lt_of_lt_of_le (abs_pos.mpr hcStar_pos.ne')
      (Finset.single_le_sum (f := fun p => |coef p|) (fun _ _ => abs_nonneg _) hiStar_mem)
  obtain ⟨B0, hB0⟩ := exists_nat_gt (8 * Cabs * ((L * Q : ℕ) : ℝ) / δ)
  let B : ℕ := max L (max B0 1)
  have hLB : L ≤ B := le_max_left _ _
  have hB1 : 1 ≤ B := le_trans (le_max_right _ _) (le_max_right _ _)
  have htail_B : 2 * Cabs * (((L * Q : ℕ) : ℝ) / (B : ℝ)) < δ / 4 := by
    have hBgt : 8 * Cabs * ((L * Q : ℕ) : ℝ) / δ < (B : ℝ) :=
      lt_of_lt_of_le hB0 (by exact_mod_cast le_trans (le_max_left _ _) (le_max_right _ _))
    have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr hB1
    have hmul : 8 * Cabs * ((L * Q : ℕ) : ℝ) < (B : ℝ) * δ := (div_lt_iff₀ hδ_pos).mp hBgt
    rw [mul_div_assoc', div_lt_iff₀ hBpos]
    linarith
  -- Both subsequences Rcomb(A0 + m * (L * Q)) and Rcomb(A1 + m * (L * Q)) tend to 0
  have hsub_tendsto : ∀ A' : ℕ, A' ≡ A [MOD Q] →
      Tendsto (fun m : ℕ => Rcomb k (A' + m * (L * Q))) atTop (nhds 0) := by
    intro A' hA'
    -- For large m, A' + m * (L * Q) = A + (k0 + m * L) * Q
    have hex_m0 : ∃ m0 q0 : ℕ, A' + m0 * (L * Q) = A + q0 * Q := by
      obtain ⟨m0, hm0⟩ := exists_nat_gt (A / (L * Q))
      have hge : A ≤ A' + m0 * (L * Q) := by
        have h1 := Nat.div_add_mod A (L * Q)
        have h2 : A % (L * Q) < L * Q := Nat.mod_lt A (Nat.mul_pos hL_prime.pos hQpos)
        have h3 : (A / (L * Q) + 1) * (L * Q) ≤ m0 * (L * Q) :=
          Nat.mul_le_mul_right _ hm0
        nlinarith
      have hmod : A' + m0 * (L * Q) ≡ A [MOD Q] := by
        have h1 : A' + m0 * (L * Q) ≡ A' [MOD Q] := by
          rw [Nat.ModEq, show m0 * (L * Q) = (m0 * L) * Q by ring, Nat.add_mul_mod_self_right]
        exact h1.trans hA'
      have hdvd : Q ∣ (A' + m0 * (L * Q) - A) := (Nat.modEq_iff_dvd' hge).mp hmod.symm
      obtain ⟨q0, hq0⟩ := hdvd
      rw [mul_comm Q q0] at hq0
      exact ⟨m0, q0, by omega⟩
    obtain ⟨m0, q0, hm0⟩ := hex_m0
    have hcomp : Tendsto (fun m : ℕ => Rcomb k (A + (q0 + m * L) * Q)) atTop (nhds 0) := by
      refine hR_tendsto.comp ?_
      rw [Filter.tendsto_atTop_atTop]
      intro b
      refine ⟨b, fun m hm => ?_⟩
      have : m * 1 ≤ m * L := Nat.mul_le_mul_left m hL_prime.pos
      omega
    have hshift_eq : ∀ m : ℕ, A' + (m + m0) * (L * Q) = A + (q0 + m * L) * Q := by
      intro m
      calc A' + (m + m0) * (L * Q) = (A' + m0 * (L * Q)) + m * (L * Q) := by ring
        _ = (A + q0 * Q) + m * (L * Q) := by rw [hm0]
        _ = A + (q0 + m * L) * Q := by ring
    have hshifted : Tendsto (fun m : ℕ => Rcomb k (A' + (m + m0) * (L * Q))) atTop (nhds 0) := by
      simpa only [hshift_eq] using hcomp
    exact (Filter.tendsto_add_atTop_iff_nat m0).mp hshifted
  have hces0 := cesaro_tendsto_zero (hsub_tendsto A0 hA0_modQ)
  have hces1 := cesaro_tendsto_zero (hsub_tendsto A1 hA1_modQ)
  have hces_diff : Tendsto (fun X : ℕ =>
      (1 / (X : ℝ)) * ∑ m ∈ Finset.range X, Rcomb k (A1 + m * (L * Q)) -
      (1 / (X : ℝ)) * ∑ m ∈ Finset.range X, Rcomb k (A0 + m * (L * Q))) atTop (nhds 0) := by
    simpa using hces1.sub hces0
  rw [Metric.tendsto_atTop] at hces_diff
  obtain ⟨X1, hX1⟩ := hces_diff (δ / 4) (by linarith)
  -- Pick X large enough that both X ≥ X1 and the X-dependent Cesaro errors are < δ / 4
  let maxA : ℕ := max A0 A1 + rStar
  let Kx : ℝ := 16 * Cabs * ((B : ℝ) + 2 * Real.sqrt ((maxA + L * Q : ℕ) : ℝ) + 1) / δ
  obtain ⟨X2, hX2⟩ := exists_nat_gt (Kx ^ 2 + 1)
  let X : ℕ := max (max X1 X2) 1
  have hX_ge1 : 1 ≤ X := le_max_right _ _
  have hX_ge_X1 : X1 ≤ X := le_trans (le_max_left _ _) (le_max_left _ _)
  have hX_gt_Kx2 : Kx ^ 2 < (X : ℝ) := by
    have : (X2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr hX_ge1
  have hKx_pos : 0 < Kx :=
    div_pos (mul_pos (mul_pos (by norm_num) hCabs_pos)
      (by have : (0 : ℝ) ≤ (B : ℝ) + 2 * Real.sqrt ((maxA + L * Q : ℕ) : ℝ) :=
            add_nonneg (Nat.cast_nonneg B) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
          linarith)) hδ_pos
  have hsqrtX_gt : Kx < Real.sqrt (X : ℝ) := by
    rw [← Real.sqrt_sq hKx_pos.le]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hX_gt_Kx2
  have hX_ge_sqrtX : Real.sqrt (X : ℝ) ≤ (X : ℝ) := by
    have h1 : (1 : ℝ) ≤ X := by exact_mod_cast hX_ge1
    calc Real.sqrt (X : ℝ) ≤ Real.sqrt ((X : ℝ) * (X : ℝ)) :=
          Real.sqrt_le_sqrt (le_mul_of_one_le_right hXpos.le h1)
      _ = (X : ℝ) := Real.sqrt_mul_self hXpos.le
  -- Upper bound from hces_diff: difference < δ / 4
  have hdiff_lt :
      |(1 / (X : ℝ)) * ∑ m ∈ Finset.range X, Rcomb k (A1 + m * (L * Q)) -
        (1 / (X : ℝ)) * ∑ m ∈ Finset.range X, Rcomb k (A0 + m * (L * Q))| < δ / 4 := by
    have := hX1 X hX_ge_X1
    rwa [Real.dist_eq, sub_zero] at this
  -- Lower bound from Cesaro approximation at cutoff B
  have hces_approx_sum : ∀ A' : ℕ, 1 ≤ A' → A' ≤ max A0 A1 →
      |(1 / (X : ℝ)) * ∑ m ∈ Finset.range X, Rcomb k (A' + m * (L * Q)) -
        ∑ p ∈ Iset, coef p * muApprox k (L * Q) B (A' + shift p)| ≤
      Cabs * (((L * Q : ℕ) : ℝ) / (B : ℝ)) + δ / 8 := by
    intro A' hA'1 hA'le
    have hrew : (1 / (X : ℝ)) * ∑ m ∈ Finset.range X, Rcomb k (A' + m * (L * Q)) =
        ∑ p ∈ Iset, coef p * ((1 / (X : ℝ)) * ∑ m ∈ Finset.range X, rho k (A' + shift p + m * (L * Q))) := by
      simp_rw [hR_eq]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Finset.mul_sum]
      have harg : ∀ m : ℕ, A' + m * (L * Q) + shift p = A' + shift p + m * (L * Q) :=
        fun m => by ring
      simp_rw [harg]
      ring
    rw [hrew, ← Finset.sum_sub_distrib]
    have hXerr_le : ∀ p ∈ Iset,
        (B : ℝ) / (X : ℝ) + 2 * Real.sqrt ((A' + shift p + X * (L * Q) : ℕ) : ℝ) / (X : ℝ) ≤
        δ / (8 * Cabs) := by
      intro p hp
      have hsh_le : shift p ≤ rStar := by
        by_cases hpe : p = iStar
        · rw [hpe]
        · exact (hshift_lt p hp hpe).le
      have harg_le : ((A' + shift p + X * (L * Q) : ℕ) : ℝ) ≤ ((maxA + L * Q : ℕ) : ℝ) * (X : ℝ) := by
        have h1 : A' + shift p ≤ maxA := by dsimp [maxA]; omega
        have h2 : A' + shift p ≤ maxA * X := le_trans h1 (Nat.le_mul_of_pos_right _ hX_ge1)
        have hnat : A' + shift p + X * (L * Q) ≤ (maxA + L * Q) * X := by
          calc A' + shift p + X * (L * Q) ≤ maxA * X + X * (L * Q) := by omega
            _ = (maxA + L * Q) * X := by ring
        exact_mod_cast hnat
      have hsqrt_ub : Real.sqrt ((A' + shift p + X * (L * Q) : ℕ) : ℝ) / (X : ℝ) ≤
          Real.sqrt ((maxA + L * Q : ℕ) : ℝ) / Real.sqrt (X : ℝ) := by
        have hsq : Real.sqrt (X : ℝ) ^ 2 = (X : ℝ) := Real.sq_sqrt hXpos.le
        calc Real.sqrt ((A' + shift p + X * (L * Q) : ℕ) : ℝ) / (X : ℝ)
            ≤ Real.sqrt (((maxA + L * Q : ℕ) : ℝ) * (X : ℝ)) / (X : ℝ) := by gcongr
          _ = Real.sqrt ((maxA + L * Q : ℕ) : ℝ) * Real.sqrt (X : ℝ) / (X : ℝ) := by
              rw [Real.sqrt_mul (Nat.cast_nonneg _)]
          _ = Real.sqrt ((maxA + L * Q : ℕ) : ℝ) / Real.sqrt (X : ℝ) := by
              field_simp [hXpos.ne', (Real.sqrt_pos.mpr hXpos).ne']
              rw [hsq]
      have hB_ub : (B : ℝ) / (X : ℝ) ≤ (B : ℝ) / Real.sqrt (X : ℝ) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg B) (Real.sqrt_pos.mpr hXpos) hX_ge_sqrtX
      have htot : ((B : ℝ) + 2 * Real.sqrt ((maxA + L * Q : ℕ) : ℝ)) / Real.sqrt (X : ℝ) ≤
          δ / (8 * Cabs) := by
        rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hXpos) (mul_pos (by norm_num) hCabs_pos)]
        have hS_nn : (0 : ℝ) ≤ (B : ℝ) + 2 * Real.sqrt ((maxA + L * Q : ℕ) : ℝ) :=
          add_nonneg (Nat.cast_nonneg B) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        have hKmul : 16 * Cabs * ((B : ℝ) + 2 * Real.sqrt ((maxA + L * Q : ℕ) : ℝ) + 1) = Kx * δ := by
          dsimp [Kx]; field_simp [hδ_pos.ne']
        have h1 : ((B : ℝ) + 2 * Real.sqrt ((maxA + L * Q : ℕ) : ℝ)) * (8 * Cabs) ≤ Kx * δ := by
          rw [← hKmul]
          nlinarith [hS_nn, hCabs_pos]
        have h2 : Kx * δ ≤ δ * Real.sqrt (X : ℝ) := by
          nlinarith [hsqrtX_gt, hδ_pos]
        linarith
      have hadd : (B : ℝ) / (X : ℝ) +
          2 * Real.sqrt ((A' + shift p + X * (L * Q) : ℕ) : ℝ) / (X : ℝ) ≤
          ((B : ℝ) + 2 * Real.sqrt ((maxA + L * Q : ℕ) : ℝ)) / Real.sqrt (X : ℝ) := by
        rw [add_div, mul_div_assoc, mul_div_assoc]
        linarith
      exact le_trans hadd htot
    calc |∑ p ∈ Iset, (coef p * ((1 / (X : ℝ)) * ∑ m ∈ Finset.range X,
            rho k (A' + shift p + m * (L * Q))) - coef p * muApprox k (L * Q) B (A' + shift p))|
        ≤ ∑ p ∈ Iset, |coef p| *
            |(1 / (X : ℝ)) * ∑ m ∈ Finset.range X, rho k (A' + shift p + m * (L * Q)) -
              muApprox k (L * Q) B (A' + shift p)| := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun p _ => ?_)
          rw [← mul_sub, abs_mul]
      _ ≤ ∑ p ∈ Iset, |coef p| * (((L * Q : ℕ) : ℝ) / (B : ℝ) + δ / (8 * Cabs)) := by
          refine Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have hces := cesaro_rho_approx (k := k) (M := L * Q) (B := B) (a := A' + shift p) (X := X)
            hk (Nat.mul_pos hL_prime.pos hQpos) hB1 (by omega) hX_ge1
          have hx := hXerr_le p hp
          linarith
      _ = Cabs * (((L * Q : ℕ) : ℝ) / (B : ℝ) + δ / (8 * Cabs)) := (Finset.sum_mul _ _ _).symm
      _ = Cabs * (((L * Q : ℕ) : ℝ) / (B : ℝ)) + δ / 8 := by field_simp [hCabs_pos.ne']
  have hmu_diff :
      δ ≤ (∑ p ∈ Iset, coef p * muApprox k (L * Q) B (A1 + shift p)) -
          (∑ p ∈ Iset, coef p * muApprox k (L * Q) B (A0 + shift p)) := by
    rw [← Finset.sum_sub_distrib]
    rw [← Finset.add_sum_erase _ _ hiStar_mem]
    have hrest0 : ∑ p ∈ Iset.erase iStar,
        (coef p * muApprox k (L * Q) B (A1 + shift p) -
          coef p * muApprox k (L * Q) B (A0 + shift p)) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      rw [hmu_eq_other B p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp), sub_self]
    rw [hrest0, add_zero, ← mul_sub]
    dsimp [δ, shift, iStar]
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (hmu_star_ge B hLB) hcStar_pos.le
  have h1 := (abs_le.mp (hces_approx_sum A1 hA1_pos (le_max_right _ _))).1
  have h0 := (abs_le.mp (hces_approx_sum A0 hA0_pos (le_max_left _ _))).2
  have hdiff_ub := (abs_lt.mp hdiff_lt).2
  linarith

end Erdos252Proof

theorem OMA.solution : type_of% @Erdos252.erdos_252 :=
  fun k hk => Erdos252Proof.irrational_erdos_252_sum k hk
