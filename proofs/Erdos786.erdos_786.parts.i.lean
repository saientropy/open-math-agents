import FormalConjectures.ErdosProblems.«786»

/-!
# Disproof of Erdős Problem 786(i)

We refute `Erdos786.erdos_786.parts.i` by showing that every `A : Set ℕ` with `0 ∉ A`,
`A.HasDensity δ`, and `A.IsMulCardSet` must satisfy `δ ≤ 3 / 4` (contradicting `ε = 1 / 8`).

Call a prime `p` good if `{x | x ∈ A ∧ p * x ∈ A}` is infinite, and bad otherwise.
1. Every `a ∈ A` must be divisible by at least one bad prime (otherwise, using the prime
   factorization of `a`, we find strictly increasing fresh pairs `(x_i, p_i * x_i)` in `A`
   giving `{a, x_1, ..., x_k}` vs `{p_1 * x_1, ..., p_k * x_k}` with equal products and
   unequal cardinalities).
2. For each bad prime `p`, at most `M_p + |A^c ∩ [0, N / p + 1)|` multiples of `p` below `N`
   lie in `A`, giving upper density at most `(1 - δ) / p` for `A ∩ pℕ`, and hence `δ / p ≤ 1 - δ`.
3. If every finite subset `F` of bad primes has `∑_{p ∈ F} 1 / p < 1 / 2`, then covering
   `A ∩ [0, N)` by multiples of bad primes `< N` yields `δ ≤ 1 / 2`.
4. Otherwise, a minimal finite set `F` of bad primes with `S = ∑_{p ∈ F} 1 / p ≥ 1 / 2`
   satisfies `S ∈ [1 / 2, 1]`. Comparing the density `1 - ∏_{p ∈ F} (1 - 1 / p) ≥ S - S^2 / 2`
   of `⋃_{p ∈ F} pℕ` with `(1 - δ) * (1 + S)` forces `1 - δ ≥ 1 / 4`, i.e., `δ ≤ 3 / 4`.
-/

namespace Erdos786Disproof

open Filter Topology Erdos786

private def Good (A : Set ℕ) (p : ℕ) : Prop :=
  {x : ℕ | x ∈ A ∧ p * x ∈ A}.Infinite

private def Bad (A : Set ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ ¬ Good A p

private lemma realize_good_list {A : Set ℕ} (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ Good A p) :
    ∀ B : ℕ, ∃ (U V : Finset ℕ),
      ↑U ⊆ A ∧ ↑V ⊆ A ∧
      U.card = L.length ∧ V.card = L.length ∧
      Disjoint U V ∧
      (∀ u ∈ U, B < u) ∧ (∀ v ∈ V, B < v) ∧
      L.prod * U.prod id = V.prod id := by
  induction L with
  | nil =>
    intro B
    exact ⟨∅, ∅, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  | cons p ps ih =>
    intro B
    have hp : p.Prime ∧ Good A p := hL p (by simp)
    have hps : ∀ q ∈ ps, q.Prime ∧ Good A q := fun q hq => hL q (by simp [hq])
    obtain ⟨x, ⟨hxA, hpxA⟩, hxgt⟩ := hp.2.exists_gt (max B 1)
    have hxB : B < x := lt_of_le_of_lt (le_max_left _ _) hxgt
    have hx1 : 1 < x := lt_of_le_of_lt (le_max_right _ _) hxgt
    have hx_lt_px : x < p * x := by
      have hp2 : 2 ≤ p := hp.1.two_le
      nlinarith
    have hpxB : B < p * x := hxB.trans hx_lt_px
    obtain ⟨U, V, hUA, hVA, hUcard, hVcard, hdisj, hUgt, hVgt, hprod⟩ := ih hps (p * x)
    have hx_not_U : x ∉ U := fun h => by have := hUgt x h; omega
    have hpx_not_V : p * x ∉ V := fun h => by have := hVgt (p * x) h; omega
    have hx_not_V : x ∉ V := fun h => by have := hVgt x h; omega
    have hpx_not_U : p * x ∉ U := fun h => by have := hUgt (p * x) h; omega
    refine ⟨insert x U, insert (p * x) V, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro y hy
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hy
      rcases hy with rfl | hyU
      · exact hxA
      · exact hUA hyU
    · intro y hy
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hy
      rcases hy with rfl | hyV
      · exact hpxA
      · exact hVA hyV
    · rw [Finset.card_insert_of_notMem hx_not_U, hUcard]; simp
    · rw [Finset.card_insert_of_notMem hpx_not_V, hVcard]; simp
    · rw [Finset.disjoint_insert_left, Finset.disjoint_insert_right]
      exact ⟨by simp [hx_lt_px.ne, hx_not_V], hpx_not_U, hdisj⟩
    · intro u hu
      simp only [Finset.mem_insert] at hu
      rcases hu with rfl | huU
      · exact hxB
      · exact hpxB.trans (hUgt u huU)
    · intro v hv
      simp only [Finset.mem_insert] at hv
      rcases hv with rfl | hvV
      · exact hpxB
      · exact hpxB.trans (hVgt v hvV)
    · rw [Finset.prod_insert hx_not_U, Finset.prod_insert hpx_not_V, List.prod_cons]
      simp only [id]
      calc
        p * ps.prod * (x * U.prod id) = p * x * (ps.prod * U.prod id) := by ring
        _ = p * x * V.prod id := by rw [hprod]

private lemma exists_bad_prime_dvd {A : Set ℕ} (h0 : 0 ∉ A) (hinf : A.Infinite)
    (hmul : A.IsMulCardSet) {a : ℕ} (ha : a ∈ A) :
    ∃ p, Bad A p ∧ p ∣ a := by
  have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
  by_contra hno
  push Not at hno
  have hL : ∀ p ∈ a.primeFactorsList, p.Prime ∧ Good A p := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactorsList hp
    have hdvd : p ∣ a := Nat.dvd_of_mem_primeFactorsList hp
    have hnotbad : ¬ Bad A p := fun hb => hno p hb hdvd
    have hgood : Good A p := by
      by_contra hng
      exact hnotbad ⟨hprime, hng⟩
    exact ⟨hprime, hgood⟩
  obtain ⟨U, V, hUA, hVA, hUcard, hVcard, _, hUgt, _, hprod⟩ :=
    realize_good_list a.primeFactorsList hL a
  have ha_not_U : a ∉ U := fun h => by have := hUgt a h; omega
  have hU'_sub : (↑(insert a U) : Set ℕ) ⊆ A := by
    intro y hy
    simp only [Finset.coe_insert, Set.mem_insert_iff] at hy
    rcases hy with rfl | hyU
    · exact ha
    · exact hUA hyU
  have hprod_eq : (insert a U).prod id = V.prod id := by
    rw [Finset.prod_insert ha_not_U]
    simp only [id]
    rw [← Nat.prod_primeFactorsList ha0]
    exact hprod
  have hcard_eq := hmul (insert a U) V hU'_sub hVA hprod_eq
  rw [Finset.card_insert_of_notMem ha_not_U, hUcard, hVcard] at hcard_eq
  omega

private lemma partialDensity_eq_filter (A : Set ℕ) (n : ℕ) :
    letI := Classical.decPred (· ∈ A)
    A.partialDensity Set.univ n =
      (((Finset.range n).filter (· ∈ A)).card : ℝ) / (n : ℝ) := by
  classical
  have hset : A ∩ Set.Iio n = ↑((Finset.range n).filter (· ∈ A)) := by
    ext m
    simp [Set.mem_Iio, and_comm]
  rw [Set.partialDensity, Set.inter_univ, Set.univ_inter, hset, Set.ncard_coe_finset,
    Nat.ncard_Iio]

private lemma tendsto_compl_density {A : Set ℕ} {δ : ℝ} (hd : A.HasDensity δ) :
    letI := Classical.decPred (· ∈ A)
    Tendsto (fun n : ℕ => (((Finset.range n).filter (· ∉ A)).card : ℝ) / (n : ℝ))
      atTop (𝓝 (1 - δ)) := by
  classical
  have hA : Tendsto (fun n : ℕ => (((Finset.range n).filter (· ∈ A)).card : ℝ) / (n : ℝ))
      atTop (𝓝 δ) := hd.congr (fun n => partialDensity_eq_filter A n)
  have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - (((Finset.range n).filter (· ∈ A)).card : ℝ) / (n : ℝ))
      atTop (𝓝 (1 - δ)) := tendsto_const_nhds.sub hA
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hsum :
      ((Finset.range n).filter (· ∈ A)).card + ((Finset.range n).filter (· ∉ A)).card = n := by
    simpa [Finset.card_range] using
      Finset.card_filter_add_card_filter_not (s := Finset.range n) (p := (· ∈ A))
  have hsumR :
      (((Finset.range n).filter (· ∈ A)).card : ℝ) +
        (((Finset.range n).filter (· ∉ A)).card : ℝ) = (n : ℝ) := by
    exact_mod_cast hsum
  field_simp [hn0]
  linarith

private lemma tendsto_div_add_one_div (p : ℕ) (hp : 0 < p) :
    Tendsto (fun n : ℕ => ((n / p + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 (1 / (p : ℝ))) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hup : Tendsto (fun n : ℕ => 1 / (p : ℝ) + 2 * (1 / (n : ℝ)))
      atTop (𝓝 (1 / (p : ℝ))) := by
    simpa using Tendsto.const_add (1 / (p : ℝ))
      (Tendsto.const_mul (2 : ℝ) tendsto_one_div_atTop_nhds_zero_nat)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h1 : n < (n / p + 1) * p := by
      have := Nat.lt_div_mul_add (a := n) hp
      linarith
    have h1R : (n : ℝ) < ((n / p + 1 : ℕ) : ℝ) * (p : ℝ) := by exact_mod_cast h1
    rw [le_div_iff₀ hn0]
    have : 1 / (p : ℝ) * (n : ℝ) ≤ ((n / p + 1 : ℕ) : ℝ) := by
      rw [one_div, inv_mul_le_iff₀ hpR]
      linarith
    exact this
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h2 : (n / p) * p ≤ n := Nat.div_mul_le_self n p
    have h2R : ((n / p : ℕ) : ℝ) * (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
    have hdiv : ((n / p : ℕ) : ℝ) ≤ (n : ℝ) / (p : ℝ) := (le_div_iff₀ hpR).mpr h2R
    rw [div_le_iff₀ hn0]
    have hstep : ((n / p + 1 : ℕ) : ℝ) ≤ (n : ℝ) / (p : ℝ) + 1 := by
      push_cast
      linarith
    have heq : (1 / (p : ℝ) + 2 * (1 / (n : ℝ))) * (n : ℝ) = (n : ℝ) / (p : ℝ) + 2 := by
      field_simp [hn0.ne', hpR.ne']
    linarith

private lemma bad_prime_upper_bound {A : Set ℕ} {δ : ℝ} (hd : A.HasDensity δ)
    {p : ℕ} (hp : Bad A p) :
    letI := Classical.decPred (· ∈ A)
    ∃ f : ℕ → ℝ,
      Tendsto f atTop (𝓝 ((1 - δ) / (p : ℝ))) ∧
      ∀ n : ℕ, 1 ≤ n →
        (((Finset.range n).filter (fun y => p ∣ y ∧ y ∈ A)).card : ℝ) / (n : ℝ) ≤ f n := by
  classical
  have hfin : {x : ℕ | x ∈ A ∧ p * x ∈ A}.Finite := Set.not_infinite.mp hp.2
  obtain ⟨M, hM⟩ := Finset.exists_nat_subset_range hfin.toFinset
  have hnot_both : ∀ x : ℕ, M ≤ x → ¬ (x ∈ A ∧ p * x ∈ A) := by
    intro x hx hboth
    have hmem : x ∈ hfin.toFinset := hfin.mem_toFinset.mpr hboth
    have hlt : x < M := Finset.mem_range.mp (hM hmem)
    omega
  let f : ℕ → ℝ := fun n =>
    (M : ℝ) / (n : ℝ) +
      ((((Finset.range (n / p + 1)).filter (· ∉ A)).card : ℝ) / ((n / p + 1 : ℕ) : ℝ)) *
        (((n / p + 1 : ℕ) : ℝ) / (n : ℝ))
  refine ⟨f, ?_, ?_⟩
  · have hM_lim : Tendsto (fun n : ℕ => (M : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        Tendsto.const_mul (M : ℝ) tendsto_one_div_atTop_nhds_zero_nat
    have hgrow : Tendsto (fun n : ℕ => n / p + 1) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨b * p, fun n hn => ?_⟩
      have : b ≤ n / p := (Nat.le_div_iff_mul_le hp.1.pos).mpr hn
      omega
    have hcompl := (tendsto_compl_density hd).comp hgrow
    have hratio := tendsto_div_add_one_div p hp.1.pos
    have hprod := hcompl.mul hratio
    simpa [f, div_eq_mul_inv] using hM_lim.add hprod
  · intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnp0 : ((n / p + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    let S := (Finset.range n).filter (fun y => p ∣ y ∧ y ∈ A)
    let T := Finset.range M ∪ (Finset.range (n / p + 1)).filter (· ∉ A)
    have hinj : Set.InjOn (· / p) (S : Set ℕ) := by
      intro a ha b hb hab
      dsimp only at hab
      simp only [S, Finset.mem_coe, Finset.mem_filter] at ha hb
      have h1 : p * (a / p) = a := Nat.mul_div_cancel' ha.2.1
      have h2 : p * (b / p) = b := Nat.mul_div_cancel' hb.2.1
      rw [← h1, ← h2, hab]
    have hmaps : S.image (· / p) ⊆ T := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      simp only [S, Finset.mem_filter, Finset.mem_range] at hy
      simp only [T, Finset.mem_union, Finset.mem_range, Finset.mem_filter]
      by_cases hlt : y / p < M
      · exact Or.inl hlt
      · refine Or.inr ⟨?_, ?_⟩
        · have : y / p ≤ n / p := Nat.div_le_div_right hy.1.le
          omega
        · intro hxA
          have hpy : p * (y / p) = y := Nat.mul_div_cancel' hy.2.1
          exact hnot_both (y / p) (by omega) ⟨hxA, hpy.symm ▸ hy.2.2⟩
    have hcard : S.card ≤ M + ((Finset.range (n / p + 1)).filter (· ∉ A)).card := by
      calc
        S.card = (S.image (· / p)).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ T.card := Finset.card_le_card hmaps
        _ ≤ (Finset.range M).card + ((Finset.range (n / p + 1)).filter (· ∉ A)).card :=
            Finset.card_union_le _ _
        _ = M + ((Finset.range (n / p + 1)).filter (· ∉ A)).card := by simp
    have hcardR : (S.card : ℝ) ≤ (M : ℝ) + (((Finset.range (n / p + 1)).filter (· ∉ A)).card : ℝ) := by
      exact_mod_cast hcard
    have hf_eq :
        f n = ((M : ℝ) + (((Finset.range (n / p + 1)).filter (· ∉ A)).card : ℝ)) / (n : ℝ) := by
      dsimp only [f]
      field_simp [hn0.ne', hnp0]
    rw [hf_eq]
    exact div_le_div_of_nonneg_right hcardR hn0.le

private lemma bad_prime_ge {A : Set ℕ} {δ : ℝ} (hd : A.HasDensity δ)
    {p : ℕ} (hp : Bad A p) :
    δ / (p : ℝ) ≤ 1 - δ := by
  classical
  obtain ⟨f, hf_lim, hf_le⟩ := bad_prime_upper_bound hd hp
  have hcompl := tendsto_compl_density hd
  have hsum_lim : Tendsto (fun n : ℕ => f n + (((Finset.range n).filter (· ∉ A)).card : ℝ) / (n : ℝ))
      atTop (𝓝 ((1 - δ) / (p : ℝ) + (1 - δ))) := hf_lim.add hcompl
  have hlow_lim : Tendsto (fun n : ℕ => ((n / p : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 (1 / (p : ℝ))) := by
    have h1 := tendsto_div_add_one_div p hp.1.pos
    have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hsub := h1.sub h2
    simp only [sub_zero] at hsub
    refine hsub.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp [hn0]
    ring
  have hle_ev :
      ∀ᶠ n : ℕ in atTop,
        ((n / p : ℕ) : ℝ) / (n : ℝ) ≤
          f n + (((Finset.range n).filter (· ∉ A)).card : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hmult_card : n / p ≤ ((Finset.range n).filter (fun y => p ∣ y)).card := by
      let g : ℕ → ℕ := fun k => k * p
      have hsub : (Finset.range (n / p)).image g ⊆ (Finset.range n).filter (fun y => p ∣ y) := by
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨k, hk, rfl⟩
        rw [Finset.mem_range] at hk
        simp only [Finset.mem_filter, Finset.mem_range, g]
        have hlt : k * p < n := by
          calc
            k * p < (n / p) * p := Nat.mul_lt_mul_of_pos_right hk hp.1.pos
            _ ≤ n := Nat.div_mul_le_self n p
        exact ⟨hlt, dvd_mul_left p k⟩
      have hinj : Set.InjOn g ((Finset.range (n / p)) : Set ℕ) := by
        intro a _ b _ hab
        exact Nat.eq_of_mul_eq_mul_right hp.1.pos hab
      calc
        n / p = ((Finset.range (n / p)).image g).card := by
          rw [Finset.card_image_of_injOn hinj, Finset.card_range]
        _ ≤ ((Finset.range n).filter (fun y => p ∣ y)).card := Finset.card_le_card hsub
    have hsplit :
        ((Finset.range n).filter (fun y => p ∣ y)).card ≤
          ((Finset.range n).filter (fun y => p ∣ y ∧ y ∈ A)).card +
            ((Finset.range n).filter (· ∉ A)).card := by
      have hsub :
          (Finset.range n).filter (fun y => p ∣ y) ⊆
            (Finset.range n).filter (fun y => p ∣ y ∧ y ∈ A) ∪
              (Finset.range n).filter (· ∉ A) := by
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_union] at hy ⊢
        by_cases hyA : y ∈ A
        · exact Or.inl ⟨hy.1, hy.2, hyA⟩
        · exact Or.inr ⟨hy.1, hyA⟩
      exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have htot : (n / p : ℕ) ≤
        ((Finset.range n).filter (fun y => p ∣ y ∧ y ∈ A)).card +
          ((Finset.range n).filter (· ∉ A)).card := hmult_card.trans hsplit
    have htotR :
        ((n / p : ℕ) : ℝ) / (n : ℝ) ≤
          (((Finset.range n).filter (fun y => p ∣ y ∧ y ∈ A)).card : ℝ) / (n : ℝ) +
            (((Finset.range n).filter (· ∉ A)).card : ℝ) / (n : ℝ) := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast htot) hn0.le
    linarith [hf_le n hn]
  have hineq := le_of_tendsto_of_tendsto hlow_lim hsum_lim hle_ev
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.1.pos
  rw [div_le_iff₀ hp_pos]
  have := mul_le_mul_of_nonneg_right hineq hp_pos.le
  field_simp [hp_pos.ne'] at this ⊢
  linarith

private lemma prod_one_sub_le (F : Finset ℕ) (x : ℕ → ℝ)
    (hx : ∀ i ∈ F, 0 ≤ x i ∧ x i ≤ 1) :
    ∏ i ∈ F, (1 - x i) ≤ 1 - (∑ i ∈ F, x i) + (∑ i ∈ F, x i) ^ 2 / 2 := by
  classical
  induction F using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have ha_bounds := hx a (Finset.mem_insert_self a s)
    have hs_bounds : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1 :=
      fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have ihs := ih hs_bounds
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have h1 : 0 ≤ 1 - x a := by linarith [ha_bounds.2]
    have h2 : (1 - x a) * ∏ i ∈ s, (1 - x i) ≤
        (1 - x a) * (1 - ∑ i ∈ s, x i + (∑ i ∈ s, x i) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left ihs h1
    nlinarith [ha_bounds.1, sq_nonneg (∑ i ∈ s, x i), sq_nonneg (x a)]

private lemma totient_prod_primes (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) :
    ((Nat.totient (∏ p ∈ F, p) : ℝ) / ((∏ p ∈ F, p : ℕ) : ℝ)) =
      ∏ p ∈ F, (1 - 1 / (p : ℝ)) := by
  classical
  induction F using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have ha_prime : a.Prime := hF a (Finset.mem_insert_self a s)
    have hs_prime : ∀ p ∈ s, p.Prime := fun p hp => hF p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      have hne : a ≠ p := fun h => ha (h ▸ hp)
      exact (Nat.coprime_primes ha_prime (hs_prime p hp)).mpr hne
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.totient_mul hcop,
      Nat.totient_prime ha_prime]
    have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha_prime.pos
    have ha_one : 1 ≤ a := ha_prime.one_lt.le
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub ha_one, Nat.cast_one, mul_div_mul_comm,
      ih hs_prime]
    congr 1
    field_simp [ha_pos.ne']

private lemma exists_minimal_subset_ge {s : Finset ℕ} {f : ℕ → ℝ} {c : ℝ}
    (hs : c ≤ ∑ i ∈ s, f i) :
    ∃ F ⊆ s, c ≤ ∑ i ∈ F, f i ∧ ∀ a ∈ F, ∑ i ∈ F.erase a, f i < c := by
  classical
  induction hcard : s.card generalizing s with
  | zero =>
    have hse : s = ∅ := Finset.card_eq_zero.mp hcard
    subst hse
    exact ⟨∅, Finset.Subset.refl _, hs, by simp⟩
  | succ k ih =>
    by_cases hmin : ∀ a ∈ s, ∑ i ∈ s.erase a, f i < c
    · exact ⟨s, Finset.Subset.refl _, hs, hmin⟩
    · push Not at hmin
      obtain ⟨a, ha, hge⟩ := hmin
      have hcard' : (s.erase a).card = k := by
        rw [Finset.card_erase_of_mem ha, hcard]
        omega
      obtain ⟨F, hFsub, hFge, hFmin⟩ := ih hge hcard'
      exact ⟨F, hFsub.trans (Finset.erase_subset a s), hFge, hFmin⟩

private lemma density_le_three_fourths {A : Set ℕ} {δ : ℝ}
    (h0 : 0 ∉ A) (hd : A.HasDensity δ) (hmul : A.IsMulCardSet) :
    δ ≤ 3 / 4 := by
  classical
  by_contra hgt
  push Not at hgt
  have hA_inf : A.Infinite := by
    intro hfin
    obtain ⟨M, hM⟩ := Finset.exists_nat_subset_range hfin.toFinset
    have hA_lim : Tendsto (fun n : ℕ => (((Finset.range n).filter (· ∈ A)).card : ℝ) / (n : ℝ))
        atTop (𝓝 δ) := hd.congr (fun n => partialDensity_eq_filter A n)
    have hzero : Tendsto (fun n : ℕ => (M : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        Tendsto.const_mul (M : ℝ) tendsto_one_div_atTop_nhds_zero_nat
    have hle : ∀ᶠ n : ℕ in atTop,
        (((Finset.range n).filter (· ∈ A)).card : ℝ) / (n : ℝ) ≤ (M : ℝ) / (n : ℝ) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hsub : (Finset.range n).filter (· ∈ A) ⊆ Finset.range M := by
        intro x hx
        exact hM (hfin.mem_toFinset.mpr (Finset.mem_filter.mp hx).2)
      have hcard : ((Finset.range n).filter (· ∈ A)).card ≤ M := by
        simpa using Finset.card_le_card hsub
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hn0.le
    have hδ0 : δ ≤ 0 := le_of_tendsto_of_tendsto hA_lim hzero hle
    linarith
  by_cases hbig : ∃ F : Finset ℕ, (∀ p ∈ F, Bad A p) ∧ (1 / 2 : ℝ) ≤ ∑ p ∈ F, (1 : ℝ) / (p : ℝ)
  · obtain ⟨F₀, hF₀bad, hF₀ge⟩ := hbig
    obtain ⟨F, hFsub, hFge, hFmin⟩ := exists_minimal_subset_ge hF₀ge
    have hFbad : ∀ p ∈ F, Bad A p := fun p hp => hF₀bad p (hFsub hp)
    have hFprime : ∀ p ∈ F, p.Prime := fun p hp => (hFbad p hp).1
    have hFne : F.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      subst hempty
      simp at hFge
      linarith
    obtain ⟨q, hqF⟩ := hFne
    have hq_inv : (1 : ℝ) / (q : ℝ) ≤ 1 / 2 := by
      have hq_ge := bad_prime_ge hd (hFbad q hqF)
      have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (hFprime q hqF).pos
      have : (3 / 4 : ℝ) / (q : ℝ) ≤ 1 / 4 := by
        have h1 : (3 / 4 : ℝ) / (q : ℝ) ≤ δ / (q : ℝ) :=
          div_le_div_of_nonneg_right hgt.le hq_pos.le
        linarith
      have : (3 : ℝ) ≤ (q : ℝ) := by
        rw [div_le_iff₀ hq_pos] at this
        linarith
      rw [div_le_div_iff₀ hq_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    set S : ℝ := ∑ p ∈ F, (1 : ℝ) / (p : ℝ)
    have hS_le : S ≤ 1 := by
      have hsplit : S = (1 : ℝ) / (q : ℝ) + ∑ p ∈ F.erase q, (1 : ℝ) / (p : ℝ) :=
        (Finset.add_sum_erase _ _ hqF).symm
      have hlt := hFmin q hqF
      linarith
    let P : ℕ := ∏ p ∈ F, p
    have hP_pos : 0 < P := Finset.prod_pos fun p hp => (hFprime p hp).pos
    have hP_posR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP_pos
    let multP := (Finset.range P).filter (fun r => ∃ p ∈ F, p ∣ r)
    have hmultP_card : multP.card = P - Nat.totient P := by
      have hcompl :
          (Finset.range P).filter (fun r => ¬ ∃ p ∈ F, p ∣ r) =
            (Finset.range P).filter (fun r => P.Coprime r) := by
        ext r
        simp only [Finset.mem_filter, not_exists]
        refine and_congr_right fun _ => ?_
        constructor
        · intro hnd
          rw [Nat.coprime_iff_gcd_eq_one]
          by_contra hne1
          obtain ⟨d, hdprime, hddvd⟩ := Nat.exists_prime_and_dvd hne1
          have hdP : d ∣ P := hddvd.trans (Nat.gcd_dvd_left P r)
          have hdr : d ∣ r := hddvd.trans (Nat.gcd_dvd_right P r)
          obtain ⟨p, hpF, hdp⟩ := (hdprime.prime.dvd_finsetProd_iff _).mp hdP
          have hdeq : d = p := (Nat.prime_dvd_prime_iff_eq hdprime (hFprime p hpF)).mp hdp
          exact hnd p ⟨hpF, hdeq ▸ hdr⟩
        · rintro hcop p ⟨hpF, hpr⟩
          have hpP : p ∣ P := Finset.dvd_prod_of_mem _ hpF
          have hpgcd : p ∣ Nat.gcd P r := Nat.dvd_gcd hpP hpr
          rw [hcop.gcd_eq_one] at hpgcd
          exact (hFprime p hpF).not_dvd_one hpgcd
      have hsum :
          multP.card + ((Finset.range P).filter (fun r => ¬ ∃ p ∈ F, p ∣ r)).card = P := by
        simpa [multP, Finset.card_range] using
          Finset.card_filter_add_card_filter_not
            (s := Finset.range P) (p := fun r => ∃ p ∈ F, p ∣ r)
      rw [hcompl, ← Nat.totient_eq_card_coprime] at hsum
      omega
    have htot_le : Nat.totient P ≤ P := Nat.totient_le P
    have hU_low : ∀ n : ℕ, (n / P) * (P - Nat.totient P) ≤
        ((Finset.range n).filter (fun y => ∃ p ∈ F, p ∣ y)).card := by
      intro n
      let D := Finset.range (n / P) ×ˢ multP
      let g : ℕ × ℕ → ℕ := fun qr => qr.1 * P + qr.2
      have hsub : D.image g ⊆ (Finset.range n).filter (fun y => ∃ p ∈ F, p ∣ y) := by
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨⟨k, r⟩, hkr, rfl⟩
        simp only [D, multP, Finset.mem_product, Finset.mem_range, Finset.mem_filter] at hkr
        simp only [Finset.mem_filter, Finset.mem_range, g]
        refine ⟨?_, ?_⟩
        · have hk1 : k + 1 ≤ n / P := hkr.1
          have hdiv : (n / P) * P ≤ n := Nat.div_mul_le_self n P
          nlinarith [hkr.2.1]
        · obtain ⟨p, hpF, hpr⟩ := hkr.2.2
          have hpP : p ∣ P := Finset.dvd_prod_of_mem _ hpF
          exact ⟨p, hpF, dvd_add (dvd_mul_of_dvd_right hpP k) hpr⟩
      have hinj : Set.InjOn g (D : Set (ℕ × ℕ)) := by
        intro a ha b hb hab
        simp only [D, multP, Finset.mem_coe, Finset.mem_product, Finset.mem_range,
          Finset.mem_filter] at ha hb
        have hmod : (a.1 * P + a.2) % P = (b.1 * P + b.2) % P := congrArg (· % P) hab
        rw [Nat.mul_add_mod_self_right, Nat.mul_add_mod_self_right,
          Nat.mod_eq_of_lt ha.2.1, Nat.mod_eq_of_lt hb.2.1] at hmod
        have hk : a.1 = b.1 := by
          dsimp only [g] at hab
          exact Nat.eq_of_mul_eq_mul_right hP_pos (by omega)
        exact Prod.ext hk hmod
      calc
        (n / P) * (P - Nat.totient P) = D.card := by
          simp [D, Finset.card_product, hmultP_card]
        _ = (D.image g).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ ((Finset.range n).filter (fun y => ∃ p ∈ F, p ∣ y)).card := Finset.card_le_card hsub
    have hlow_lim :
        Tendsto (fun n : ℕ => (((n / P) * (P - Nat.totient P) : ℕ) : ℝ) / (n : ℝ))
          atTop (𝓝 (1 - ∏ p ∈ F, (1 - (1 : ℝ) / (p : ℝ)))) := by
      have hdivP : Tendsto (fun n : ℕ => ((n / P : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 (1 / (P : ℝ))) := by
        have h1 := tendsto_div_add_one_div P hP_pos
        have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
          tendsto_one_div_atTop_nhds_zero_nat
        have hsub := h1.sub h2
        simp only [sub_zero] at hsub
        refine hsub.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hn0 : (n : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp [hn0]
        ring
      have hmul_lim := hdivP.mul_const ((P - Nat.totient P : ℕ) : ℝ)
      have hval : 1 / (P : ℝ) * ((P - Nat.totient P : ℕ) : ℝ) =
          1 - ∏ p ∈ F, (1 - (1 : ℝ) / (p : ℝ)) := by
        rw [← totient_prod_primes F hFprime, Nat.cast_sub htot_le]
        dsimp only [P]
        have hP0 : ((∏ p ∈ F, p : ℕ) : ℝ) ≠ 0 := hP_posR.ne'
        field_simp [hP0]
      rw [hval] at hmul_lim
      refine hmul_lim.congr fun n => ?_
      push_cast
      ring
    have hex_f : ∀ p : ℕ, p ∈ F →
        ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 ((1 - δ) / (p : ℝ))) ∧
          ∀ n : ℕ, 1 ≤ n →
            (((Finset.range n).filter (fun y => p ∣ y ∧ y ∈ A)).card : ℝ) / (n : ℝ) ≤ f n :=
      fun p hp => bad_prime_upper_bound hd (hFbad p hp)
    let fp : ℕ → ℕ → ℝ := fun p =>
      if hp : p ∈ F then Classical.choose (hex_f p hp) else fun _ => 0
    have hfp_lim : ∀ p ∈ F, Tendsto (fp p) atTop (𝓝 ((1 - δ) / (p : ℝ))) := fun p hp => by
      simp only [fp, dif_pos hp]
      exact (Classical.choose_spec (hex_f p hp)).1
    have hfp_le : ∀ p ∈ F, ∀ n : ℕ, 1 ≤ n →
        (((Finset.range n).filter (fun y => p ∣ y ∧ y ∈ A)).card : ℝ) / (n : ℝ) ≤ fp p n :=
      fun p hp => by
        simp only [fp, dif_pos hp]
        exact (Classical.choose_spec (hex_f p hp)).2
    have hup_lim :
        Tendsto (fun n : ℕ =>
            (((Finset.range n).filter (· ∉ A)).card : ℝ) / (n : ℝ) + ∑ p ∈ F, fp p n)
          atTop (𝓝 ((1 - δ) * (1 + S))) := by
      have hsum := tendsto_finsetSum F hfp_lim
      have htot := (tendsto_compl_density hd).add hsum
      have hlim_eq : (1 - δ) + ∑ p ∈ F, (1 - δ) / (p : ℝ) = (1 - δ) * (1 + S) := by
        dsimp only [S]
        have hfactor : ∑ p ∈ F, (1 - δ) / (p : ℝ) = (1 - δ) * ∑ p ∈ F, (1 : ℝ) / (p : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
        rw [hfactor]
        ring
      rwa [hlim_eq] at htot
    have hineq_ev :
        ∀ᶠ n : ℕ in atTop,
          (((n / P) * (P - Nat.totient P) : ℕ) : ℝ) / (n : ℝ) ≤
            (((Finset.range n).filter (· ∉ A)).card : ℝ) / (n : ℝ) + ∑ p ∈ F, fp p n := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hcov :
          (Finset.range n).filter (fun y => ∃ p ∈ F, p ∣ y) ⊆
            (Finset.range n).filter (· ∉ A) ∪
              F.biUnion (fun p => (Finset.range n).filter (fun y => p ∣ y ∧ y ∈ A)) := by
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_biUnion] at hy ⊢
        by_cases hyA : y ∈ A
        · obtain ⟨p, hpF, hpy⟩ := hy.2
          exact Or.inr ⟨p, hpF, hy.1, hpy, hyA⟩
        · exact Or.inl ⟨hy.1, hyA⟩
      have hcard_le :
          ((Finset.range n).filter (fun y => ∃ p ∈ F, p ∣ y)).card ≤
            ((Finset.range n).filter (· ∉ A)).card +
              ∑ p ∈ F, ((Finset.range n).filter (fun y => p ∣ y ∧ y ∈ A)).card := by
        calc
          ((Finset.range n).filter (fun y => ∃ p ∈ F, p ∣ y)).card
              ≤ ((Finset.range n).filter (· ∉ A) ∪
                  F.biUnion (fun p => (Finset.range n).filter (fun y => p ∣ y ∧ y ∈ A))).card :=
                Finset.card_le_card hcov
          _ ≤ ((Finset.range n).filter (· ∉ A)).card +
                (F.biUnion (fun p => (Finset.range n).filter (fun y => p ∣ y ∧ y ∈ A))).card :=
                Finset.card_union_le _ _
          _ ≤ ((Finset.range n).filter (· ∉ A)).card +
                ∑ p ∈ F, ((Finset.range n).filter (fun y => p ∣ y ∧ y ∈ A)).card :=
                Nat.add_le_add_left Finset.card_biUnion_le _
      have hcard_comb := (hU_low n).trans hcard_le
      have hR :
          (((n / P) * (P - Nat.totient P) : ℕ) : ℝ) / (n : ℝ) ≤
            (((Finset.range n).filter (· ∉ A)).card : ℝ) / (n : ℝ) +
              ∑ p ∈ F, (((Finset.range n).filter (fun y => p ∣ y ∧ y ∈ A)).card : ℝ) / (n : ℝ) := by
        rw [← Finset.sum_div, ← add_div]
        apply div_le_div_of_nonneg_right _ hn0.le
        exact_mod_cast hcard_comb
      have hsum_le :
          ∑ p ∈ F, (((Finset.range n).filter (fun y => p ∣ y ∧ y ∈ A)).card : ℝ) / (n : ℝ) ≤
            ∑ p ∈ F, fp p n :=
        Finset.sum_le_sum fun p hp => hfp_le p hp n hn
      linarith
    have hlim_ineq := le_of_tendsto_of_tendsto hlow_lim hup_lim hineq_ev
    have hprod_le : ∏ p ∈ F, (1 - (1 : ℝ) / (p : ℝ)) ≤ 1 - S + S ^ 2 / 2 := by
      refine prod_one_sub_le F (fun p => (1 : ℝ) / (p : ℝ)) fun p hp => ?_
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hFprime p hp).one_lt.le
      exact ⟨by positivity, div_le_one_of_le₀ hp1 (by positivity)⟩
    have hquad : (1 + S) / 4 ≤ S - S ^ 2 / 2 := by nlinarith [hFge, hS_le]
    nlinarith [hlim_ineq, hprod_le, hquad, hFge]
  · push Not at hbig
    have hA_lim : Tendsto (fun n : ℕ => (((Finset.range n).filter (· ∈ A)).card : ℝ) / (n : ℝ))
        atTop (𝓝 δ) := hd.congr (fun n => partialDensity_eq_filter A n)
    have hle_half :
        ∀ᶠ n : ℕ in atTop,
          (((Finset.range n).filter (· ∈ A)).card : ℝ) / (n : ℝ) ≤ 1 / 2 := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      let FN := (Finset.range n).filter (Bad A)
      have hFN_bad : ∀ p ∈ FN, Bad A p := fun p hp => (Finset.mem_filter.mp hp).2
      have hFN_sum : ∑ p ∈ FN, (1 : ℝ) / (p : ℝ) < 1 / 2 := hbig FN hFN_bad
      have hcov :
          (Finset.range n).filter (· ∈ A) ⊆
            FN.biUnion (fun p => (Finset.Ico 1 n).filter (fun y => p ∣ y)) := by
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_range] at ha
        obtain ⟨p, hpbad, hpa⟩ := exists_bad_prime_dvd h0 hA_inf hmul ha.2
        have ha_pos : 0 < a := Nat.pos_of_ne_zero (fun h => h0 (h ▸ ha.2))
        have hp_le_a : p ≤ a := Nat.le_of_dvd ha_pos hpa
        refine Finset.mem_biUnion.mpr ⟨p, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_le_of_lt hp_le_a ha.1), hpbad⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨ha_pos, ha.1⟩, hpa⟩
      have hmult_le : ∀ p ∈ FN,
          (((Finset.Ico 1 n).filter (fun y => p ∣ y)).card : ℝ) ≤ (n : ℝ) / (p : ℝ) := by
        intro p hp
        have hp_pos : 0 < p := (hFN_bad p hp).1.pos
        have hp_posR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pos
        let S := (Finset.Ico 1 n).filter (fun y => p ∣ y)
        have hinj : Set.InjOn (· / p) (S : Set ℕ) := by
          intro a ha b hb hab
          dsimp only at hab
          simp only [S, Finset.mem_coe, Finset.mem_filter] at ha hb
          have h1 : p * (a / p) = a := Nat.mul_div_cancel' ha.2
          have h2 : p * (b / p) = b := Nat.mul_div_cancel' hb.2
          rw [← h1, ← h2, hab]
        have hmaps : S.image (· / p) ⊆ Finset.Icc 1 (n / p) := by
          intro k hk
          rcases Finset.mem_image.mp hk with ⟨y, hy, rfl⟩
          simp only [S, Finset.mem_filter, Finset.mem_Ico] at hy
          rw [Finset.mem_Icc]
          have hy_ge_p : p ≤ y := Nat.le_of_dvd (by omega) hy.2
          exact ⟨Nat.div_pos hy_ge_p hp_pos, Nat.div_le_div_right hy.1.2.le⟩
        have hcard : S.card ≤ n / p := by
          calc
            S.card = (S.image (· / p)).card := (Finset.card_image_of_injOn hinj).symm
            _ ≤ (Finset.Icc 1 (n / p)).card := Finset.card_le_card hmaps
            _ = n / p := by simp [Nat.card_Icc]
        have hdiv : ((n / p : ℕ) : ℝ) * (p : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast Nat.div_mul_le_self n p
        calc
          (S.card : ℝ) ≤ ((n / p : ℕ) : ℝ) := by exact_mod_cast hcard
          _ ≤ (n : ℝ) / (p : ℝ) := (le_div_iff₀ hp_posR).mpr hdiv
      have hcard_le :
          (((Finset.range n).filter (· ∈ A)).card : ℝ) ≤
            ∑ p ∈ FN, (n : ℝ) / (p : ℝ) := by
        have h1 : ((Finset.range n).filter (· ∈ A)).card ≤
            ∑ p ∈ FN, ((Finset.Ico 1 n).filter (fun y => p ∣ y)).card :=
          (Finset.card_le_card hcov).trans Finset.card_biUnion_le
        calc
          (((Finset.range n).filter (· ∈ A)).card : ℝ)
              ≤ ∑ p ∈ FN, (((Finset.Ico 1 n).filter (fun y => p ∣ y)).card : ℝ) := by
                exact_mod_cast h1
          _ ≤ ∑ p ∈ FN, (n : ℝ) / (p : ℝ) := Finset.sum_le_sum hmult_le
      have hsum_eq : ∑ p ∈ FN, (n : ℝ) / (p : ℝ) = (n : ℝ) * ∑ p ∈ FN, (1 : ℝ) / (p : ℝ) := by
        simp_rw [div_eq_mul_inv, one_mul, ← Finset.mul_sum]
      rw [div_le_iff₀ hn0]
      linarith [hcard_le, hsum_eq, mul_lt_mul_of_pos_left hFN_sum hn0]
    have hδ_half : δ ≤ 1 / 2 := le_of_tendsto hA_lim hle_half
    linarith

end Erdos786Disproof

theorem OMA.disproof : ¬ (type_of% @Erdos786.erdos_786.parts.i) := by
  intro h
  obtain ⟨A, δ, h0, hδ, hdens, hmul⟩ := h (1 / 8) (by norm_num) (by norm_num)
  have hle := Erdos786Disproof.density_le_three_fourths h0 hdens hmul
  linarith
