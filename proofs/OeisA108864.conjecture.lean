import FormalConjectures.OEIS.«108864»

/-!
Disproof of `OeisA108864.conjecture`:
The odd integer `N = 815634435 = 3 * 5 * 7 * 11 * 547 * 1291` satisfies
`sigma_1(N) = 1631268864 = 2 * N - 6 <= 2 * N`, so `perfectDeficiency N = 6 <= 10`
and hence `A N` holds. Moreover, there are at least 59 elements of `A` strictly less
than `N` (30 powers of 2 plus 29 numbers of the form `2^k * p` with `2^(k+1) - 1 <= p <= 2^(k+1) + 9`),
so `Nat.count A N >= 59 > 58` and `a (Nat.count A N) = N` is odd.
-/

private def greedyStep (n m d : ℕ) : ℕ :=
  if d ∣ n ∧ d ≤ m then m - d else m

private def divSum (n k : ℕ) : ℕ :=
  ∑ d ∈ (Finset.range k).filter (· ∣ n), d

private lemma divSum_succ (n k : ℕ) :
    divSum n (k + 1) = divSum n k + if k ∣ n then k else 0 := by
  unfold divSum
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.sum_insert (by simp), add_comm]
  · simp

private lemma divSum_mono (n : ℕ) {a b : ℕ} (h : a ≤ b) :
    divSum n a ≤ divSum n b := by
  unfold divSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_range] at hd ⊢
    exact ⟨lt_of_lt_of_le hd.1 h, hd.2⟩
  · intro _ _ _
    exact Nat.zero_le _

private lemma foldl_range_eq (n : ℕ) (hsum : divSum n n ≤ n) :
    ∀ k ≤ n, (List.range k).foldl (greedyStep n) n = n - divSum n k := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [divSum]
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ih (Nat.le_of_succ_le hk)]
    unfold greedyStep
    rw [divSum_succ]
    by_cases hd : k ∣ n
    · have hle : divSum n k + k ≤ n := by
        calc divSum n k + k = divSum n (k + 1) := by rw [divSum_succ, if_pos hd]
          _ ≤ divSum n n := divSum_mono n hk
          _ ≤ n := hsum
      rw [if_pos ⟨hd, by omega⟩, if_pos hd]
      omega
    · rw [if_neg (fun h => hd h.1), if_neg hd]
      omega

private lemma sum_divisors_eq_divSum_add (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ n.divisors, d = divSum n n + n := by
  have hset : n.divisors = (Finset.range (n + 1)).filter (· ∣ n) := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hd, hn0⟩
      exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) hd), hd⟩
    · rintro ⟨_, hd⟩
      exact ⟨hd, by omega⟩
  rw [hset]
  change divSum n (n + 1) = divSum n n + n
  rw [divSum_succ, if_pos dvd_rfl]

private lemma perfectDeficiency_of_sum_divisors_le (n : ℕ) (hn : 2 ≤ n)
    (hsum : ∑ d ∈ n.divisors, d ≤ 2 * n) :
    OeisA108864.perfectDeficiency n = 2 * n - ∑ d ∈ n.divisors, d := by
  have htot := sum_divisors_eq_divSum_add n (by omega)
  have hproper : divSum n n ≤ n := by omega
  change (List.range (n + 1)).foldl (greedyStep n) n = 2 * n - ∑ d ∈ n.divisors, d
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
    foldl_range_eq n hproper n le_rfl]
  have h1 : 1 ≤ divSum n n := by
    have hmem : 1 ∈ (Finset.range n).filter (· ∣ n) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, one_dvd n⟩
    exact Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _) hmem
  unfold greedyStep
  rw [if_neg (by omega), htot]
  omega

private lemma sum_divisors_prime {p : ℕ} (hp : p.Prime) :
    ∑ d ∈ p.divisors, d = p + 1 := by
  rw [hp.divisors, Finset.sum_pair hp.ne_one.symm, add_comm]

private lemma sum_two_pow_range (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), 2 ^ j = 2 ^ (k + 1) - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ]
    omega

private lemma sum_divisors_two_pow (k : ℕ) :
    ∑ d ∈ (2 ^ k).divisors, d = 2 ^ (k + 1) - 1 := by
  rw [← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two, sum_two_pow_range]

private lemma mem_A_two_pow (k : ℕ) : OeisA108864.A (2 ^ k) := by
  rcases k with _ | k
  · decide
  · refine ⟨Nat.pos_of_ne_zero (by positivity), ?_⟩
    have h2 : 2 ≤ 2 ^ (k + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hpow : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := pow_succ' 2 (k + 1)
    have hsig : ∑ d ∈ (2 ^ (k + 1)).divisors, d = 2 * 2 ^ (k + 1) - 1 := by
      rw [sum_divisors_two_pow (k + 1), hpow]
    have hle : ∑ d ∈ (2 ^ (k + 1)).divisors, d ≤ 2 * 2 ^ (k + 1) := by
      rw [hsig]
      omega
    rw [perfectDeficiency_of_sum_divisors_le _ h2 hle, hsig]
    omega

private lemma mem_A_two_pow_mul_prime {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime)
    (hp2 : p ≠ 2) (hlo : 2 ^ (k + 1) - 1 ≤ p) (hhi : p ≤ 2 ^ (k + 1) + 9) :
    OeisA108864.A (2 ^ k * p) := by
  have hcop : (2 ^ k).Coprime p :=
    ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm).pow_left k
  have hsig : ∑ d ∈ (2 ^ k * p).divisors, d = (2 ^ (k + 1) - 1) * (p + 1) := by
    rw [hcop.sum_divisors_mul, sum_divisors_two_pow, sum_divisors_prime hp]
  have hpow : 2 ≤ 2 ^ (k + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  have hp2gt : 2 ≤ p := hp.two_le
  have hge2 : 2 ≤ 2 ^ k * p := by nlinarith
  have hprod : (2 ^ (k + 1) - 1) * (p + 1) + (p + 1) = 2 ^ (k + 1) * p + 2 ^ (k + 1) := by
    have hsub : 2 ^ (k + 1) - 1 + 1 = 2 ^ (k + 1) := by omega
    calc (2 ^ (k + 1) - 1) * (p + 1) + (p + 1)
        = (2 ^ (k + 1) - 1 + 1) * (p + 1) := by ring
      _ = 2 ^ (k + 1) * (p + 1) := by rw [hsub]
      _ = 2 ^ (k + 1) * p + 2 ^ (k + 1) := by ring
  have h2mul : 2 * (2 ^ k * p) = 2 ^ (k + 1) * p := by
    rw [pow_succ']
    ring
  have hle : ∑ d ∈ (2 ^ k * p).divisors, d ≤ 2 * (2 ^ k * p) := by
    rw [hsig, h2mul]
    omega
  refine ⟨by omega, ?_⟩
  rw [perfectDeficiency_of_sum_divisors_le _ hge2 hle, hsig, h2mul]
  omega

private lemma witness_ok {k p N : ℕ} (hN : 2 ^ k * p < N) (hk : 1 ≤ k) (hp : p.Prime)
    (hp2 : p ≠ 2) (hlo : 2 ^ (k + 1) - 1 ≤ p) (hhi : p ≤ 2 ^ (k + 1) + 9) :
    2 ^ k * p < N ∧ OeisA108864.A (2 ^ k * p) ∧ ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ 2 ^ k * p :=
  ⟨hN, mem_A_two_pow_mul_prime hk hp hp2 hlo hhi, p, hp, hp2, dvd_mul_left p (2 ^ k)⟩

private def witnessPairs : List (ℕ × ℕ) :=
  [ (1, 3), (1, 5), (1, 7), (1, 11), (1, 13),
    (2, 7), (2, 11), (2, 13), (2, 17),
    (3, 17), (3, 19), (3, 23),
    (4, 31), (4, 37), (4, 41),
    (5, 67), (5, 71), (5, 73),
    (6, 127), (6, 131), (6, 137),
    (7, 257), (7, 263),
    (8, 521),
    (9, 1031), (9, 1033),
    (10, 2053),
    (11, 4099),
    (12, 8191) ]

theorem OMA.disproof : ¬ (type_of% @OeisA108864.conjecture) := by
  intro hconj
  set N : ℕ := 815634435 with hN_def
  have hN_fac : N = 3 * (5 * (7 * (11 * (547 * 1291)))) := by norm_num [hN_def]
  have hsigN : ∑ d ∈ N.divisors, d = 1631268864 := by
    rw [hN_fac,
      Nat.Coprime.sum_divisors_mul (by norm_num),
      Nat.Coprime.sum_divisors_mul (by norm_num),
      Nat.Coprime.sum_divisors_mul (by norm_num),
      Nat.Coprime.sum_divisors_mul (by norm_num),
      Nat.Coprime.sum_divisors_mul (by norm_num),
      sum_divisors_prime (by norm_num),
      sum_divisors_prime (by norm_num),
      sum_divisors_prime (by norm_num),
      sum_divisors_prime (by norm_num),
      sum_divisors_prime (by norm_num),
      sum_divisors_prime (by norm_num)]
  have hAN : OeisA108864.A N := by
    refine ⟨by omega, ?_⟩
    rw [perfectDeficiency_of_sum_divisors_le N (by omega) (by omega), hsigN]
    omega
  let S1 : Finset ℕ := (Finset.range 30).image (2 ^ ·)
  let S2 : Finset ℕ := (witnessPairs.map (fun kp => 2 ^ kp.1 * kp.2)).toFinset
  have hS1_card : S1.card = 30 := by
    rw [Finset.card_image_of_injective _ (Nat.pow_right_injective (by omega)), Finset.card_range]
  have hS2_nodup : (witnessPairs.map (fun kp => 2 ^ kp.1 * kp.2)).Nodup := by decide
  have hS2_card : S2.card = 29 := by
    rw [List.toFinset_card_of_nodup hS2_nodup]
    decide
  have hS2_mem_prop : ∀ x ∈ S2, x < N ∧ OeisA108864.A x ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ x := by
    intro x hx
    simp only [S2, witnessPairs, List.mem_toFinset, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with ⟨kp, hkp, rfl⟩
    rcases hkp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact witness_ok (by norm_num [hN_def]) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [S1, Finset.mem_image, Finset.mem_range] at hx1
    rcases hx1 with ⟨k, _, rfl⟩
    rcases (hS2_mem_prop (2 ^ k) hx2).2.2 with ⟨p, hp, hp2, hdvd⟩
    have hp_dvd2 : p ∣ 2 := hp.dvd_of_dvd_pow hdvd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp_dvd2
    exact hp2 this
  have hsub_mem : ∀ x ∈ S1 ∪ S2, x < N ∧ OeisA108864.A x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx1 | hx2
    · simp only [S1, Finset.mem_image, Finset.mem_range] at hx1
      rcases hx1 with ⟨k, hk, rfl⟩
      refine ⟨?_, mem_A_two_pow k⟩
      calc 2 ^ k ≤ 2 ^ 29 := Nat.pow_le_pow_right (by omega) (by omega)
        _ < N := by norm_num [hN_def]
    · exact ⟨(hS2_mem_prop x hx2).1, (hS2_mem_prop x hx2).2.1⟩
  have hcnt : 58 < Nat.count OeisA108864.A N := by
    rw [Nat.count_eq_card_filter_range]
    have hcard : (S1 ∪ S2).card = 59 := by
      rw [Finset.card_union_of_disjoint hdisj, hS1_card, hS2_card]
    calc 58 < (S1 ∪ S2).card := by omega
      _ ≤ {x ∈ Finset.range N | OeisA108864.A x}.card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter, Finset.mem_range]
        exact hsub_mem x hx
  have heven : Even (OeisA108864.a (Nat.count OeisA108864.A N)) :=
    hconj (Nat.count OeisA108864.A N) hcnt
  have ha_eq : OeisA108864.a (Nat.count OeisA108864.A N) = N :=
    Nat.nth_count hAN
  rw [ha_eq] at heven
  rcases heven with ⟨m, hm⟩
  omega
