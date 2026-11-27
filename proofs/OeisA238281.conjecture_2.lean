import FormalConjectures.OEIS.«238281»

/-!
Disproof of `OeisA238281.conjecture_2` using the counterexample `n = 14`.
-/

private def isSmallPrime (n : ℕ) : Bool :=
  n == 2 || n == 3 || n == 5 || n == 7 || n == 11 || n == 13 ||
    (2 ≤ n && n % 2 != 0 && n % 3 != 0 && n % 5 != 0 && n % 7 != 0 && n % 11 != 0 && n % 13 != 0)

private lemma prime_iff_isSmallPrime {n : ℕ} (hn : n < 169) :
    n.Prime ↔ isSmallPrime n = true := by
  constructor
  · intro hp
    unfold isSmallPrime
    by_cases h2 : n = 2; · simp [h2]
    by_cases h3 : n = 3; · simp [h3]
    by_cases h5 : n = 5; · simp [h5]
    by_cases h7 : n = 7; · simp [h7]
    by_cases h11 : n = 11; · simp [h11]
    by_cases h13 : n = 13; · simp [h13]
    have hd : ∀ q : ℕ, q.Prime → n ≠ q → n % q ≠ 0 := by
      intro q hq hne hdvd
      have := (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hdvd)
      rcases this with h1 | rfl
      · exact hq.ne_one h1
      · exact hne rfl
    have hge2 : 2 ≤ n := hp.two_le
    have m2 : n % 2 ≠ 0 := hd 2 (by norm_num) h2
    have m3 : n % 3 ≠ 0 := hd 3 (by norm_num) h3
    have m5 : n % 5 ≠ 0 := hd 5 (by norm_num) h5
    have m7 : n % 7 ≠ 0 := hd 7 (by norm_num) h7
    have m11 : n % 11 ≠ 0 := hd 11 (by norm_num) h11
    have m13 : n % 13 ≠ 0 := hd 13 (by norm_num) h13
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
    right
    refine ⟨⟨⟨⟨⟨⟨hge2, m2⟩, m3⟩, m5⟩, m7⟩, m11⟩, m13⟩
  · intro h
    unfold isSmallPrime at h
    by_cases h2 : n = 2; · subst h2; norm_num
    by_cases h3 : n = 3; · subst h3; norm_num
    by_cases h5 : n = 5; · subst h5; norm_num
    by_cases h7 : n = 7; · subst h7; norm_num
    by_cases h11 : n = 11; · subst h11; norm_num
    by_cases h13 : n = 13; · subst h13; norm_num
    simp only [h2, h3, h5, h7, h11, h13, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq, bne_iff_ne, false_or] at h
    obtain ⟨⟨⟨⟨⟨⟨hge2, m2⟩, m3⟩, m5⟩, m7⟩, m11⟩, m13⟩ := h
    by_contra hnp
    have hq_prime : n.minFac.Prime := Nat.minFac_prime (by omega)
    have hq_sq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
    have hq_lt : n.minFac < 13 := by nlinarith
    have hq_dvd : n.minFac ∣ n := Nat.minFac_dvd n
    have hq_mod : n % n.minFac = 0 := Nat.mod_eq_zero_of_dvd hq_dvd
    have hq_ge : 2 ≤ n.minFac := hq_prime.two_le
    interval_cases q : n.minFac
    all_goals first | exact m2 hq_mod | exact m3 hq_mod | exact m5 hq_mod |
      exact m7 hq_mod | exact m11 hq_mod | (norm_num at hq_prime)

private def fastPi (m : ℕ) : ℕ :=
  Nat.count (fun n => isSmallPrime n = true) (m + 1)

private lemma primeCounting_eq_fastPi {m : ℕ} (hm : m ≤ 168) :
    Nat.primeCounting m = fastPi m := by
  rw [Nat.primeCounting, Nat.primeCounting', fastPi, Nat.count_eq_card_filter_range,
    Nat.count_eq_card_filter_range]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hlt, hp⟩
    exact ⟨hlt, (prime_iff_isSmallPrime (by omega)).mp hp⟩
  · rintro ⟨hlt, hp⟩
    exact ⟨hlt, (prime_iff_isSmallPrime (by omega)).mpr hp⟩

private lemma fastPi_check :
    ∀ k ∈ Finset.Ioo 0 14, isSmallPrime (2 * k + 1) = true →
      fastPi (k * 14) - fastPi ((k - 1) * 14) ≠
      fastPi ((k + 1) * 14) - fastPi (k * 14) := by
  decide

theorem OMA.disproof : ¬ (type_of% @OeisA238281.conjecture_2) := by
  intro h
  obtain ⟨k, hk0, hk14, hprime, heq⟩ := h 14 (by omega) (by omega)
  have hsp : isSmallPrime (2 * k + 1) = true :=
    (prime_iff_isSmallPrime (by omega)).mp hprime
  have hk11 : k ≤ 11 := by
    by_contra hgt
    have : k = 12 ∨ k = 13 := by omega
    rcases this with rfl | rfl <;> norm_num at hprime
  have h1 : Nat.primeCounting (k * 14) = fastPi (k * 14) :=
    primeCounting_eq_fastPi (by omega)
  have h2 : Nat.primeCounting ((k - 1) * 14) = fastPi ((k - 1) * 14) :=
    primeCounting_eq_fastPi (by omega)
  have h3 : Nat.primeCounting ((k + 1) * 14) = fastPi ((k + 1) * 14) :=
    primeCounting_eq_fastPi (by omega)
  rw [h1, h2, h3] at heq
  exact fastPi_check k (Finset.mem_Ioo.mpr ⟨hk0, hk14⟩) hsp heq
