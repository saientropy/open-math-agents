import FormalConjectures.OEIS.«108569»

/-!
Disproof of `OeisA108569.conjecture` via the odd counterexample $k = 5095354107$.
-/

private lemma prime_3 : Nat.Prime 3 := by norm_num
private lemma prime_5 : Nat.Prime 5 := by norm_num
private lemma prime_7 : Nat.Prime 7 := by norm_num
private lemma prime_13 : Nat.Prime 13 := by norm_num
private lemma prime_19 : Nat.Prime 19 := by norm_num
private lemma prime_1033 : Nat.Prime 1033 := by norm_num
private lemma prime_327317 : Nat.Prime 327317 := by norm_num
private lemma prime_1644193 : Nat.Prime 1644193 := by norm_num

private lemma totient_5095354107 : Nat.totient 5095354107 = 3393612288 := by
  have h1 : (5095354107 : ℕ) = 3 * (1033 * 1644193) := by norm_num
  rw [h1, Nat.totient_mul (by decide), Nat.totient_mul (by decide),
    Nat.totient_prime prime_3, Nat.totient_prime prime_1033, Nat.totient_prime prime_1644193]

private lemma totient_8488966395 : Nat.totient 8488966395 = 3393612288 := by
  have h1 : (8488966395 : ℕ) = 3 * (5 * (7 * (13 * (19 * 327317)))) := by norm_num
  rw [h1,
    Nat.totient_mul (by decide), Nat.totient_mul (by decide),
    Nat.totient_mul (by decide), Nat.totient_mul (by decide),
    Nat.totient_mul (by decide),
    Nat.totient_prime prime_3, Nat.totient_prime prime_5, Nat.totient_prime prime_7,
    Nat.totient_prime prime_13, Nat.totient_prime prime_19, Nat.totient_prime prime_327317]

theorem OMA.disproof : ¬ (type_of% @OeisA108569.conjecture) := by
  intro h
  have hk : OeisA108569.A 5095354107 := by
    refine ⟨by omega, ?_⟩
    rw [totient_5095354107]
    have hadd : (5095354107 : ℕ) + 3393612288 = 8488966395 := by norm_num
    rw [hadd, totient_8488966395]
  have hc2 : 1 ≤ Nat.count OeisA108569.A 2 := by decide
  have hpos : 0 < Nat.count OeisA108569.A 5095354107 :=
    lt_of_lt_of_le (by omega) (Nat.count_monotone OeisA108569.A (by omega : 2 ≤ 5095354107))
  have ha : OeisA108569.a (Nat.count OeisA108569.A 5095354107) = 5095354107 :=
    Nat.nth_count (p := OeisA108569.A) hk
  have heven := h (Nat.count OeisA108569.A 5095354107) hpos
  rw [ha] at heven
  rcases heven with ⟨m, hm⟩
  omega
