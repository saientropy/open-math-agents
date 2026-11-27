import FormalConjectures.OEIS.«114137»

/-!
Disproof of `OeisA114137.conjecture2`:
Using a period-360 double covering system built from 20 odd primes dividing `2^360 - 1`
(together with `3^2` of order 6 and `5^2` of order 20), the 41-digit odd integer
`K = 31578183342437226018483364220022071159573` has the property that for every `n : ℕ`,
there exist primes `p, q <= 61681` with `p * q ∣ 2^n + K` and `p * q < 2^n + K`.
Hence `Omega(2^n + K) >= 3`, so `2^n + K` is never a semiprime, and `a n != K` for all `n`.
-/

private def K : ℕ := 31578183342437226018483364220022071159573

private def primeRules : List (ℕ × ℕ × ℕ) :=
  [ (3, 2, 0), (7, 3, 1), (5, 4, 1), (31, 5, 0), (17, 8, 3),
    (73, 9, 2), (11, 10, 3), (13, 12, 3), (151, 15, 2), (19, 18, 8),
    (41, 20, 11), (241, 24, 23), (331, 30, 9), (37, 36, 14), (109, 36, 32),
    (61681, 40, 7), (631, 45, 14), (23311, 45, 44), (61, 60, 57), (1321, 60, 19) ]

private def isCovered (x : ℕ) : Bool :=
  x % 6 == 0 || x % 20 == 1 ||
    2 ≤ (primeRules.filter (fun t => x % t.2.1 == t.2.2)).length

private def checkRange (start : ℕ) : ℕ → Bool
  | 0 => true
  | len + 1 => isCovered start && checkRange (start + 1) len

private def checkBlocks : ℕ → Bool
  | 0 => true
  | b + 1 => checkRange (40 * b) 40 && checkBlocks b

private lemma checkRange_spec (start len : ℕ) (h : checkRange start len = true) :
    ∀ x, start ≤ x → x < start + len → isCovered x = true := by
  induction len generalizing start with
  | zero => intro x h1 h2; omega
  | succ len ih =>
    intro x h1 h2
    simp only [checkRange, Bool.and_eq_true] at h
    rcases eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · exact ih (start + 1) h.2 x (by omega) (by omega)

private lemma checkBlocks_spec (b : ℕ) (h : checkBlocks b = true) :
    ∀ x < 40 * b, isCovered x = true := by
  induction b with
  | zero => intro x hx; omega
  | succ b ih =>
    intro x hx
    simp only [checkBlocks, Bool.and_eq_true] at h
    by_cases hlt : x < 40 * b
    · exact ih h.2 x hlt
    · exact checkRange_spec (40 * b) 40 h.1 x (by omega) (by omega)

private lemma cover_360 (x : ℕ) (hx : x < 360) : isCovered x = true :=
  checkBlocks_spec 9 (by decide +kernel) x hx

private lemma primeRules_nodup_fst : (primeRules.map Prod.fst).Nodup := by
  decide

private lemma primeRules_valid :
    ∀ t ∈ primeRules,
      t.1.Prime ∧ t.1 ≤ 61681 ∧ t.2.1 ∣ 360 ∧ 2 ^ t.2.1 % t.1 = 1 ∧
        (2 ^ t.2.2 + K) % t.1 = 0 := by
  intro t ht
  simp only [primeRules, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num [K]⟩

private lemma dvd_pow_add_K_of_mod {d m r n : ℕ} (hd : 1 < d)
    (hord : 2 ^ m % d = 1) (hres : (2 ^ r + K) % d = 0) (hn : n % m = r) :
    d ∣ 2 ^ n + K := by
  have h2m : 2 ^ m ≡ 1 [MOD d] := by
    rw [Nat.ModEq, hord, Nat.mod_eq_of_lt hd]
  have hpow : 2 ^ n ≡ 2 ^ r [MOD d] := by
    have hdiv : m * (n / m) + r = n := by
      rw [← hn]
      exact Nat.div_add_mod n m
    calc 2 ^ n = 2 ^ (m * (n / m) + r) := by rw [hdiv]
      _ = (2 ^ m) ^ (n / m) * 2 ^ r := by rw [pow_add, pow_mul]
      _ ≡ 1 ^ (n / m) * 2 ^ r [MOD d] := (h2m.pow (n / m)).mul_right _
      _ = 2 ^ r := by simp
  have hsum : 2 ^ n + K ≡ 0 [MOD d] := by
    have h0 : 2 ^ r + K ≡ 0 [MOD d] := by
      rw [Nat.ModEq, hres, Nat.zero_mod]
    exact (hpow.add_right K).trans h0
  exact Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using hsum)

private lemma not_isSemiprime_of_mul_dvd {p q M : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hdvd : p * q ∣ M) (hlt : p * q < M) : ¬ M.IsSemiprime := by
  intro hsp
  rcases hdvd with ⟨t, rfl⟩
  have h1t : 1 < t := by
    by_contra h
    have ht : t ≤ 1 := Nat.le_of_not_lt h
    interval_cases t <;> simp at hlt
  have hcard : ArithmeticFunction.cardFactors (p * q * t) = 2 := hsp.2
  rw [ArithmeticFunction.cardFactors_mul (mul_ne_zero hp.ne_zero hq.ne_zero) (by omega),
    ArithmeticFunction.cardFactors_mul hp.ne_zero hq.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime hp,
    ArithmeticFunction.cardFactors_apply_prime hq] at hcard
  have htz : ArithmeticFunction.cardFactors t = 0 := by omega
  rcases ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one.mp htz with rfl | rfl <;> omega

private lemma not_isSemiprime_two_pow_add_K (n : ℕ) : ¬ (2 ^ n + K).IsSemiprime := by
  have hcov := cover_360 (n % 360) (Nat.mod_lt n (by omega))
  simp only [isCovered, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hcov
  rcases hcov with (h6 | h20) | hlen
  · have hn6 : n % 6 = 0 := by
      rw [← Nat.mod_mod_of_dvd n (by decide : 6 ∣ 360), h6]
    have hdvd : 3 * 3 ∣ 2 ^ n + K :=
      dvd_pow_add_K_of_mod (d := 9) (m := 6) (r := 0) (by omega) (by norm_num)
        (by norm_num [K]) hn6
    have hlt : 3 * 3 < 2 ^ n + K :=
      lt_of_lt_of_le (by norm_num [K] : 3 * 3 < K) (Nat.le_add_left K (2 ^ n))
    exact not_isSemiprime_of_mul_dvd (by norm_num) (by norm_num) hdvd hlt
  · have hn20 : n % 20 = 1 := by
      rw [← Nat.mod_mod_of_dvd n (by decide : 20 ∣ 360), h20]
    have hdvd : 5 * 5 ∣ 2 ^ n + K :=
      dvd_pow_add_K_of_mod (d := 25) (m := 20) (r := 1) (by omega) (by norm_num)
        (by norm_num [K]) hn20
    have hlt : 5 * 5 < 2 ^ n + K :=
      lt_of_lt_of_le (by norm_num [K] : 5 * 5 < K) (Nat.le_add_left K (2 ^ n))
    exact not_isSemiprime_of_mul_dvd (by norm_num) (by norm_num) hdvd hlt
  · have hL_nodup : ((primeRules.filter (fun t => (n % 360) % t.2.1 == t.2.2)).map Prod.fst).Nodup :=
      primeRules_nodup_fst.sublist ((List.filter_sublist).map Prod.fst)
    generalize hL : primeRules.filter (fun t => (n % 360) % t.2.1 == t.2.2) = L at hlen hL_nodup
    rcases L with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at hlen
    · simp at hlen
    · have ha_mem : a ∈ primeRules.filter (fun t => (n % 360) % t.2.1 == t.2.2) := by
        rw [hL]; simp
      have hb_mem : b ∈ primeRules.filter (fun t => (n % 360) % t.2.1 == t.2.2) := by
        rw [hL]; simp
      rw [List.mem_filter] at ha_mem hb_mem
      have ha_val := primeRules_valid a ha_mem.1
      have hb_val := primeRules_valid b hb_mem.1
      rw [List.map_cons, List.map_cons, List.nodup_cons] at hL_nodup
      have hne : a.1 ≠ b.1 := fun heq => hL_nodup.1 (by simp [heq])
      have hna : n % a.2.1 = a.2.2 := by
        have hmod := beq_iff_eq.mp ha_mem.2
        rwa [Nat.mod_mod_of_dvd n ha_val.2.2.1] at hmod
      have hnb : n % b.2.1 = b.2.2 := by
        have hmod := beq_iff_eq.mp hb_mem.2
        rwa [Nat.mod_mod_of_dvd n hb_val.2.2.1] at hmod
      have hda : a.1 ∣ 2 ^ n + K :=
        dvd_pow_add_K_of_mod ha_val.1.one_lt ha_val.2.2.2.1 ha_val.2.2.2.2 hna
      have hdb : b.1 ∣ 2 ^ n + K :=
        dvd_pow_add_K_of_mod hb_val.1.one_lt hb_val.2.2.2.1 hb_val.2.2.2.2 hnb
      have hcop : a.1.Coprime b.1 := (Nat.coprime_primes ha_val.1 hb_val.1).mpr hne
      have hdvd : a.1 * b.1 ∣ 2 ^ n + K := hcop.mul_dvd_of_dvd_of_dvd hda hdb
      have hlt : a.1 * b.1 < 2 ^ n + K :=
        lt_of_le_of_lt (Nat.mul_le_mul ha_val.2.1 hb_val.2.1)
          (lt_of_lt_of_le (by norm_num [K] : 61681 * 61681 < K) (Nat.le_add_left K (2 ^ n)))
      exact not_isSemiprime_of_mul_dvd ha_val.1 hb_val.1 hdvd hlt

theorem OMA.disproof : ¬ (type_of% @OeisA114137.conjecture2) := by
  intro hconj
  have hKodd : Odd K := ⟨15789091671218613009241682110011035579786, by norm_num [K]⟩
  rcases hconj K hKodd with ⟨n, hn⟩
  set S : Set ℕ := { s | s > 2 ^ n ∧ s.IsSemiprime ∧ Odd s } with hS_def
  have hS_ne : S.Nonempty := by
    rcases Nat.exists_infinite_primes (2 ^ n + 3) with ⟨q, hq_ge, hq_prime⟩
    have h2pos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hq_odd : Odd q := hq_prime.odd_of_ne_two (by omega)
    refine ⟨3 * q, ?_, Nat.Prime.mul_isAlmostPrime_two (by norm_num) hq_prime,
      (by decide : Odd 3).mul hq_odd⟩
    omega
  have hmem : sInf S ∈ S := Nat.sInf_mem hS_ne
  have hsub : sInf S - 2 ^ n = K := hn
  have hgt : 2 ^ n < sInf S := hmem.1
  have heq : sInf S = 2 ^ n + K := by omega
  have hsp : (2 ^ n + K).IsSemiprime := by
    rw [← heq]
    exact hmem.2.1
  exact not_isSemiprime_two_pow_add_K n hsp
