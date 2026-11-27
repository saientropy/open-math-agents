import FormalConjectures.OEIS.«234360»

/-!
Disproof of `OeisA234360.conjecture_4`:
Counterexample at `n = 3998`. For every `0 < k < 3998`:
- For `k = 3996, 3997`, `totient (3998 - k) = 1` and `k + 1 ∈ {3997, 3998}` is not a perfect square.
- For `1 ≤ k ≤ 3995`, `totient (3998 - k) = 2 * he` is even, so `(p + 1)^2 = k^2 * (k + 1)^(2 * he)`
  forces `p = k * (k + 1)^he - 1`. We certify that every such number is composite using:
  (a) a certified fast totient computation via the 23 primes `< 89`,
  (b) algebraic difference-of-squares factorization when `k` is a square and `he` is even,
  (c) small prime divisors `< 10^7` verified by modular exponentiation, and
  (d) base-2 Fermat compositeness (`2^(m - 1) % m ≠ 1`) via tree-split modular exponentiation
      load-balanced across 20 parallel kernel-checked chunks.
-/

private def smallPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83]

private def stripPrime (p : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, m, mult => (m, mult)
  | fuel + 1, m, mult =>
    if m % p == 0 then stripPrime p fuel (m / p) (mult * p)
    else (m, mult)

private def fastTotientLoop : List ℕ → ℕ → ℕ → ℕ
  | [], m, acc => if 1 < m then acc * (m - 1) else acc
  | p :: ps, m, acc =>
    if m % p == 0 then
      let r := stripPrime p 14 (m / p) (p - 1)
      fastTotientLoop ps r.1 (acc * r.2)
    else
      fastTotientLoop ps m acc

private def fastTotient (m : ℕ) : ℕ :=
  fastTotientLoop smallPrimes m 1

private lemma smallPrimes_prime : ∀ p ∈ smallPrimes, p.Prime := by
  decide

private lemma prime_lt_89_mem : ∀ q : Fin 89, q.val.Prime → q.val ∈ smallPrimes := by
  decide

private lemma stripPrime_spec {p : ℕ} (hp : p.Prime) :
    ∀ (fuel m mult : ℕ), 0 < m → m < 2 ^ fuel →
      let r := stripPrime p fuel m mult
      0 < r.1 ∧ r.1 ≤ m ∧ ¬ p ∣ r.1 ∧ (∀ q, q ∣ r.1 → q ∣ m) ∧
        ∃ t : ℕ, m = p ^ t * r.1 ∧ r.2 = mult * p ^ t := by
  intro fuel
  induction fuel with
  | zero =>
    intro m mult hm hlt
    omega
  | succ fuel ih =>
    intro m mult hm hlt
    dsimp only [stripPrime]
    by_cases hmod : m % p == 0
    · rw [if_pos hmod]
      have hdvd : p ∣ m := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp hmod)
      have hp2 : 2 ≤ p := hp.two_le
      have hdiv_pos : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm hdvd) (by omega)
      have hdiv_lt : m / p < 2 ^ fuel := by
        have hmul : 2 * (m / p) ≤ m := by
          calc 2 * (m / p) ≤ p * (m / p) := Nat.mul_le_mul_right _ hp2
            _ = m := Nat.mul_div_cancel' hdvd
        rw [pow_succ'] at hlt
        omega
      rcases ih (m / p) (mult * p) hdiv_pos hdiv_lt with
        ⟨hpos', hle', hnd', hdiv', t, hm_eq, hmult_eq⟩
      refine ⟨hpos', le_trans hle' (Nat.div_le_self m p), hnd', ?_, t + 1, ?_, ?_⟩
      · intro q hq
        exact dvd_trans (hdiv' q hq) (Nat.div_dvd_of_dvd hdvd)
      · calc m = p * (m / p) := (Nat.mul_div_cancel' hdvd).symm
          _ = p * (p ^ t * (stripPrime p fuel (m / p) (mult * p)).1) := congr_arg (p * ·) hm_eq
          _ = p ^ (t + 1) * (stripPrime p fuel (m / p) (mult * p)).1 := by rw [pow_succ']; ring
      · rw [hmult_eq, pow_succ']
        ring
    · rw [if_neg hmod]
      have hnd : ¬ p ∣ m := fun hd => hmod (beq_iff_eq.mpr (Nat.mod_eq_zero_of_dvd hd))
      exact ⟨hm, le_rfl, hnd, fun _ hq => hq, 0, by simp, by simp⟩

private lemma fastTotientLoop_spec :
    ∀ (ps : List ℕ), (∀ p ∈ ps, p.Prime) →
      ∀ (m acc : ℕ), 0 < m → m < 7921 →
        (∀ q, q.Prime → q < 89 → q ∣ m → q ∈ ps) →
        fastTotientLoop ps m acc = acc * m.totient := by
  intro ps
  induction ps with
  | nil =>
    intro _ m acc hm hlt hno
    dsimp only [fastTotientLoop]
    by_cases h1 : 1 < m
    · rw [if_pos h1]
      have hprime : m.Prime := by
        by_contra hnp
        have hmf_p : m.minFac.Prime := Nat.minFac_prime (by omega)
        have hmf_d : m.minFac ∣ m := Nat.minFac_dvd m
        have hmf_sq : m.minFac * m.minFac ≤ m := by
          simpa [sq] using Nat.minFac_sq_le_self hm hnp
        have hmf_lt : m.minFac < 89 := by nlinarith
        exact List.not_mem_nil (hno m.minFac hmf_p hmf_lt hmf_d)
      rw [Nat.totient_prime hprime]
    · rw [if_neg h1]
      have hm1 : m = 1 := by omega
      simp [hm1]
  | cons p ps ih =>
    intro hps m acc hm hlt hcov
    have hp : p.Prime := hps p (by simp)
    have hps' : ∀ q ∈ ps, q.Prime := fun q hq => hps q (by simp [hq])
    dsimp only [fastTotientLoop]
    by_cases hmod : m % p == 0
    · rw [if_pos hmod]
      have hdvd : p ∣ m := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp hmod)
      have hdiv_pos : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm hdvd) hp.pos
      have hdiv_lt : m / p < 2 ^ 14 := by
        have := Nat.div_le_self m p
        omega
      rcases stripPrime_spec hp 14 (m / p) (p - 1) hdiv_pos hdiv_lt with
        ⟨hpos', hle', hnd', hdiv', t, hm_eq, hmult_eq⟩
      set r := stripPrime p 14 (m / p) (p - 1)
      have hm_full : m = p ^ (t + 1) * r.1 := by
        calc m = p * (m / p) := (Nat.mul_div_cancel' hdvd).symm
          _ = p * (p ^ t * r.1) := by rw [hm_eq]
          _ = p ^ (t + 1) * r.1 := by rw [pow_succ']; ring
      have hcop : (p ^ (t + 1)).Coprime r.1 :=
        (hp.coprime_iff_not_dvd.mpr hnd').pow_left (t + 1)
      have htot_eq : m.totient = r.2 * r.1.totient := by
        rw [hm_full, Nat.totient_mul hcop, Nat.totient_prime_pow hp (by omega), hmult_eq]
        have : t + 1 - 1 = t := by omega
        rw [this]
        ring
      have hr1_lt : r.1 < 7921 := by
        have := Nat.div_le_self m p
        omega
      have hcov' : ∀ q, q.Prime → q < 89 → q ∣ r.1 → q ∈ ps := by
        intro q hqp hq89 hqd
        have hqm : q ∣ m := dvd_trans (hdiv' q hqd) (Nat.div_dvd_of_dvd hdvd)
        rcases List.mem_cons.mp (hcov q hqp hq89 hqm) with rfl | hmem
        · exact False.elim (hnd' hqd)
        · exact hmem
      rw [ih hps' r.1 (acc * r.2) hpos' hr1_lt hcov', htot_eq, mul_assoc]
    · rw [if_neg hmod]
      have hnd : ¬ p ∣ m := fun hd => hmod (beq_iff_eq.mpr (Nat.mod_eq_zero_of_dvd hd))
      have hcov' : ∀ q, q.Prime → q < 89 → q ∣ m → q ∈ ps := by
        intro q hqp hq89 hqm
        rcases List.mem_cons.mp (hcov q hqp hq89 hqm) with rfl | hmem
        · exact False.elim (hnd hqm)
        · exact hmem
      exact ih hps' m acc hm hlt hcov'

private lemma fastTotient_eq (m : ℕ) (hm : 0 < m) (hlt : m < 7921) :
    fastTotient m = m.totient := by
  have h := fastTotientLoop_spec smallPrimes smallPrimes_prime m 1 hm hlt
    (fun q hqp hq89 _ => prime_lt_89_mem ⟨q, hq89⟩ hqp)
  simpa [fastTotient] using h

private def powBinAux (b : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | fuel + 1, e, acc =>
    if e == 0 then acc
    else
      let acc' := if e % 2 == 1 then acc * b else acc
      powBinAux (b * b) fuel (e / 2) acc'

private lemma powBinAux_spec :
    ∀ (fuel b e acc : ℕ), e < 2 ^ fuel → powBinAux b fuel e acc = acc * b ^ e := by
  intro fuel
  induction fuel with
  | zero =>
    intro b e acc he
    have : e = 0 := by omega
    subst this
    simp [powBinAux]
  | succ fuel ih =>
    intro b e acc he
    dsimp only [powBinAux]
    by_cases he0 : e == 0
    · rw [if_pos he0]
      have : e = 0 := beq_iff_eq.mp he0
      subst this
      simp
    · rw [if_neg he0]
      have hdiv : e / 2 < 2 ^ fuel := by
        rw [pow_succ'] at he
        omega
      rw [ih (b * b) (e / 2) _ hdiv]
      by_cases hodd : e % 2 == 1
      · rw [if_pos hodd]
        have heq : e = 2 * (e / 2) + 1 := by
          have := beq_iff_eq.mp hodd
          omega
        conv_rhs => rw [heq, pow_add, pow_one, pow_mul]
        have : b * b = b ^ 2 := by ring
        rw [this]
        ring
      · rw [if_neg hodd]
        have heq : e = 2 * (e / 2) := by
          have : e % 2 ≠ 1 := fun h => hodd (beq_iff_eq.mpr h)
          omega
        conv_rhs => rw [heq, pow_mul]
        have : b * b = b ^ 2 := by ring
        rw [this]

private def powModSmallAux (m : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | fuel + 1, b, e, acc =>
    if e == 0 then acc
    else
      let acc' := if e % 2 == 1 then (acc * b) % m else acc
      powModSmallAux m fuel ((b * b) % m) (e / 2) acc'

private lemma powModSmallAux_spec (m : ℕ) :
    ∀ (fuel b e acc : ℕ), e < 2 ^ fuel →
      powModSmallAux m fuel b e acc % m = (acc * b ^ e) % m := by
  intro fuel
  induction fuel with
  | zero =>
    intro b e acc he
    have : e = 0 := by omega
    subst this
    simp [powModSmallAux]
  | succ fuel ih =>
    intro b e acc he
    dsimp only [powModSmallAux]
    by_cases he0 : e == 0
    · rw [if_pos he0]
      have : e = 0 := beq_iff_eq.mp he0
      subst this
      simp
    · rw [if_neg he0]
      have hdiv : e / 2 < 2 ^ fuel := by
        rw [pow_succ'] at he
        omega
      rw [ih ((b * b) % m) (e / 2) _ hdiv]
      have hsq : ((b * b) % m) ^ (e / 2) % m = (b ^ 2) ^ (e / 2) % m := by
        have h1 : (b * b) % m ≡ b ^ 2 [MOD m] := by
          rw [Nat.ModEq, Nat.mod_mod, sq]
        exact h1.pow (e / 2)
      by_cases hodd : e % 2 == 1
      · rw [if_pos hodd]
        have heq : e = 2 * (e / 2) + 1 := by
          have := beq_iff_eq.mp hodd
          omega
        have hm1 : (acc * b) % m * ((b * b) % m) ^ (e / 2) ≡ (acc * b) * (b ^ 2) ^ (e / 2) [MOD m] :=
          Nat.ModEq.mul (by rw [Nat.ModEq, Nat.mod_mod]) hsq
        rw [hm1]
        congr 1
        conv_rhs => rw [heq, pow_add, pow_one, pow_mul]
        ring
      · rw [if_neg hodd]
        have heq : e = 2 * (e / 2) := by
          have : e % 2 ≠ 1 := fun h => hodd (beq_iff_eq.mpr h)
          omega
        have hm1 : acc * ((b * b) % m) ^ (e / 2) ≡ acc * (b ^ 2) ^ (e / 2) [MOD m] :=
          Nat.ModEq.mul_left acc hsq
        rw [hm1]
        congr 1
        conv_rhs => rw [heq, pow_mul]

private def stepBits (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | k + 1, c, x =>
    let x1 := stepBits m k (c / 2) x
    let sq := (x1 * x1) % m
    if c % 2 == 1 then
      let sq2 := sq + sq
      if m ≤ sq2 then sq2 - m else sq2
    else sq

private lemma stepBits_spec (m : ℕ) (hm : 1 < m) :
    ∀ (k c x : ℕ), x < m →
      stepBits m k c x < m ∧ stepBits m k c x = (x ^ (2 ^ k) * 2 ^ (c % 2 ^ k)) % m := by
  intro k
  induction k with
  | zero =>
    intro c x hx
    simp only [stepBits, pow_zero, pow_one, Nat.mod_one, mul_one, Nat.mod_eq_of_lt hx, hx, and_self]
  | succ k ih =>
    intro c x hx
    dsimp only [stepBits]
    rcases ih (c / 2) x hx with ⟨hx1_lt, hx1_eq⟩
    set x1 := stepBits m k (c / 2) x
    set sq := (x1 * x1) % m
    have hsq_lt : sq < m := Nat.mod_lt _ (by omega)
    have hsq_eq : sq = (x ^ (2 ^ (k + 1)) * 2 ^ (2 * ((c / 2) % 2 ^ k))) % m := by
      have h1 : x1 ≡ x ^ (2 ^ k) * 2 ^ ((c / 2) % 2 ^ k) [MOD m] := by
        rw [Nat.ModEq, hx1_eq, Nat.mod_mod]
      have h2 := h1.mul h1
      have h3 : (x1 * x1) % m = ((x ^ (2 ^ k) * 2 ^ ((c / 2) % 2 ^ k)) *
          (x ^ (2 ^ k) * 2 ^ ((c / 2) % 2 ^ k))) % m := h2
      dsimp only [sq]
      rw [h3]
      congr 1
      rw [pow_succ, pow_mul, mul_comm 2 ((c / 2) % 2 ^ k), pow_mul]
      ring
    have hmod_div : c % 2 ^ (k + 1) = 2 * ((c / 2) % 2 ^ k) + c % 2 := by
      have h1 := Nat.div_add_mod c 2
      have h2 : c / 2 = 2 ^ k * (c / 2 / 2 ^ k) + (c / 2) % 2 ^ k := (Nat.div_add_mod (c / 2) (2 ^ k)).symm
      have h3 : c = 2 ^ (k + 1) * (c / 2 / 2 ^ k) + (2 * ((c / 2) % 2 ^ k) + c % 2) := by
        rw [pow_succ']; linarith
      have hlt : 2 * ((c / 2) % 2 ^ k) + c % 2 < 2 ^ (k + 1) := by
        have hlt1 : (c / 2) % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
        have hlt2 : c % 2 < 2 := Nat.mod_lt _ (by omega)
        rw [pow_succ']
        omega
      conv_lhs => rw [h3]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    by_cases hodd : c % 2 == 1
    · rw [if_pos hodd]
      have hc1 : c % 2 = 1 := beq_iff_eq.mp hodd
      have hsq2_eq : (if m ≤ sq + sq then sq + sq - m else sq + sq) < m ∧
          (if m ≤ sq + sq then sq + sq - m else sq + sq) = (sq * 2) % m := by
        by_cases hge : m ≤ sq + sq
        · rw [if_pos hge]
          refine ⟨by omega, ?_⟩
          have hsub : sq * 2 = m + (sq + sq - m) := by omega
          rw [hsub, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        · rw [if_neg hge]
          refine ⟨by omega, ?_⟩
          have hsub : sq * 2 = sq + sq := by omega
          rw [hsub, Nat.mod_eq_of_lt (by omega)]
      refine ⟨hsq2_eq.1, ?_⟩
      rw [hsq2_eq.2]
      have h4 : sq * 2 ≡ (x ^ (2 ^ (k + 1)) * 2 ^ (2 * ((c / 2) % 2 ^ k))) * 2 [MOD m] :=
        Nat.ModEq.mul_right 2 (by rw [Nat.ModEq, hsq_eq, Nat.mod_mod])
      rw [h4]
      congr 1
      rw [hmod_div, hc1, pow_succ]
      ring
    · rw [if_neg hodd]
      have hc0 : c % 2 = 0 := by
        have : c % 2 ≠ 1 := fun h => hodd (beq_iff_eq.mpr h)
        omega
      refine ⟨hsq_lt, ?_⟩
      rw [hsq_eq, hmod_div, hc0, add_zero]

private def pow2ModFull (m : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], e, x => stepBits m 16 e x
  | B :: Bs, e, x =>
    let x1 := pow2ModFull m Bs (e / B) x
    if x1 == 0 then 0 else pow2ModFull m Bs (e % B) x1

private def pow2ModStart (m : ℕ) : List ℕ → ℕ → ℕ
  | [], e => stepBits m 16 e 1
  | B :: Bs, e =>
    let hi := e / B
    if hi == 0 then pow2ModStart m Bs e
    else
      let x1 := pow2ModStart m Bs hi
      if x1 == 0 then 0 else pow2ModFull m Bs (e % B) x1

private inductive ValidSplits : List ℕ → ℕ → Prop
  | nil : ValidSplits [] 16
  | cons {Bs w} : ValidSplits Bs w → ValidSplits (2 ^ w :: Bs) (2 * w)

private lemma pow2ModFull_spec (m : ℕ) (hm : 1 < m) :
    ∀ {Bs w}, ValidSplits Bs w → ∀ (e x : ℕ), x < m →
      pow2ModFull m Bs e x < m ∧ pow2ModFull m Bs e x = (x ^ (2 ^ w) * 2 ^ (e % 2 ^ w)) % m := by
  intro Bs w hvs
  induction hvs with
  | nil =>
    intro e x hx
    exact stepBits_spec m hm 16 e x hx
  | @cons Bs w hvs ih =>
    intro e x hx
    dsimp only [pow2ModFull]
    set B := 2 ^ w
    rcases ih (e / B) x hx with ⟨hx1_lt, hx1_eq⟩
    set x1 := pow2ModFull m Bs (e / B) x
    have hmod_split : e % (2 ^ (2 * w)) = B * ((e / B) % B) + e % B := by
      have hB2 : 2 ^ (2 * w) = B * B := by rw [two_mul, pow_add]
      have h1 : e / B = B * (e / B / B) + (e / B) % B := (Nat.div_add_mod (e / B) B).symm
      have h2 : e = B * (e / B) + e % B := (Nat.div_add_mod e B).symm
      have h3 : e = (B * B) * (e / B / B) + (B * ((e / B) % B) + e % B) := by
        calc e = B * (B * (e / B / B) + (e / B) % B) + e % B := by rw [← h1, ← h2]
          _ = (B * B) * (e / B / B) + (B * ((e / B) % B) + e % B) := by ring
      have hB_pos : 0 < B := by positivity
      have hlt : B * ((e / B) % B) + e % B < B * B := by
        have hlt1 : (e / B) % B < B := Nat.mod_lt _ hB_pos
        have hlt2 : e % B < B := Nat.mod_lt _ hB_pos
        nlinarith
      rw [hB2]
      conv_lhs => rw [h3]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    have hpow_comb : (x ^ B * 2 ^ ((e / B) % B)) ^ B * 2 ^ (e % B) =
        x ^ (2 ^ (2 * w)) * 2 ^ (e % (2 ^ (2 * w))) := by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add, hmod_split]
      rw [← two_mul w, ← pow_add, mul_comm ((e / B) % B) B]
    by_cases hx1z : x1 == 0
    · rw [if_pos hx1z]
      refine ⟨by omega, ?_⟩
      have hx1_zero : x1 = 0 := beq_iff_eq.mp hx1z
      have h0 : (x ^ B * 2 ^ ((e / B) % B)) % m = 0 := by rw [← hx1_eq, hx1_zero]
      have hdvd : m ∣ (x ^ B * 2 ^ ((e / B) % B)) := Nat.dvd_of_mod_eq_zero h0
      have hB_ne : B ≠ 0 := by positivity
      have hdvd2 : m ∣ (x ^ B * 2 ^ ((e / B) % B)) ^ B * 2 ^ (e % B) :=
        dvd_mul_of_dvd_left (dvd_pow hdvd hB_ne) _
      rw [hpow_comb] at hdvd2
      exact (Nat.mod_eq_zero_of_dvd hdvd2).symm
    · rw [if_neg hx1z]
      rcases ih (e % B) x1 hx1_lt with ⟨hx2_lt, hx2_eq⟩
      refine ⟨hx2_lt, ?_⟩
      rw [hx2_eq]
      have h1 : x1 ≡ x ^ B * 2 ^ ((e / B) % B) [MOD m] := by
        rw [Nat.ModEq, hx1_eq, Nat.mod_mod]
      have h2 : x1 ^ B * 2 ^ (e % B % B) ≡ (x ^ B * 2 ^ ((e / B) % B)) ^ B * 2 ^ (e % B) [MOD m] := by
        rw [Nat.mod_mod]
        exact (h1.pow B).mul_right _
      rw [h2, hpow_comb]

private lemma pow2ModStart_spec (m : ℕ) (hm : 1 < m) :
    ∀ {Bs w}, ValidSplits Bs w → ∀ (e : ℕ), e < 2 ^ w →
      pow2ModStart m Bs e = 2 ^ e % m := by
  intro Bs w hvs
  induction hvs with
  | nil =>
    intro e he
    have h := (stepBits_spec m hm 16 e 1 hm).2
    rw [one_pow, one_mul, Nat.mod_eq_of_lt he] at h
    exact h
  | @cons Bs w hvs ih =>
    intro e he
    dsimp only [pow2ModStart]
    set B := 2 ^ w
    have hB_pos : 0 < B := by positivity
    have hB2 : 2 ^ (2 * w) = B * B := by rw [two_mul, pow_add]
    by_cases hhi : e / B == 0
    · rw [if_pos hhi]
      have he_lt : e < B := by
        have h0 : e / B = 0 := beq_iff_eq.mp hhi
        exact (Nat.div_eq_zero_iff_lt hB_pos).mp h0
      exact ih e he_lt
    · rw [if_neg hhi]
      have hhi_lt : e / B < B := by
        rw [hB2] at he
        exact Nat.div_lt_of_lt_mul he
      have hx1_eq : pow2ModStart m Bs (e / B) = 2 ^ (e / B) % m := ih (e / B) hhi_lt
      set x1 := pow2ModStart m Bs (e / B)
      have hx1_lt : x1 < m := by rw [hx1_eq]; exact Nat.mod_lt _ (by omega)
      have hdecomp : B * (e / B) + e % B = e := Nat.div_add_mod e B
      by_cases hx1z : x1 == 0
      · rw [if_pos hx1z]
        have hx1_zero : x1 = 0 := beq_iff_eq.mp hx1z
        have hdvd : m ∣ 2 ^ (e / B) := Nat.dvd_of_mod_eq_zero (by rw [← hx1_eq, hx1_zero])
        have hdvd2 : m ∣ (2 ^ (e / B)) ^ B * 2 ^ (e % B) :=
          dvd_mul_of_dvd_left (dvd_pow hdvd (by positivity)) _
        have hpow : (2 ^ (e / B)) ^ B * 2 ^ (e % B) = 2 ^ e := by
          rw [← pow_mul, mul_comm (e / B) B, ← pow_add, hdecomp]
        rw [hpow] at hdvd2
        exact (Nat.mod_eq_zero_of_dvd hdvd2).symm
      · rw [if_neg hx1z]
        have hfull := (pow2ModFull_spec m hm hvs (e % B) x1 hx1_lt).2
        rw [hfull]
        have h1 : x1 ≡ 2 ^ (e / B) [MOD m] := by
          rw [Nat.ModEq, hx1_eq, Nat.mod_mod]
        have h2 : x1 ^ B * 2 ^ (e % B % B) ≡ (2 ^ (e / B)) ^ B * 2 ^ (e % B) [MOD m] := by
          rw [Nat.mod_mod]
          exact (h1.pow B).mul_right _
        rw [h2]
        congr 1
        rw [← pow_mul, mul_comm (e / B) B, ← pow_add, hdecomp]

private def mkSplitsAux : ℕ → ℕ → List ℕ → List ℕ
  | 0, _, acc => acc
  | d + 1, b, acc => mkSplitsAux d (b * b) (b :: acc)

private def splits14 : List ℕ :=
  mkSplitsAux 10 (2 ^ 16) []

private def bMax14 : ℕ :=
  match splits14 with
  | B :: _ => B * B
  | [] => 2 ^ 16

private lemma mkSplitsAux_valid :
    ∀ (d w : ℕ) (Bs : List ℕ), ValidSplits Bs w →
      ValidSplits (mkSplitsAux d (2 ^ w) Bs) (2 ^ d * w) := by
  intro d
  induction d with
  | zero =>
    intro w Bs hvs
    simpa [mkSplitsAux] using hvs
  | succ d ih =>
    intro w Bs hvs
    dsimp only [mkSplitsAux]
    have hsq : 2 ^ w * 2 ^ w = 2 ^ (2 * w) := by rw [two_mul, pow_add]
    rw [hsq]
    have h := ih (2 * w) (2 ^ w :: Bs) (ValidSplits.cons hvs)
    have hexp : 2 ^ d * (2 * w) = 2 ^ (d + 1) * w := by rw [pow_succ]; ring
    rwa [hexp] at h

private lemma splits14_valid : ValidSplits splits14 16384 := by
  have h := mkSplitsAux_valid 10 16 [] ValidSplits.nil
  simpa [splits14] using h

private lemma bMax14_eq : bMax14 = 2 ^ 16384 := by
  have hvs : ValidSplits splits14 16384 := splits14_valid
  generalize hW : 16384 = W at hvs
  cases h : splits14 with
  | nil => rw [h] at hvs; cases hvs; omega
  | cons B Bs =>
    rw [h] at hvs
    cases hvs with
    | @cons _ w _ =>
      have hw : w = 8192 := by omega
      subst hw
      dsimp only [bMax14]
      rw [h]
      dsimp only
      rw [← pow_add, ← two_mul]

private lemma not_prime_of_fermat {m : ℕ} (h2 : 2 < m) (hflt : 2 ^ (m - 1) % m ≠ 1) :
    ¬ m.Prime := by
  intro hm
  have : Fact m.Prime := ⟨hm⟩
  have h2ne : (2 : ZMod m) ≠ 0 := by
    intro hz
    have hd : m ∣ 2 := (ZMod.natCast_eq_zero_iff 2 m).mp (by simpa using hz)
    have := Nat.le_of_dvd (by omega) hd
    omega
  have h1 : (2 : ZMod m) ^ (m - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hcast : ((2 ^ (m - 1) : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) := by
    simpa using h1
  have hmod : 2 ^ (m - 1) % m = 1 % m := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
  rw [Nat.mod_eq_of_lt (by omega : 1 < m)] at hmod
  exact hflt hmod

private def checkFermatK (k : ℕ) : Bool :=
  let e := fastTotient (3998 - k)
  let he := e / 2
  let m := k * powBinAux (k + 1) 14 he 1 - 1
  e % 2 == 0 && 2 < m && m - 1 < bMax14 && pow2ModStart m splits14 (m - 1) != 1

private lemma checkFermatK_sound {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 3995)
    (h : checkFermatK k = true) :
    ¬ (k * (k + 1) ^ ((3998 - k).totient / 2) - 1).Prime := by
  dsimp only [checkFermatK] at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at h
  rcases h with ⟨⟨⟨_, hm2⟩, hmlt⟩, hpow⟩
  have htot : fastTotient (3998 - k) = (3998 - k).totient :=
    fastTotient_eq (3998 - k) (by omega) (by omega)
  have hhe_lt : (3998 - k).totient / 2 < 2 ^ 14 := by
    have := Nat.totient_le (3998 - k)
    omega
  have hm_eq : k * powBinAux (k + 1) 14 (fastTotient (3998 - k) / 2) 1 - 1 =
      k * (k + 1) ^ ((3998 - k).totient / 2) - 1 := by
    rw [htot, powBinAux_spec 14 (k + 1) _ 1 hhe_lt, one_mul]
  rw [hm_eq] at hm2 hmlt hpow
  rw [bMax14_eq] at hmlt
  rw [pow2ModStart_spec _ (by omega) splits14_valid _ hmlt] at hpow
  exact not_prime_of_fermat hm2 hpow

private def fermatChunk_0 : List ℕ := [
  516, 609, 1383, 1424, 1494, 1805, 2097, 2208, 2344, 2379, 2903, 3007, 3038, 3338, 3483, 3794, 3976
]

private def fermatChunk_1 : List ℕ := [
  3, 284, 459, 612, 1140, 1524, 1754, 1827, 1878, 2011, 2183, 2397, 2778, 3761, 3812, 3936
]

private def fermatChunk_2 : List ℕ := [
  439, 482, 1050, 1082, 1707, 1953, 2121, 2330, 2424, 2469, 2583, 3399, 3444, 3619, 3701, 3784
]

private def fermatChunk_3 : List ℕ := [
  480, 551, 679, 1554, 1719, 1910, 2015, 2139, 2538, 3020, 3057, 3093, 3110, 3140, 3177, 3684
]

private def fermatChunk_4 : List ℕ := [
  367, 452, 678, 737, 1629, 1829, 1838, 2081, 2214, 2298, 2431, 2855, 2918, 3304, 3332, 3524
]

private def fermatChunk_5 : List ℕ := [
  132, 515, 789, 1454, 1656, 1689, 2040, 2238, 2349, 2529, 2628, 2762, 3087, 3617, 3736, 3825
]

private def fermatChunk_6 : List ℕ := [
  79, 420, 811, 860, 1164, 1244, 1542, 1563, 2072, 2273, 2324, 2499, 3084, 3362, 3869
]

private def fermatChunk_7 : List ℕ := [
  339, 356, 880, 972, 1487, 1638, 1662, 1687, 1934, 2131, 2544, 3149, 3156, 3755, 3759, 3917
]

private def fermatChunk_8 : List ℕ := [
  2, 159, 264, 835, 863, 875, 1070, 1598, 2117, 2421, 2793, 2909, 3170, 3204, 3261, 3632
]

private def fermatChunk_9 : List ℕ := [
  304, 350, 879, 881, 1008, 1599, 2252, 2484, 2505, 2736, 2805, 2911, 2936, 3272, 3717, 3779
]

private def fermatChunk_10 : List ℕ := [
  279, 305, 654, 842, 1557, 1847, 1850, 1904, 2103, 2279, 2824, 3135, 3535, 3783, 3828, 3918, 3965
]

private def fermatChunk_11 : List ℕ := [
  271, 740, 784, 857, 984, 1329, 1595, 1668, 2403, 2723, 3167, 3240, 3279, 3575, 3582, 3792
]

private def fermatChunk_12 : List ℕ := [
  399, 462, 528, 1283, 1447, 2104, 2149, 2163, 2348, 2555, 2664, 3218, 3237, 3475, 3692, 3727
]

private def fermatChunk_13 : List ℕ := [
  248, 681, 1109, 1239, 1620, 1685, 1775, 1925, 1980, 2508, 2680, 3098, 3105, 3288, 3651, 3656
]

private def fermatChunk_14 : List ℕ := [
  194, 765, 1167, 1264, 1883, 1991, 2007, 2459, 2559, 2573, 2856, 3335, 3367, 3380, 3699, 3903, 3944
]

private def fermatChunk_15 : List ℕ := [
  38, 200, 999, 1104, 1327, 1803, 1832, 2032, 2210, 2370, 2571, 2607, 2985, 3544, 3713
]

private def fermatChunk_16 : List ℕ := [
  390, 563, 801, 856, 1278, 1305, 1533, 2174, 2244, 2334, 2799, 2813, 3002, 3188, 3372, 3618
]

private def fermatChunk_17 : List ℕ := [
  138, 249, 285, 839, 1144, 1578, 1649, 1872, 2352, 2715, 2790, 3428, 3511, 3519
]

private def fermatChunk_18 : List ℕ := [
  605, 720, 923, 1005, 1119, 1512, 1937, 2340, 2345, 2819, 3089, 3275, 3469, 3530
]

private def fermatChunk_19 : List ℕ := [
  33, 195, 773, 1137, 1950, 2027, 2361, 2405, 2450, 2873, 3129, 3201, 3251, 3847
]

private def fermatAll : List ℕ :=
  fermatChunk_0 ++ fermatChunk_1 ++ fermatChunk_2 ++ fermatChunk_3 ++ fermatChunk_4 ++ fermatChunk_5 ++ fermatChunk_6 ++ fermatChunk_7 ++ fermatChunk_8 ++ fermatChunk_9 ++ fermatChunk_10 ++ fermatChunk_11 ++ fermatChunk_12 ++ fermatChunk_13 ++ fermatChunk_14 ++ fermatChunk_15 ++ fermatChunk_16 ++ fermatChunk_17 ++ fermatChunk_18 ++ fermatChunk_19

private theorem fermatChunk_0_ok : fermatChunk_0.all checkFermatK = true := by
  decide +kernel

private theorem fermatChunk_1_ok : fermatChunk_1.all checkFermatK = true := by
  decide +kernel

private theorem fermatChunk_2_ok : fermatChunk_2.all checkFermatK = true := by
  decide +kernel

private theorem fermatChunk_3_ok : fermatChunk_3.all checkFermatK = true := by
  decide +kernel

private theorem fermatChunk_4_ok : fermatChunk_4.all checkFermatK = true := by
  decide +kernel

private theorem fermatChunk_5_ok : fermatChunk_5.all checkFermatK = true := by
  decide +kernel

private theorem fermatChunk_6_ok : fermatChunk_6.all checkFermatK = true := by
  decide +kernel

private theorem fermatChunk_7_ok : fermatChunk_7.all checkFermatK = true := by
  decide +kernel

private theorem fermatChunk_8_ok : fermatChunk_8.all checkFermatK = true := by
  decide +kernel

private theorem fermatChunk_9_ok : fermatChunk_9.all checkFermatK = true := by
  decide +kernel

private theorem fermatChunk_10_ok : fermatChunk_10.all checkFermatK = true := by
  decide +kernel

private theorem fermatChunk_11_ok : fermatChunk_11.all checkFermatK = true := by
  decide +kernel

private theorem fermatChunk_12_ok : fermatChunk_12.all checkFermatK = true := by
  decide +kernel

private theorem fermatChunk_13_ok : fermatChunk_13.all checkFermatK = true := by
  decide +kernel

private theorem fermatChunk_14_ok : fermatChunk_14.all checkFermatK = true := by
  decide +kernel

private theorem fermatChunk_15_ok : fermatChunk_15.all checkFermatK = true := by
  decide +kernel

private theorem fermatChunk_16_ok : fermatChunk_16.all checkFermatK = true := by
  decide +kernel

private theorem fermatChunk_17_ok : fermatChunk_17.all checkFermatK = true := by
  decide +kernel

private theorem fermatChunk_18_ok : fermatChunk_18.all checkFermatK = true := by
  decide +kernel

private theorem fermatChunk_19_ok : fermatChunk_19.all checkFermatK = true := by
  decide +kernel


private lemma all_append_true {α : Type*} {p : α → Bool} {l₁ l₂ : List α}
    (h₁ : l₁.all p = true) (h₂ : l₂.all p = true) : (l₁ ++ l₂).all p = true := by
  rw [List.all_append, h₁, h₂]
  rfl

private lemma fermatAll_ok : ∀ k ∈ fermatAll, checkFermatK k = true := by
  have hall : fermatAll.all checkFermatK = true :=
    all_append_true (all_append_true (all_append_true (all_append_true (all_append_true (all_append_true (all_append_true (all_append_true (all_append_true (all_append_true (all_append_true (all_append_true (all_append_true (all_append_true (all_append_true (all_append_true (all_append_true (all_append_true (all_append_true (fermatChunk_0_ok) fermatChunk_1_ok) fermatChunk_2_ok) fermatChunk_3_ok) fermatChunk_4_ok) fermatChunk_5_ok) fermatChunk_6_ok) fermatChunk_7_ok) fermatChunk_8_ok) fermatChunk_9_ok) fermatChunk_10_ok) fermatChunk_11_ok) fermatChunk_12_ok) fermatChunk_13_ok) fermatChunk_14_ok) fermatChunk_15_ok) fermatChunk_16_ok) fermatChunk_17_ok) fermatChunk_18_ok) fermatChunk_19_ok
  intro k hk
  exact List.all_eq_true.mp hall k hk

private def checkEntry (k w : ℕ) : Bool :=
  let e := fastTotient (3998 - k)
  let he := e / 2
  if e % 2 != 0 then false
  else if w == 0 then
    fermatAll.contains k
  else if 100000000 ≤ w then
    let r := w - 100000000
    he % 2 == 0 && r * r == k && (2 ≤ r || 2 ≤ he / 2)
  else
    1 < w && w < 33554431 &&
    (k * powModSmallAux w 14 (k + 1) he 1) % w == 1 &&
    (25 ≤ he || w < k * powBinAux (k + 1) 6 he 1 - 1)

private def checkBlock (start : ℕ) : List ℕ → Bool
  | [] => true
  | w :: ws => checkEntry start w && checkBlock (start + 1) ws

private lemma checkBlock_spec :
    ∀ (ws : List ℕ) (start : ℕ), checkBlock start ws = true →
      ∀ k, start ≤ k → k < start + ws.length → ∃ w, checkEntry k w = true := by
  intro ws
  induction ws with
  | nil =>
    intro start _ k h1 h2
    simp at h2
    omega
  | cons w ws ih =>
    intro start h k h1 h2
    simp only [checkBlock, Bool.and_eq_true] at h
    rcases eq_or_lt_of_le h1 with rfl | hlt
    · exact ⟨w, h.1⟩
    · simp only [List.length_cons] at h2
      exact ih (start + 1) h.2 k (by omega) (by omega)

private lemma checkEntry_sound {k w : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 3995)
    (h : checkEntry k w = true) :
    (3998 - k).totient % 2 = 0 ∧
      ¬ (k * (k + 1) ^ ((3998 - k).totient / 2) - 1).Prime := by
  have htot : fastTotient (3998 - k) = (3998 - k).totient :=
    fastTotient_eq (3998 - k) (by omega) (by omega)
  dsimp only [checkEntry] at h
  rw [htot] at h
  set e := (3998 - k).totient
  set he := e / 2
  have he_even : e % 2 = 0 := by
    by_contra hne
    have : (e % 2 != 0) = true := bne_iff_ne.mpr hne
    rw [if_pos this] at h
    exact Bool.false_ne_true h
  have hne0 : (e % 2 != 0) = false := by simp [he_even]
  rw [if_neg (by simp [hne0])] at h
  refine ⟨he_even, ?_⟩
  by_cases hw0 : w == 0
  · rw [if_pos hw0] at h
    have hmem : k ∈ fermatAll := by simpa using h
    exact checkFermatK_sound hk1 hk2 (fermatAll_ok k hmem)
  · rw [if_neg hw0] at h
    by_cases hw1 : 100000000 ≤ w
    · rw [if_pos hw1] at h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      rcases h with ⟨⟨hhe_even, hr_sq⟩, hbig⟩
      set r := w - 100000000
      set j := he / 2
      have hhe_eq : he = 2 * j := by omega
      have hge1 : 1 ≤ r := by
        by_contra h0
        have hr0 : r = 0 := by omega
        rw [hr0] at hr_sq
        omega
      have hj1 : 1 ≤ j := by
        have he_ge2 : 2 ≤ e := by
          have : 2 < 3998 - k := by omega
          rcases Nat.totient_even this with ⟨m, hm⟩
          have hpos : 0 < e := Nat.totient_pos.mpr (by omega)
          omega
        omega
      set A := r * (k + 1) ^ j
      have hA_ge : 3 ≤ A := by
        have hpow1 : 2 ≤ (k + 1) ^ j := by
          calc 2 ≤ k + 1 := by omega
            _ = (k + 1) ^ 1 := (pow_one _).symm
            _ ≤ (k + 1) ^ j := Nat.pow_le_pow_right (by omega) hj1
        rcases hbig with hr2 | hj2
        · calc 3 ≤ 2 * 2 := by omega
            _ ≤ r * (k + 1) ^ j := Nat.mul_le_mul hr2 hpow1
        · have hpow2 : 4 ≤ (k + 1) ^ j := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ (k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
              _ ≤ (k + 1) ^ j := Nat.pow_le_pow_right (by omega) hj2
          calc 3 ≤ 1 * 4 := by omega
            _ ≤ r * (k + 1) ^ j := Nat.mul_le_mul hge1 hpow2
      have hfac : k * (k + 1) ^ he - 1 = (A - 1) * (A + 1) := by
        have hsq : k * (k + 1) ^ he = A * A := by
          have hAA : A * A = (r * r) * ((k + 1) ^ j) ^ 2 := by
            dsimp only [A]
            ring
          rw [hAA, hr_sq, hhe_eq, mul_comm 2 j, pow_mul]
        rw [hsq]
        have hA1 : A = (A - 1) + 1 := by omega
        have hAA1 : A * A = (A - 1) * (A + 1) + 1 := by
          conv_lhs => rw [hA1]
          conv_rhs => rw [show A + 1 = (A - 1) + 2 by omega]
          ring
        omega
      rw [hfac]
      exact Nat.not_prime_mul (by omega) (by omega)
    · rw [if_neg hw1] at h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      rcases h with ⟨⟨⟨hw_gt1, hw_lt_cap⟩, hmod1⟩, hlt_m⟩
      have hhe_lt14 : he < 2 ^ 14 := by
        have := Nat.totient_le (3998 - k)
        omega
      have hpow_mod : powModSmallAux w 14 (k + 1) he 1 % w = (k + 1) ^ he % w := by
        simpa using powModSmallAux_spec w 14 (k + 1) he 1 hhe_lt14
      have hkpow_mod : (k * (k + 1) ^ he) % w = 1 := by
        have h1 : k * powModSmallAux w 14 (k + 1) he 1 ≡ k * (k + 1) ^ he [MOD w] :=
          Nat.ModEq.mul_left k hpow_mod
        rw [← h1]
        exact hmod1
      have hkpow_ge1 : 1 ≤ k * (k + 1) ^ he := by
        have : 1 ≤ (k + 1) ^ he := Nat.one_le_pow _ _ (by omega)
        nlinarith
      have hdvd : w ∣ k * (k + 1) ^ he - 1 := by
        apply Nat.dvd_of_mod_eq_zero
        have h1 : k * (k + 1) ^ he = (k * (k + 1) ^ he - 1) + 1 := by omega
        have h2 : ((k * (k + 1) ^ he - 1) + 1) % w = 1 := by rw [← h1, hkpow_mod]
        have hw1_mod : 1 % w = 1 := Nat.mod_eq_of_lt hw_gt1
        have h3 : (k * (k + 1) ^ he - 1) % w < w := Nat.mod_lt _ (by omega)
        rw [Nat.add_mod, hw1_mod] at h2
        by_cases h0 : (k * (k + 1) ^ he - 1) % w = 0
        · exact h0
        · by_cases hwm1 : (k * (k + 1) ^ he - 1) % w + 1 < w
          · rw [Nat.mod_eq_of_lt hwm1] at h2; omega
          · have : (k * (k + 1) ^ he - 1) % w + 1 = w := by omega
            rw [this, Nat.mod_self] at h2; omega
      have hw_lt_M : w < k * (k + 1) ^ he - 1 := by
        rcases hlt_m with h25 | hsmall
        · have hpow25 : 33554432 ≤ (k + 1) ^ he := by
            calc 33554432 = 2 ^ 25 := by norm_num
              _ ≤ (k + 1) ^ 25 := Nat.pow_le_pow_left (by omega) 25
              _ ≤ (k + 1) ^ he := Nat.pow_le_pow_right (by omega) h25
          have : 33554432 ≤ k * (k + 1) ^ he := by nlinarith
          omega
        · by_cases h25 : 25 ≤ he
          · have hpow25 : 33554432 ≤ (k + 1) ^ he := by
              calc 33554432 = 2 ^ 25 := by norm_num
                _ ≤ (k + 1) ^ 25 := Nat.pow_le_pow_left (by omega) 25
                _ ≤ (k + 1) ^ he := Nat.pow_le_pow_right (by omega) h25
            have : 33554432 ≤ k * (k + 1) ^ he := by nlinarith
            omega
          · have hhe6 : he < 2 ^ 6 := by omega
            rw [powBinAux_spec 6 (k + 1) he 1 hhe6, one_mul] at hsmall
            exact hsmall
      intro hprime
      rcases hprime.eq_one_or_self_of_dvd w hdvd with h1 | h2 <;> omega

private def block_0 : List ℕ := [
  100000001, 0, 0, 100000002, 19, 5, 3, 7, 100000003, 3, 967, 64811, 3, 11, 7, 100000004, 41413, 17, 3, 19, 5, 3, 11, 67, 100000005,
  5, 73, 3, 7, 839, 13, 31, 0, 3, 17, 100000006, 3, 0, 19, 179, 1723, 3023, 3, 7, 41, 3, 1773791, 71, 100000007, 7,
  97, 3, 7, 19, 263, 5, 7, 3, 8221, 17, 3, 23, 81649, 100000008, 167, 313, 5, 13, 19309, 3, 5, 17, 3, 73, 41,
  3, 17, 7, 0, 6481, 100000009, 3, 47, 49429, 3, 5, 6211, 3, 97, 8191, 15733, 7, 89, 3, 7, 13, 3, 97, 7, 100000010,
  5, 43, 3, 23, 13, 3, 67, 13163, 3, 109, 5, 3, 7, 7, 3, 7, 23, 3, 347, 7, 100000011, 24631, 61, 3, 29,
  5, 3, 127, 113, 3, 5, 0, 3, 7, 11, 13, 17, 0, 3, 23, 5, 3, 113, 100000012, 3, 5, 5, 3, 7, 53,
  137, 13, 191, 3, 7, 5, 3, 11, 0, 3, 83, 7, 3, 241817, 238789, 3, 613, 29, 100000013, 373, 5, 3, 467, 31, 37,
  5, 11, 3, 89, 11, 3, 103, 7, 83, 757, 5, 3, 17, 1637, 3, 11, 349, 3, 0, 0, 100000014, 7, 67, 3, 0
]

private def block_1 : List ℕ := [
  103, 3, 491, 7, 3, 5, 80231, 3, 13, 73, 3, 47, 11, 3, 103, 5, 3, 7, 23, 3, 7, 17, 3, 107, 100000015,
  3, 179, 16729, 3, 1951, 17, 3, 7, 17, 3, 5, 19, 3, 7, 359, 3, 23, 11, 3, 79, 5, 3, 0, 0, 3,
  5, 55469, 3, 113, 23, 12589, 419, 19, 19, 7, 5, 3, 929, 0, 3, 5, 7, 3, 13, 7, 0, 229589, 17, 3, 113,
  11, 3, 40093, 0, 3, 5, 7, 3, 0, 0, 3, 13, 7, 100000017, 11, 5, 3, 73, 313, 3, 5, 709, 3, 2843, 4603,
  3, 7, 257, 0, 0, 5, 5, 230729, 7, 3, 5, 701, 3, 29, 2897, 3, 43, 43, 3, 199, 276251, 3, 7, 100000018, 3,
  5, 8951, 3, 31, 7, 3, 9277, 70843, 3, 43207, 23, 3, 199, 0, 3, 5, 53, 3, 7, 43, 3, 7, 167, 3, 0,
  5, 971, 17, 7, 11, 0, 89, 3, 223, 163, 100000019, 137, 83, 3, 7, 5, 0, 29, 701, 3, 5, 7, 3, 23, 59,
  191, 31, 13, 3, 31, 5, 3, 359, 850177, 3, 5, 6897929, 3, 97, 0, 11, 17, 7, 3, 907, 5, 3, 1879, 0, 100000020
]

private def block_2 : List ℕ := [
  5, 239, 3, 19, 141319, 3, 7, 2593, 3, 307, 5, 3, 61, 7, 173, 79, 2903, 3, 13, 0, 3, 7, 15131, 11, 937,
  5, 5, 7, 1409, 3, 5, 11, 3, 709, 7, 3, 277, 23, 0, 61, 100000021, 3, 11, 461, 3, 5, 1429, 3, 7, 7,
  23, 0, 179, 3, 17, 5, 3, 2663, 0, 3, 17, 0, 3, 3583, 11, 3, 19, 3389, 3, 7, 2333, 3, 401, 11, 3,
  11, 7, 3, 2089, 0, 3, 0, 137, 100000022, 11, 5, 59, 11, 59219, 3, 5, 281, 3, 17, 13, 3, 47, 7, 1091, 3469,
  5, 3, 13, 109, 3, 5, 5, 3, 23, 157, 3, 7, 29, 3, 0, 0, 19, 23, 7, 3, 5, 521, 3, 127, 383,
  3, 821, 0, 100000023, 37, 109, 3, 7, 13, 11, 5, 12589, 3, 271, 7, 3, 11, 4211, 3, 211, 31, 3, 347, 474137, 3,
  0, 5, 3, 7, 1489, 3, 773, 67, 3, 397, 7, 3, 0, 23, 3, 5, 167, 3, 251, 271, 3, 571, 11, 3, 7,
  100000024, 3, 577, 1861, 3, 5, 7, 3, 857, 67, 3, 53, 71, 3, 31, 19, 3, 101, 2161, 3, 7, 17, 3, 13, 60601
]

private def block_3 : List ℕ := [
  3, 4603, 7, 3, 0, 5, 1471, 43, 0, 3, 5, 0, 3, 23, 9544109, 3, 7, 7366379, 3, 7, 17, 3, 307, 7, 100000025,
  5, 5, 3, 163, 17, 3, 47, 1567333, 3, 47, 5, 3, 7, 263, 3, 5, 412807, 3, 523, 7, 3, 19, 271, 3, 11,
  379, 3, 3919, 0, 13, 5, 72341, 3, 7, 41, 3, 349, 137, 61, 73, 5, 5, 119611, 140663, 3, 5, 43, 3, 59, 109,
  100000026, 13, 0, 0, 7, 0, 3, 53, 839, 3, 5, 7, 3, 19, 7, 281, 69061, 653, 3, 397, 5, 3, 13, 37, 3,
  5, 151, 3, 19, 3209, 3, 11, 7, 3, 19, 5, 3, 888773, 19, 3, 17, 23, 3, 11, 0, 3, 7, 7, 3, 7,
  5, 29, 353, 100000027, 3, 73, 43, 3, 608483, 53, 3, 0, 26863, 1277, 0, 5, 3, 7, 113, 3, 5, 5, 3, 23, 7,
  3, 941, 1021, 3, 570781, 151, 3, 5881, 47, 13, 5, 281, 3, 7, 0, 3, 17, 13, 3, 3505457, 5, 3, 0, 29, 3,
  79, 13, 3, 172307, 599, 3, 6288077, 31, 0, 7, 5, 3, 7, 0, 3, 5, 7, 3, 13, 11, 3, 587, 23, 3, 17
]

private def block_4 : List ℕ := [
  0, 3, 20483, 643, 3, 5, 17, 3, 109, 43, 0, 197, 7, 3, 11, 5, 3, 61, 113, 3, 5, 31, 3, 83, 17191,
  3, 7, 107, 3, 997, 11, 11, 13, 7, 0, 5, 19, 3, 0, 23, 100000029, 0, 421, 3, 211, 5, 3, 7, 859, 3,
  5, 23, 3, 13, 7, 0, 0, 461, 3, 0, 5, 3, 0, 11, 3, 5, 227, 3, 7, 149, 3, 7, 43, 3, 0,
  7, 3, 5197, 0, 0, 0, 71, 3, 13697, 67, 3, 23, 109, 3, 7, 5, 3, 29, 173, 3, 5, 7, 3, 109, 100000030,
  3, 17, 103, 3, 7, 5, 3, 257, 19, 3, 7, 1166057, 3, 179, 2333, 3, 619, 7, 37, 4789, 5, 3, 0, 1487, 3,
  5, 11, 3, 61027, 4349, 619, 7, 23, 3, 883, 659, 3, 31, 7, 3, 811, 7, 3, 691, 107, 3, 23, 97, 3, 13,
  5, 5, 7, 7, 3, 5, 89, 3, 69233, 7, 100000031, 31, 13, 3, 241, 5, 3, 7, 3761, 3, 5, 0, 3, 7, 11,
  23, 90353, 53, 26357, 19, 7, 3, 11, 0, 3, 5, 5, 3, 7, 52147, 3, 131, 29, 3, 7, 1033, 3, 7, 0, 1931
]

private def block_5 : List ℕ := [
  5, 7, 3, 197, 0, 3, 17, 0, 3, 61, 5, 3, 23, 7321, 3, 5, 157, 3, 4799, 199, 3, 17299, 7, 258031, 113,
  7, 5, 13, 131, 3, 5, 5, 3, 277, 107, 3, 7, 17, 3, 7, 2087, 3, 13, 7, 3, 5, 199, 3, 11, 0,
  3, 7, 8693, 3, 12781, 547, 3, 7, 13, 3, 5, 201121, 3, 532607, 7, 3, 1139557, 29, 3, 0, 5261, 3, 79, 29, 3,
  3559, 1361, 3, 7, 48179, 3, 0, 110603, 3, 379, 5, 3, 53, 100000033, 3, 5, 11, 3, 1565041, 59, 16759, 37057, 251, 3, 7,
  5, 3, 20749, 0, 3, 5, 7, 3, 0, 131, 17, 137, 907, 3, 17681, 2797, 3, 1381, 0, 71, 5, 7, 3, 7, 359,
  3, 1361, 7, 3, 19, 5, 3, 1284823, 13, 3, 5, 0, 3, 337, 0, 3, 7, 17, 0, 13, 5, 5, 31, 7, 3,
  5, 156749, 3, 8893, 67, 100000034, 7, 28961, 3, 17, 383, 3, 7, 0, 3, 5, 0, 3, 349, 7, 3, 191, 7, 3, 151,
  5, 3, 43, 283207, 3, 5, 19, 3, 7, 83, 3, 83, 46727, 3, 154097, 5, 3, 167, 7, 11, 31, 1787, 3, 1987, 17
]

private def block_6 : List ℕ := [
  3, 67061, 102769, 3, 7, 5, 203789, 17, 17, 3, 5, 7, 3, 23, 7, 3, 19, 569, 3, 23, 5, 3, 13, 107, 100000035,
  5, 521, 3, 523, 107, 23, 73, 7, 3, 953, 571, 3, 13, 0, 3, 29, 17, 3, 0, 61, 3, 7, 313, 3, 79,
  5, 3, 293, 7, 3, 5, 79, 3, 131, 173, 3, 13, 3684047, 0, 19, 23, 5, 7, 587, 3, 5, 149, 3, 37, 7,
  3, 47, 0, 13, 6944299, 5, 3, 0, 13, 3, 5, 67, 3, 7, 7, 823, 7, 17, 3, 1678321, 100000036, 3, 641, 4903, 3,
  5, 11, 3, 7, 0, 3, 751, 19, 3, 7, 4783, 3, 7, 13, 73, 5, 7, 3, 80207, 479, 3, 17, 4583, 3, 331,
  5, 0, 41, 0, 3, 5, 11, 3, 127, 23, 89, 19, 7, 383, 389, 5, 3, 45817, 13, 3, 5, 167, 3, 31, 1009,
  17, 7, 7, 3, 7, 5, 3, 103, 7, 57493, 5, 7, 3, 79, 37, 3, 11, 4576889, 100000037, 23, 5, 3, 7, 7, 3,
  5, 59, 3, 13, 7, 3, 18313, 0, 13, 1627, 5, 3, 23, 83, 3, 5, 4177, 3, 7, 17, 3, 31, 11, 3, 179
]

private def block_7 : List ℕ := [
  5, 3, 373, 673, 3, 5, 191, 3, 7, 463, 3, 43, 3229, 3, 7, 17, 3, 13, 33617, 3, 457, 7, 3, 0, 3313,
  3, 331, 1272991, 3, 7, 5, 5, 853, 2057791, 3, 5, 2087, 3, 3733, 701, 3, 11, 7, 100000038, 11, 5, 0, 47629, 881, 3,
  103, 107, 3, 0, 11, 3, 7, 479, 285179, 3761, 23, 3, 17, 7, 3, 5, 5, 3, 661, 13, 3, 2657, 2171203, 3, 17,
  5, 3, 7, 787, 2341, 7, 151, 3, 2617, 7, 3, 0, 911, 3, 23, 5, 3, 7, 0, 4397, 31, 11, 3, 7, 12713,
  3, 59, 23, 3, 47, 5, 3, 19, 101, 3, 5, 0, 3, 89, 5851, 3, 13, 41, 3, 7, 100000039, 3, 71, 0, 3,
  5, 7, 3, 233, 7, 29, 6582461, 0, 3, 7, 1120081, 3, 11909, 691, 3, 5, 0, 3, 10687, 719, 3, 461, 7, 3, 463,
  1831, 719, 193, 0, 3, 5, 0, 3, 19, 17, 3, 7, 0, 3, 967, 5, 3, 17, 7, 3, 5, 397, 3, 11, 79,
  3, 5512627, 0, 3, 353, 5, 3, 7, 53, 3, 5, 5, 3, 83, 7, 3, 2536057, 23, 3, 0, 5, 5, 0, 0, 100000040
]

private def block_8 : List ℕ := [
  5, 13, 3, 7, 19, 3, 7, 509, 3, 137, 5, 3, 13, 7, 739, 5, 347, 3, 108541, 0, 3, 23, 241, 167, 7,
  5, 5, 31, 0, 3, 11, 7, 3, 181, 23, 3, 353, 0, 3, 11, 17, 3, 877, 31, 3, 5, 1093, 3, 0, 359,
  251, 193, 7, 3, 59, 0, 3, 937, 11783, 3, 5, 0, 3, 19, 6203, 3, 7, 0, 3, 151, 5, 5, 11, 7, 3,
  97, 179, 3, 19, 73, 100000041, 31, 29, 3, 0, 5, 0, 7, 0, 3, 5, 19, 3, 233, 7, 43, 11, 43, 3, 1583,
  5, 3, 37, 13, 3, 5, 0, 3, 7, 315421, 11, 793553, 41759, 3, 19, 7, 3, 17, 0, 3, 5, 1471, 3, 79, 113,
  3, 2707, 599, 3, 7, 1151, 3, 23, 311, 3, 5, 7, 3, 11, 377339, 3, 419, 23, 3, 139, 3050263, 5, 379, 1867, 3,
  5, 5, 3, 0, 3739, 3, 5003, 7, 103, 59, 239, 3, 79, 100000042, 3, 5, 137, 3, 43, 2347, 3, 7, 7, 3, 0,
  5, 3, 347, 7, 3, 71, 13, 3, 52697, 11, 3, 59, 6691, 11, 13, 23, 41, 7, 941, 101, 11, 1567, 3, 199, 7
]

private def block_9 : List ℕ := [
  3, 947, 0, 3, 0, 5, 3, 13, 157, 3, 419, 103, 3, 7, 9661, 37, 277, 193, 288767, 997201, 7, 3, 17971, 839, 3,
  5, 0, 3, 0, 31, 3, 0, 912763, 3, 7, 29, 3, 0, 281, 3, 3391123, 7, 3, 151, 389, 3, 0, 569, 100000043, 0,
  5, 3, 43, 17, 11, 5, 251, 3, 19889, 43, 3, 13, 7, 3, 29, 5, 5, 13, 359, 3, 5, 0, 3, 3767, 673,
  3, 7, 0, 3, 7, 5, 3, 0, 7, 3, 5, 15139, 3, 2381, 23, 3, 212701, 11, 3, 107, 126457, 3, 7, 29, 3,
  5, 3619507, 3, 0, 7, 3, 13, 89, 3, 0, 1099741, 3, 43, 13, 33083, 31, 23, 3, 7, 269, 3, 17, 19, 3, 0,
  5, 3, 479, 1223, 3, 5, 26981, 3, 0, 19, 9479, 0, 13, 3, 7, 5, 3, 7, 565661, 3, 5, 7, 3, 19, 0,
  3, 139, 0, 3, 1618613, 43, 3, 31, 19, 2677, 5, 7, 3, 13, 827, 3, 223, 7, 3, 113, 3084203, 3, 739, 3162839, 3,
  5, 1097, 3, 43, 0, 3, 7, 149, 3, 31, 659, 5, 3678517, 7, 3, 0, 19, 3, 23, 13, 3, 7, 13, 103, 880519
]

private def block_10 : List ℕ := [
  6079, 3, 7, 97, 3, 5, 0, 3, 139, 7, 0, 197, 1997, 3, 0, 31, 3, 103, 89, 3, 19, 59, 3, 7, 100000045,
  3, 0, 11, 3, 19, 5, 0, 677813, 7, 3, 5, 5457229, 3, 7, 0, 3, 13, 9679, 3, 7, 5, 31, 121063, 419, 3,
  5, 7, 3, 31, 13, 89, 13, 17, 3, 11519, 5, 3, 680203, 19, 3, 5, 5, 3, 103, 1523, 3, 0, 7, 3, 17,
  313, 3, 19, 6863, 3, 0, 19, 3, 421, 401981, 3, 7, 37, 3, 883, 227, 3, 653, 7, 3, 5, 0, 3, 173, 185681,
  3, 23, 0, 0, 557, 5, 3, 7, 17, 3, 5, 103, 3, 137, 7, 100000046, 0, 19, 67, 13, 0, 3, 569, 23, 3,
  5, 1276049, 3, 7, 7, 0, 7, 13, 3, 773, 7, 3, 31817, 0, 3, 79, 9721, 3, 17, 23, 3, 29, 19, 0, 7,
  11, 3, 103, 13, 3, 421, 7, 3, 13, 79, 3, 1538311, 0, 3, 107, 5, 17, 11, 47, 3, 5, 4937, 3, 0, 146921,
  157, 107, 7, 3, 421, 97, 3, 0, 11, 3, 5, 5, 3, 28669, 223, 3, 7, 61, 3, 9932207, 5, 3, 13, 7, 3
]

private def block_11 : List ℕ := [
  347, 7, 3, 163, 19, 3, 149, 0, 100000047, 0, 61, 3, 7, 0, 13, 23, 367, 3, 13, 7, 3, 349471, 7, 186437, 5167,
  11, 3, 7, 719, 3, 5, 5, 3, 7, 2013533, 3, 7, 0, 73, 67, 7, 3, 19, 0, 3, 5, 11, 3, 7, 13,
  29, 0, 77587, 3, 7, 5, 3, 47363, 821, 3, 5, 7, 3, 89, 89, 3, 2176877, 61403, 3, 23, 5, 167, 0, 673, 241,
  5, 19, 3, 0, 37, 3, 3137, 7, 3, 109, 5, 3, 541, 19, 3, 5, 4603517, 3, 823, 31, 3, 7, 0, 281, 29,
  5, 3, 2080961, 100000048, 3, 5, 47, 3, 557, 83, 3, 7, 17, 3, 13, 617, 3, 7, 19, 17, 5, 103, 3, 0, 7,
  3, 29, 73, 3, 0, 26111, 3, 57037, 0, 11, 5, 743, 3, 7, 0, 3, 283, 571, 0, 0, 5, 3, 0, 0, 3,
  5, 0, 3, 5441, 11, 3, 11, 44729, 3, 7, 0, 3, 137, 18913, 3, 5, 7, 3, 37, 0, 11, 463, 157667, 3, 929,
  2381, 3, 397, 0, 3, 5, 7, 3, 7, 199, 3, 29, 7, 3, 409, 1531, 3, 79, 23, 3, 5, 0, 3, 11, 241
]

private def block_12 : List ℕ := [
  100000049, 7, 0, 3, 0, 5, 3, 13, 7, 3, 2531, 983, 3, 907297, 2621, 3, 151, 139, 17, 19, 0, 3, 7, 0, 3,
  5, 5, 3, 1009741, 7, 0, 13, 23, 3, 9613, 3863, 3, 59009, 17, 3, 5, 41, 3, 7, 11, 3, 7, 157, 3, 0,
  5, 3, 1583, 467, 173, 5, 5936509, 3, 0, 151, 3, 19, 11677, 3, 7, 7, 5, 11, 0, 3, 5, 7, 3, 61, 23,
  3, 175519, 3559, 3, 7, 5, 3, 17, 0, 3, 5, 23, 3, 7, 23, 3, 13, 7, 3, 4472113, 29, 3, 11, 0, 100000050,
  17, 41, 3, 59, 0, 3, 7, 0, 3, 13, 523, 37, 83, 7, 11, 5, 71, 3, 19, 271, 3, 173, 6368053, 3, 13,
  5, 13, 7, 0, 3, 1673279, 29, 3, 17, 7, 3, 53, 0, 43, 13, 43, 3, 29, 0, 3, 5, 5, 3, 7, 389,
  131, 4813, 19, 3, 0, 7, 3, 31, 0, 113, 29, 6566407, 3, 7, 59, 3, 41, 17, 3, 7, 0, 3, 0, 257, 53,
  17, 7, 3, 251, 79, 3, 181, 0, 3, 19, 5, 3, 23, 8123, 3, 5, 281, 3, 28621, 79, 3, 131, 7, 563851, 11
]

private def block_13 : List ℕ := [
  100000051, 3, 113, 1621, 3, 5, 0, 3, 16127, 11, 3, 7, 304069, 3, 7, 757, 3, 769, 7, 3, 5, 15817, 3, 1222513, 2383,
  3, 13, 0, 3, 29, 9211117, 5, 7, 375227, 3, 7, 2857, 3, 53, 7, 3, 379, 367, 3, 1129, 5, 3, 547, 331, 3,
  5, 241, 3, 7, 397, 3, 281, 57689, 3, 302971, 7, 3, 53, 0, 3, 5, 5, 3, 7, 17, 5737, 154247, 67, 3, 7,
  1523, 3, 7, 24469, 0, 29, 7, 3, 2693, 11, 3, 11, 19, 3, 266993, 103, 3, 61, 48017, 47, 5, 37, 3, 11, 23,
  3, 37, 7, 139, 19, 5, 5, 45281, 87313, 3, 5, 5, 3, 19, 0, 3, 7, 7, 6089, 1258469, 431, 3, 0, 7, 3,
  5, 53, 3, 317, 59, 3, 131, 683, 3, 173, 0, 3, 7, 773, 3, 7, 467, 3, 13, 7, 3, 73, 7, 3, 29,
  5, 3, 7, 2161, 3, 19, 13, 3, 7, 29, 3, 0, 41, 3, 179, 5, 31189, 23, 443, 3, 5, 42719, 3, 3209, 11,
  3, 1753, 0, 3, 7, 5, 3, 13, 593, 3, 5, 7, 3, 17, 0, 3, 673, 0, 3, 7, 5, 3, 13, 0, 580231
]

private def block_14 : List ℕ := [
  5, 311, 3, 6912539, 0, 3, 23, 7, 100000053, 821, 11, 3, 0, 97, 3, 5, 11, 3, 0, 73, 3, 7, 7, 0, 7,
  5, 5, 257, 7, 3, 5, 23, 3, 1991929, 71, 3, 349, 23, 3, 17, 5, 3, 7, 8863, 3, 5, 29, 3, 8119651, 7,
  3, 367, 101, 3, 0, 0, 3, 107747, 1301, 3, 23, 8193907, 3, 7, 1709, 3, 608213, 643, 3, 23, 7, 5, 0, 7, 31,
  5, 1787, 3, 239, 709, 3, 1783, 47, 3, 7, 5, 3, 3023, 193, 3, 5, 7, 3, 29, 53, 3, 55579, 43, 3, 13,
  5, 3, 0, 823841, 3, 5, 5, 3, 0, 67, 0, 41, 7, 3, 773, 100000054, 3, 0, 11, 3, 7, 257, 3, 29, 17,
  3, 7, 17, 3, 1069, 5, 3, 19, 7, 5879, 0, 23, 3, 31, 19, 3, 7, 199, 3, 17, 79, 5, 7, 29, 3,
  5, 5, 3, 1097, 7, 3, 53, 5591, 4561, 13, 5, 3, 317, 37, 3, 5, 311, 3, 7, 7, 3, 4591, 13, 3, 911,
  5, 3, 1361, 71, 3, 5, 1279, 3, 11, 0, 3, 71, 733, 3, 7, 5, 59, 17, 19, 3, 103, 7, 3, 1879, 23
]

private def block_15 : List ℕ := [
  3, 0, 19, 3, 318289, 5, 0, 31, 3251, 3, 5, 419, 3, 7, 3919, 113, 13, 7, 3, 0, 5, 3, 991, 71551, 100000055,
  2377, 5, 3, 23, 71, 11, 7, 373, 3, 2063, 5, 5, 0, 7, 7003943, 5, 7, 3, 8957771, 193, 3, 7, 11, 3, 11,
  101, 3, 7, 7, 3, 5, 0, 3, 103, 7, 3, 307, 53, 11, 457, 5, 3, 29, 59, 3, 31, 11, 3, 7, 23,
  3, 67, 17, 197, 283, 7, 3, 100517, 0, 3, 5, 0, 3, 0, 13, 67, 11, 0, 3, 7, 5, 3, 0, 479, 3,
  5, 7, 3, 19, 0, 3, 991, 101, 3, 0, 193, 5, 811, 1259, 5584421, 7, 41, 3, 7, 3083, 3, 521, 7, 3, 131,
  5, 3, 11, 0, 3, 5, 23, 3, 13, 0, 23, 7, 418459, 17, 0, 5, 3, 11827, 7, 3, 5, 13, 3, 0, 211,
  3, 239, 23, 3, 13, 0, 3, 7, 149, 6311, 5717, 109, 3, 6197, 7, 3, 0, 29, 3, 0, 131, 3, 53, 4219, 11,
  5, 0, 3, 7, 23, 3, 31, 17, 3, 73, 5, 5, 0, 26423, 3, 5, 397, 3, 11, 4572679, 3, 17, 31, 3, 7
]

private def block_16 : List ℕ := [
  0, 3, 7, 0, 3, 5, 7, 3, 181, 7, 23689, 59, 113, 3, 911, 5, 3, 0, 1301, 3, 5, 167, 3, 61, 487,
  3, 13, 7, 3, 26597, 5, 19, 163, 19, 3, 733, 0, 3, 103, 0, 3, 7, 17, 3, 7, 5, 367, 577, 100000057, 3,
  0, 6761, 3, 4569811, 17, 3, 31, 36497, 41, 857, 0, 3, 7, 7511341, 3, 5, 107, 3, 107, 7, 167, 0, 7, 3, 0,
  929, 3, 23, 0, 653, 1831, 23, 3, 7, 79, 3, 379, 0, 3, 13567, 5, 3, 73, 7, 3, 5, 53, 3, 7, 115987,
  3, 47, 11, 0, 7, 5, 5, 7, 89, 3, 5, 7, 3, 4621, 2213, 3, 17, 2089, 3, 7, 13931, 3, 11, 421, 3,
  5, 43, 3, 107, 19, 3, 0, 7, 3, 0, 23, 3, 0, 59, 3, 5, 31, 3, 41, 569, 3, 7, 24103, 3, 131,
  279329, 3, 47, 7, 41, 37, 71, 3, 359, 19, 3, 0, 6938081, 100000058, 593, 5, 0, 7, 47, 3, 5, 0, 3, 565069, 7,
  17, 103, 11, 127, 0, 5, 3, 7, 137, 3, 5, 17, 3, 7, 47, 6282607, 7, 19, 3, 19157, 7, 3, 367, 0, 3
]

private def block_17 : List ℕ := [
  47, 13, 3, 421, 47, 3, 755767, 353, 3, 7, 307, 3, 41, 89, 3, 5, 7, 3, 41, 7, 3, 23, 2311, 3, 7,
  5, 5, 0, 59, 3, 7, 5, 3, 26813, 11, 3, 59, 7, 3, 19, 59, 3, 1867, 0, 3, 5, 11, 3, 1381451, 19,
  431, 7, 23, 3, 11, 120163, 3, 11, 7, 3, 13, 83, 3, 191, 103, 3, 63533, 73, 0, 127, 5, 11, 7, 7, 0,
  5, 11, 3, 4877, 7, 100000059, 151, 0, 3, 23, 5, 3, 7, 29, 3, 5, 2239, 3, 7, 17, 17, 7, 337, 23, 13,
  7, 3, 17, 29, 3, 5, 5, 3, 3659, 11, 0, 5, 11, 3, 7, 5, 3, 7, 0, 1621, 5, 7, 3, 0, 571,
  3, 277, 23, 3, 0, 61, 3, 52163, 787, 0, 5, 2381, 3, 2549, 89, 3, 41, 7, 0, 23, 5, 3, 67, 58111, 3,
  5, 557, 3, 17, 13, 3, 7, 409, 349, 1117, 89, 3, 1759, 7, 3, 5, 4957, 3, 31531, 31, 3, 7, 23, 3, 0,
  778559, 3, 7, 373, 3, 10957, 0, 3, 47, 7, 3, 3469, 17, 3, 29, 5, 3, 179, 499, 3, 29423, 31, 3, 7, 311
]

private def block_18 : List ℕ := [
  3, 13, 617, 3, 43, 5, 3, 2017, 83, 3, 11, 14879, 3, 7, 11, 8059, 0, 0, 0, 7, 5, 3, 7, 23, 3,
  5, 7, 3, 127, 7, 21943, 0, 2843, 3, 23, 97, 11, 439, 167, 43, 5, 7, 3, 7, 19, 3, 173, 7, 3, 137,
  0, 3, 1249, 13, 7, 0, 2273071, 3, 19, 479749, 3, 7, 62633, 233, 293, 307, 5, 181, 7, 3, 5, 5, 3, 151, 56843,
  3, 7, 19, 3, 643, 53, 3, 7, 0, 3, 5, 383, 3, 11, 7, 11, 0, 13, 3, 13, 1091, 3, 7, 0, 3,
  0, 1378561, 3, 7, 92669, 3, 17, 41, 3, 67, 5, 3, 0, 7, 4517, 19, 0, 3, 11, 17837, 100000061, 109, 283, 3, 7,
  5, 0, 9349, 97, 3, 5, 7, 3, 13, 241, 0, 479263, 419, 3, 1733, 5, 3, 613, 67, 3, 5, 5, 3, 7, 64871,
  3, 11, 7, 3, 0, 73, 3, 17, 0, 3, 0, 23, 3, 29, 11, 3, 7, 131, 3, 349, 59, 3, 41, 7, 13,
  5, 89, 3, 0, 131, 3, 19, 0, 0, 11, 5, 5, 7, 107, 3, 1609, 0, 3, 0, 7, 3, 503, 7, 17, 171403
]

private def block_19 : List ℕ := [
  53, 3, 131, 23, 3, 5, 743, 3, 7, 7, 3, 0, 1399, 3, 4957, 5, 3, 146617, 59, 3, 37, 23, 3, 7, 0,
  3, 14843, 0, 3, 7, 17, 5, 7, 151, 11, 281357, 7, 3, 179, 13, 3, 127, 199, 100000062, 233, 5, 0, 29, 4973, 3,
  7, 61, 3, 27793, 17, 681409, 13, 7, 2791, 73, 5, 3, 17, 83, 3, 5, 5, 3, 0, 41, 1583, 7, 11, 3, 7,
  23, 4397, 109, 7, 13, 5, 7, 3, 593, 138661, 3, 23993, 109, 3, 23, 359, 3, 7, 17, 1889, 5, 13, 3, 23, 7,
  3, 19, 0, 1307, 23, 19, 3, 67, 59, 3, 5, 5, 3, 7, 1741, 3, 0, 0, 227, 11, 7, 3, 1288697, 275963, 3,
  5, 41, 3, 7, 11, 47, 37, 44111, 3, 7, 0, 3, 29, 103, 3, 41, 7, 3, 0, 718657, 3, 1543, 13, 7, 2860457,
  61169, 11, 11, 293, 701, 7, 8761, 3, 12781, 419, 3, 23, 7, 3, 0, 5, 29, 13, 100000063, 3, 79, 43, 3, 13, 29,
  0, 7, 7, 1601, 4111, 5, 3, 827, 7, 3, 11, 5, 3, 41, 8867, 7, 5, 184969, 19, 89
]

private theorem block_0_ok : checkBlock 1 block_0 = true := by
  decide +kernel

private theorem block_1_ok : checkBlock 201 block_1 = true := by
  decide +kernel

private theorem block_2_ok : checkBlock 401 block_2 = true := by
  decide +kernel

private theorem block_3_ok : checkBlock 601 block_3 = true := by
  decide +kernel

private theorem block_4_ok : checkBlock 801 block_4 = true := by
  decide +kernel

private theorem block_5_ok : checkBlock 1001 block_5 = true := by
  decide +kernel

private theorem block_6_ok : checkBlock 1201 block_6 = true := by
  decide +kernel

private theorem block_7_ok : checkBlock 1401 block_7 = true := by
  decide +kernel

private theorem block_8_ok : checkBlock 1601 block_8 = true := by
  decide +kernel

private theorem block_9_ok : checkBlock 1801 block_9 = true := by
  decide +kernel

private theorem block_10_ok : checkBlock 2001 block_10 = true := by
  decide +kernel

private theorem block_11_ok : checkBlock 2201 block_11 = true := by
  decide +kernel

private theorem block_12_ok : checkBlock 2401 block_12 = true := by
  decide +kernel

private theorem block_13_ok : checkBlock 2601 block_13 = true := by
  decide +kernel

private theorem block_14_ok : checkBlock 2801 block_14 = true := by
  decide +kernel

private theorem block_15_ok : checkBlock 3001 block_15 = true := by
  decide +kernel

private theorem block_16_ok : checkBlock 3201 block_16 = true := by
  decide +kernel

private theorem block_17_ok : checkBlock 3401 block_17 = true := by
  decide +kernel

private theorem block_18_ok : checkBlock 3601 block_18 = true := by
  decide +kernel

private theorem block_19_ok : checkBlock 3801 block_19 = true := by
  decide +kernel


private lemma all_1_to_3995 (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 3995) :
    ∃ w, checkEntry k w = true := by

  if h0 : k < 201 then
    exact checkBlock_spec block_0 1 block_0_ok k (by omega) (by have : block_0.length = 200 := (by decide +kernel); omega)

  else if h1 : k < 401 then
    exact checkBlock_spec block_1 201 block_1_ok k (by omega) (by have : block_1.length = 200 := (by decide +kernel); omega)

  else if h2 : k < 601 then
    exact checkBlock_spec block_2 401 block_2_ok k (by omega) (by have : block_2.length = 200 := (by decide +kernel); omega)

  else if h3 : k < 801 then
    exact checkBlock_spec block_3 601 block_3_ok k (by omega) (by have : block_3.length = 200 := (by decide +kernel); omega)

  else if h4 : k < 1001 then
    exact checkBlock_spec block_4 801 block_4_ok k (by omega) (by have : block_4.length = 200 := (by decide +kernel); omega)

  else if h5 : k < 1201 then
    exact checkBlock_spec block_5 1001 block_5_ok k (by omega) (by have : block_5.length = 200 := (by decide +kernel); omega)

  else if h6 : k < 1401 then
    exact checkBlock_spec block_6 1201 block_6_ok k (by omega) (by have : block_6.length = 200 := (by decide +kernel); omega)

  else if h7 : k < 1601 then
    exact checkBlock_spec block_7 1401 block_7_ok k (by omega) (by have : block_7.length = 200 := (by decide +kernel); omega)

  else if h8 : k < 1801 then
    exact checkBlock_spec block_8 1601 block_8_ok k (by omega) (by have : block_8.length = 200 := (by decide +kernel); omega)

  else if h9 : k < 2001 then
    exact checkBlock_spec block_9 1801 block_9_ok k (by omega) (by have : block_9.length = 200 := (by decide +kernel); omega)

  else if h10 : k < 2201 then
    exact checkBlock_spec block_10 2001 block_10_ok k (by omega) (by have : block_10.length = 200 := (by decide +kernel); omega)

  else if h11 : k < 2401 then
    exact checkBlock_spec block_11 2201 block_11_ok k (by omega) (by have : block_11.length = 200 := (by decide +kernel); omega)

  else if h12 : k < 2601 then
    exact checkBlock_spec block_12 2401 block_12_ok k (by omega) (by have : block_12.length = 200 := (by decide +kernel); omega)

  else if h13 : k < 2801 then
    exact checkBlock_spec block_13 2601 block_13_ok k (by omega) (by have : block_13.length = 200 := (by decide +kernel); omega)

  else if h14 : k < 3001 then
    exact checkBlock_spec block_14 2801 block_14_ok k (by omega) (by have : block_14.length = 200 := (by decide +kernel); omega)

  else if h15 : k < 3201 then
    exact checkBlock_spec block_15 3001 block_15_ok k (by omega) (by have : block_15.length = 200 := (by decide +kernel); omega)

  else if h16 : k < 3401 then
    exact checkBlock_spec block_16 3201 block_16_ok k (by omega) (by have : block_16.length = 200 := (by decide +kernel); omega)

  else if h17 : k < 3601 then
    exact checkBlock_spec block_17 3401 block_17_ok k (by omega) (by have : block_17.length = 200 := (by decide +kernel); omega)

  else if h18 : k < 3801 then
    exact checkBlock_spec block_18 3601 block_18_ok k (by omega) (by have : block_18.length = 200 := (by decide +kernel); omega)

  else
    exact checkBlock_spec block_19 3801 block_19_ok k (by omega) (by show k < 3801 + block_19.length; have : block_19.length = 195 := (by decide +kernel); omega)


theorem OMA.disproof : ¬ (type_of% @OeisA234360.conjecture_4) := by
  intro hconj
  rcases hconj 3998 (by omega) with ⟨k, hk0, hk3998, p, hp, heq⟩
  by_cases hle : k ≤ 3995
  · rcases all_1_to_3995 k (by omega) hle with ⟨w, hw⟩
    rcases checkEntry_sound (by omega) hle hw with ⟨heven, hnp⟩
    set he := (3998 - k).totient / 2
    have htot_eq : (3998 - k).totient = 2 * he := by omega
    rw [htot_eq, mul_comm 2 he, pow_mul] at heq
    have hsq : (p + 1) ^ 2 = (k * (k + 1) ^ he) ^ 2 := by
      rw [heq]
      ring
    have hval : p + 1 = k * (k + 1) ^ he :=
      Nat.pow_left_injective (by omega : 2 ≠ 0) hsq
    have hp_eq : p = k * (k + 1) ^ he - 1 := by omega
    rw [hp_eq] at hp
    exact hnp hp
  · interval_cases k
    · have htot : (3998 - 3996).totient = 1 := by decide
      rw [htot, pow_one] at heq
      have hdvd : 3996 ^ 2 ∣ (p + 1) ^ 2 := ⟨3997, heq⟩
      have hdvd1 : 3996 ∣ p + 1 := (Nat.pow_dvd_pow_iff (by omega : 2 ≠ 0)).mp hdvd
      rcases hdvd1 with ⟨r, hr⟩
      rw [hr] at heq
      have hr2 : r ^ 2 = 3997 := by nlinarith
      have hr_lo : 63 < r := by nlinarith
      have hr_hi : r < 64 := by nlinarith
      omega
    · have htot : (3998 - 3997).totient = 1 := by decide
      rw [htot, pow_one] at heq
      have hdvd : 3997 ^ 2 ∣ (p + 1) ^ 2 := ⟨3998, heq⟩
      have hdvd1 : 3997 ∣ p + 1 := (Nat.pow_dvd_pow_iff (by omega : 2 ≠ 0)).mp hdvd
      rcases hdvd1 with ⟨r, hr⟩
      rw [hr] at heq
      have hr2 : r ^ 2 = 3998 := by nlinarith
      have hr_lo : 63 < r := by nlinarith
      have hr_hi : r < 64 := by nlinarith
      omega
