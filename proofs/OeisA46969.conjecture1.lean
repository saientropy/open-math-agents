import FormalConjectures.OEIS.«46969»

/-!
Proof of `OeisA46969.conjecture1`:
For every prime `p > 3` such that `q = 2 * p - 1` is also prime, we prove `a p = 12 * q`,
whence `a p / 12 = q` is prime.
1. Since `p > 3` and `2 * p - 1` are prime, `p % 3 = 1`, so `3 ∣ 2 * p + 1` and neither
   `p + 1` nor `2 * p + 1` is prime. By `Bernoulli.vonStaudt_clausen`, `bernoulli (2 * p) = N / 6`
   for an integer `N ≡ 1 (mod 6)`.
2. By Faulhaber's formula (`sum_range_pow`) and `vonStaudt_clausen` for `B_i` (`i < 2 * p`),
   for any prime `ℓ >= 5` not dividing `2 * p + 1` (in particular `ℓ = p` and `ℓ = q`),
   `ℓ^2 ∣ 6 * ∑_{k < ℓ} k^(2p) - ℓ * N`.
3. Using the multiplier-2 shift `(a + ℓ)^(2p) ≡ a^(2p) + 2p * a^(2p-1) * ℓ (mod ℓ^2)`,
   we obtain `p^2 ∣ ∑_{k < p} k^(2p)` (so `p ∣ N`) and `q^2 ∤ ∑_{k < q} k^(2p)` (so `q ∤ N`).
4. Writing `N = p * C`, `C` is coprime to `12 * q`, so `(bernoulli (2 * p) / (2 * p * q)).den = 12 * q`.
-/

private lemma not_dvd_den_int (ℓ : ℕ) (hℓ : ℓ.Prime) (z : ℤ) : ¬ ℓ ∣ (z : ℚ).den := by
  simpa using hℓ.not_dvd_one

private lemma not_dvd_den_nat (ℓ : ℕ) (hℓ : ℓ.Prime) (n : ℕ) : ¬ ℓ ∣ (n : ℚ).den := by
  simpa using hℓ.not_dvd_one

private lemma not_dvd_den_add {ℓ : ℕ} (hℓ : ℓ.Prime) {x y : ℚ}
    (hx : ¬ ℓ ∣ x.den) (hy : ¬ ℓ ∣ y.den) : ¬ ℓ ∣ (x + y).den := by
  intro h
  rcases hℓ.dvd_mul.mp (dvd_trans h (Rat.add_den_dvd x y)) with h1 | h2
  · exact hx h1
  · exact hy h2

private lemma not_dvd_den_sub {ℓ : ℕ} (hℓ : ℓ.Prime) {x y : ℚ}
    (hx : ¬ ℓ ∣ x.den) (hy : ¬ ℓ ∣ y.den) : ¬ ℓ ∣ (x - y).den := by
  rw [sub_eq_add_neg]
  exact not_dvd_den_add hℓ hx (by simpa using hy)

private lemma not_dvd_den_mul {ℓ : ℕ} (hℓ : ℓ.Prime) {x y : ℚ}
    (hx : ¬ ℓ ∣ x.den) (hy : ¬ ℓ ∣ y.den) : ¬ ℓ ∣ (x * y).den := by
  intro h
  rcases hℓ.dvd_mul.mp (dvd_trans h (Rat.mul_den_dvd x y)) with h1 | h2
  · exact hx h1
  · exact hy h2

private lemma not_dvd_den_sum {ι : Type*} {ℓ : ℕ} (hℓ : ℓ.Prime) (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, ¬ ℓ ∣ (f i).den) : ¬ ℓ ∣ (∑ i ∈ s, f i).den := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using hℓ.not_dvd_one
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact not_dvd_den_add hℓ
      (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma den_int_div_nat_dvd (z : ℤ) (b : ℕ) (_hb : b ≠ 0) :
    ((z : ℚ) / (b : ℚ)).den ∣ b := by
  have h : (z : ℚ) / (b : ℚ) = Rat.divInt z b := by
    rw [Rat.divInt_eq_div]
    norm_cast
  rw [h]
  have hd := Rat.den_dvd z b
  exact Int.natCast_dvd_natCast.mp (by simpa [Int.natAbs_natCast] using hd)

private lemma not_dvd_den_nat_div {ℓ : ℕ} (a b : ℕ) (hb : b ≠ 0) (hℓb : ¬ ℓ ∣ b) :
    ¬ ℓ ∣ ((a : ℚ) / (b : ℚ)).den := by
  intro h
  have hdvd : ((a : ℚ) / (b : ℚ)).den ∣ b := by
    simpa using den_int_div_nat_dvd (a : ℤ) b hb
  exact hℓb (dvd_trans h hdvd)

private lemma not_dvd_den_prime_mul_bernoulli {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (i : ℕ) :
    ¬ ℓ ∣ ((ℓ : ℚ) * bernoulli i).den := by
  rcases i with _ | _ | i
  · rw [bernoulli_zero, mul_one]
    exact not_dvd_den_nat ℓ hℓ ℓ
  · rw [bernoulli_one]
    have hEq : (ℓ : ℚ) * (-1 / 2) = ((- (ℓ : ℤ) : ℚ) / (2 : ℕ)) := by
      push_cast
      ring
    rw [hEq]
    intro h
    have hd : (((- (ℓ : ℤ) : ℚ) / (2 : ℕ))).den ∣ 2 := den_int_div_nat_dvd (-ℓ) 2 (by omega)
    have h2 : ℓ ∣ 2 := dvd_trans h hd
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h2)
  · rcases Nat.even_or_odd (i + 2) with ⟨m, hm⟩ | hodd
    · have hi : i + 2 = 2 * m := by omega
      rw [hi]
      obtain ⟨M, hM⟩ := Bernoulli.vonStaudt_clausen m
      have hB : (ℓ : ℚ) * bernoulli (2 * m) =
          (ℓ : ℚ) * (M : ℚ) -
            ∑ r ∈ (Finset.range (2 * m + 2)).filter (fun r => r.Prime ∧ (r - 1) ∣ 2 * m),
              ((ℓ : ℚ) / (r : ℚ)) := by
        have hsub : bernoulli (2 * m) =
            (M : ℚ) - ∑ r ∈ (Finset.range (2 * m + 2)).filter (fun r => r.Prime ∧ (r - 1) ∣ 2 * m),
              (1 : ℚ) / (r : ℚ) := by linarith
        rw [hsub, mul_sub, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
      rw [hB]
      apply not_dvd_den_sub hℓ
      · exact_mod_cast not_dvd_den_int ℓ hℓ (ℓ * M)
      · apply not_dvd_den_sum hℓ
        intro r hr
        simp only [Finset.mem_filter] at hr
        have hrp : r.Prime := hr.2.1
        by_cases hrl : r = ℓ
        · subst hrl
          rw [div_self (Nat.cast_ne_zero.mpr hℓ.ne_zero)]
          simpa using hℓ.not_dvd_one
        · exact not_dvd_den_nat_div ℓ r hrp.ne_zero
            (fun hd => hrl ((Nat.prime_dvd_prime_iff_eq hℓ hrp).mp hd).symm)
    · rw [bernoulli_eq_zero_of_odd hodd (by omega), mul_zero]
      simpa using hℓ.not_dvd_one

private lemma dvd_of_not_dvd_den_div {ℓ : ℕ} (hℓ : ℓ.Prime) (A : ℤ)
    (h : ¬ ℓ ∣ ((A : ℚ) / ((ℓ ^ 2 : ℕ) : ℚ)).den) : (ℓ ^ 2 : ℤ) ∣ A := by
  set r : ℚ := (A : ℚ) / ((ℓ ^ 2 : ℕ) : ℚ)
  have hℓ2_ne : ((ℓ ^ 2 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero 2 hℓ.ne_zero)
  have hden_ne : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_ne_zero
  have hq : (A : ℚ) * (r.den : ℚ) = (r.num : ℚ) * ((ℓ ^ 2 : ℕ) : ℚ) := by
    have hr : (r.num : ℚ) / (r.den : ℚ) = (A : ℚ) / ((ℓ ^ 2 : ℕ) : ℚ) := Rat.num_div_den r
    field_simp [hden_ne, hℓ2_ne] at hr
    linarith
  have hz : A * (r.den : ℤ) = r.num * (ℓ ^ 2 : ℤ) := by
    exact_mod_cast hq
  have hdvd : (ℓ ^ 2 : ℤ) ∣ A * (r.den : ℤ) := ⟨r.num, by linarith⟩
  have hcop : Nat.Coprime (ℓ ^ 2) r.den :=
    ((hℓ.coprime_iff_not_dvd).mpr h).pow_left 2
  have hicop : IsCoprime (ℓ ^ 2 : ℤ) (r.den : ℤ) := by
    exact_mod_cast Nat.isCoprime_iff_coprime.mpr hcop
  exact hicop.dvd_of_dvd_mul_right hdvd

private lemma faulhaber_mod_sq {p ℓ : ℕ} (hp : 3 < p) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hnd : ¬ ℓ ∣ (2 * p + 1)) {N : ℤ} (hB : bernoulli (2 * p) = (N : ℚ) / 6) :
    (ℓ ^ 2 : ℤ) ∣ 6 * (∑ k ∈ Finset.range ℓ, (k : ℤ) ^ (2 * p)) - (ℓ : ℤ) * N := by
  apply dvd_of_not_dvd_den_div hℓ
  have hℓ_ne : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  have hfaul : (∑ k ∈ Finset.range ℓ, (k : ℚ) ^ (2 * p)) =
      (∑ i ∈ Finset.range (2 * p),
        bernoulli i * ((2 * p + 1).choose i : ℚ) * (ℓ : ℚ) ^ (2 * p + 1 - i) / (2 * p + 1 : ℚ)) +
      (ℓ : ℚ) * bernoulli (2 * p) := by
    rw [sum_range_pow ℓ (2 * p), Finset.sum_range_succ, Nat.choose_succ_self_right,
      show 2 * p + 1 - 2 * p = 1 by omega, pow_one]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      rfl
    · have hcast : ((2 * p + 1 : ℕ) : ℚ) = ((2 * p : ℕ) : ℚ) + 1 := by push_cast; ring
      have h2p1 : ((2 * p : ℕ) : ℚ) + 1 ≠ 0 := by positivity
      rw [hcast]
      field_simp [h2p1]
  have hEq : (((6 * (∑ k ∈ Finset.range ℓ, (k : ℤ) ^ (2 * p)) - (ℓ : ℤ) * N : ℤ) : ℚ) /
      ((ℓ ^ 2 : ℕ) : ℚ)) =
      (6 : ℚ) * ∑ i ∈ Finset.range (2 * p),
        (bernoulli i * ((2 * p + 1).choose i : ℚ) * (ℓ : ℚ) ^ (2 * p - 1 - i) / (2 * p + 1 : ℚ)) := by
    push_cast
    rw [hfaul, hB]
    have hsum_div :
        (∑ i ∈ Finset.range (2 * p),
          bernoulli i * ((2 * p + 1).choose i : ℚ) * (ℓ : ℚ) ^ (2 * p + 1 - i) / (2 * p + 1 : ℚ)) =
        (ℓ : ℚ) ^ 2 * ∑ i ∈ Finset.range (2 * p),
          (bernoulli i * ((2 * p + 1).choose i : ℚ) * (ℓ : ℚ) ^ (2 * p - 1 - i) / (2 * p + 1 : ℚ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      by_cases hi_last : i = 2 * p - 1
      · subst hi_last
        have hodd : Odd (2 * p - 1) := ⟨p - 1, by omega⟩
        rw [bernoulli_eq_zero_of_odd hodd (by omega)]
        ring
      · have hexp : 2 * p + 1 - i = (2 * p - 1 - i) + 2 := by omega
        rw [hexp, pow_add]
        ring
    rw [hsum_div]
    field_simp [hℓ_ne]
    ring
  rw [hEq]
  apply not_dvd_den_mul hℓ (not_dvd_den_nat ℓ hℓ 6)
  apply not_dvd_den_sum hℓ
  intro i hi
  rw [Finset.mem_range] at hi
  by_cases hi_last : i = 2 * p - 1
  · subst hi_last
    have hodd : Odd (2 * p - 1) := ⟨p - 1, by omega⟩
    rw [bernoulli_eq_zero_of_odd hodd (by omega)]
    simp [hℓ.not_dvd_one]
  · have hexp : 2 * p - 1 - i = (2 * p - 2 - i) + 1 := by omega
    have hterm :
        bernoulli i * ((2 * p + 1).choose i : ℚ) * (ℓ : ℚ) ^ (2 * p - 1 - i) / (2 * p + 1 : ℚ) =
        ((ℓ : ℚ) * bernoulli i) * ((ℓ : ℚ) ^ (2 * p - 2 - i)) *
          ((((2 * p + 1).choose i : ℕ) : ℚ) / ((2 * p + 1 : ℕ) : ℚ)) := by
      rw [hexp, pow_succ]
      push_cast
      ring
    rw [hterm]
    apply not_dvd_den_mul hℓ
    · apply not_dvd_den_mul hℓ
      · exact not_dvd_den_prime_mul_bernoulli hℓ hℓ2 i
      · exact_mod_cast not_dvd_den_nat ℓ hℓ (ℓ ^ (2 * p - 2 - i))
    · exact not_dvd_den_nat_div ((2 * p + 1).choose i) (2 * p + 1) (by omega) hnd

private lemma add_pow_of_sq_eq_zero {R : Type*} [CommRing R] {a b : R} (hb : b ^ 2 = 0) :
    ∀ m : ℕ, 1 ≤ m → (a + b) ^ m = a ^ m + (m : R) * a ^ (m - 1) * b := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    rcases m with _ | m
    · simp
    · rw [pow_succ, ih (by omega)]
      have hsub : m + 1 - 1 = m := by omega
      have hsub2 : m + 1 + 1 - 1 = m + 1 := by omega
      rw [hsub, hsub2]
      push_cast
      calc (a ^ (m + 1) + (↑m + 1) * a ^ m * b) * (a + b)
          = a ^ (m + 1) * a + (↑m + 1 + 1) * (a ^ m * a) * b + (↑m + 1) * a ^ m * b ^ 2 := by ring
        _ = a ^ (m + 1) * a + (↑m + 1 + 1) * (a ^ m * a) * b := by rw [hb]; ring
        _ = a ^ (m + 1 + 1) + (↑m + 1 + 1) * a ^ (m + 1) * b := by rw [← pow_succ, ← pow_succ]

private lemma sum_Ico_odd_even {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ h : ℕ, ∑ k ∈ Finset.Ico 1 (2 * h + 1), f k =
      (∑ j ∈ Finset.range h, f (2 * j + 1)) + ∑ j ∈ Finset.range h, f (2 * j + 2) := by
  intro h
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show 2 * (h + 1) + 1 = (2 * h + 1) + 2 by omega]
    have hsplit : Finset.Ico 1 (2 * h + 1 + 2) =
        insert (2 * h + 2) (insert (2 * h + 1) (Finset.Ico 1 (2 * h + 1))) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      ih, Finset.sum_range_succ, Finset.sum_range_succ]
    abel

private lemma sum_Ico_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (h : ℕ) :
    ∑ k ∈ Finset.Ico 1 (2 * h + 1), f (2 * k) =
      (∑ j ∈ Finset.range h, f (2 * j + 2)) +
      ∑ j ∈ Finset.range h, f ((2 * h + 1) + (2 * j + 1)) := by
  have hsplit : ∑ k ∈ Finset.Ico 1 (2 * h + 1), f (2 * k) =
      (∑ k ∈ Finset.Ico 1 (h + 1), f (2 * k)) +
      ∑ k ∈ Finset.Ico (h + 1) (2 * h + 1), f (2 * k) :=
    (Finset.sum_Ico_consecutive (fun k => f (2 * k)) (by omega) (by omega)).symm
  rw [hsplit]
  congr 1
  · rw [Finset.sum_Ico_eq_sum_range]
    have hsub : h + 1 - 1 = h := by omega
    rw [hsub]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    omega
  · rw [Finset.sum_Ico_eq_sum_range]
    have hsub : 2 * h + 1 - (h + 1) = h := by omega
    rw [hsub]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    omega

private lemma sum_odd_range (n : ℕ) :
    ∑ j ∈ Finset.range n, (2 * j + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

private lemma sum_pow_range_eq_Ico (ℓ m : ℕ) (hm : 0 < m) :
    ∑ k ∈ Finset.range ℓ, (k : ℤ) ^ m = ∑ k ∈ Finset.Ico 1 ℓ, (k : ℤ) ^ m := by
  rcases ℓ with _ | ℓ
  · simp
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp [zero_pow (by omega : m ≠ 0)]

private lemma pow_sq_dvd_sum_pow_self {p : ℕ} (hp : p.Prime) (h3 : 3 < p) :
    (p ^ 2 : ℤ) ∣ ∑ k ∈ Finset.range p, (k : ℤ) ^ (2 * p) := by
  rw [sum_pow_range_eq_Ico p (2 * p) (by omega)]
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  rcases hodd with ⟨h, hp_eq⟩
  set S : ZMod (p ^ 2) := ∑ k ∈ Finset.Ico 1 p, (k : ZMod (p ^ 2)) ^ (2 * p)
  have hb : ((p : ZMod (p ^ 2))) ^ 2 = 0 := by
    norm_cast
    exact ZMod.natCast_self (p ^ 2)
  have hshift : ∀ a : ℕ, (((p + a : ℕ) : ZMod (p ^ 2)) ^ (2 * p)) = (a : ZMod (p ^ 2)) ^ (2 * p) := by
    intro a
    rw [Nat.cast_add, add_comm, add_pow_of_sq_eq_zero hb (2 * p) (by omega)]
    have hterm : ((2 * p : ℕ) : ZMod (p ^ 2)) * (a : ZMod (p ^ 2)) ^ (2 * p - 1) * (p : ZMod (p ^ 2)) = 0 := by
      push_cast
      calc (2 : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * (a : ZMod (p ^ 2)) ^ (2 * p - 1) * (p : ZMod (p ^ 2))
          = 2 * (a : ZMod (p ^ 2)) ^ (2 * p - 1) * ((p : ZMod (p ^ 2)) ^ 2) := by ring
        _ = 0 := by rw [hb, mul_zero]
    rw [hterm, add_zero]
  have h2S : ((2 : ZMod (p ^ 2)) ^ (2 * p)) * S = S := by
    calc ((2 : ZMod (p ^ 2)) ^ (2 * p)) * S
        = ∑ k ∈ Finset.Ico 1 p, ((2 * k : ℕ) : ZMod (p ^ 2)) ^ (2 * p) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Nat.cast_mul, Nat.cast_ofNat, mul_pow]
      _ = ∑ k ∈ Finset.Ico 1 (2 * h + 1), ((2 * k : ℕ) : ZMod (p ^ 2)) ^ (2 * p) := by rw [hp_eq]
      _ = (∑ j ∈ Finset.range h, ((2 * j + 2 : ℕ) : ZMod (p ^ 2)) ^ (2 * p)) +
          ∑ j ∈ Finset.range h, (((2 * h + 1) + (2 * j + 1) : ℕ) : ZMod (p ^ 2)) ^ (2 * p) :=
          sum_Ico_two_mul (fun x => (x : ZMod (p ^ 2)) ^ (2 * p)) h
      _ = (∑ j ∈ Finset.range h, ((2 * j + 2 : ℕ) : ZMod (p ^ 2)) ^ (2 * p)) +
          ∑ j ∈ Finset.range h, ((2 * j + 1 : ℕ) : ZMod (p ^ 2)) ^ (2 * p) := by
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← hp_eq]
          exact hshift (2 * j + 1)
      _ = (∑ j ∈ Finset.range h, ((2 * j + 1 : ℕ) : ZMod (p ^ 2)) ^ (2 * p)) +
          ∑ j ∈ Finset.range h, ((2 * j + 2 : ℕ) : ZMod (p ^ 2)) ^ (2 * p) := add_comm _ _
      _ = ∑ k ∈ Finset.Ico 1 (2 * h + 1), (k : ZMod (p ^ 2)) ^ (2 * p) :=
          (sum_Ico_odd_even (fun x => (x : ZMod (p ^ 2)) ^ (2 * p)) h).symm
      _ = S := by rw [← hp_eq]
  have hmul_zero : (((2 ^ (2 * p) - 1 : ℕ) : ℤ) * (∑ k ∈ Finset.Ico 1 p, (k : ℤ) ^ (2 * p)) : ZMod (p ^ 2)) = 0 := by
    have h1 : 1 ≤ 2 ^ (2 * p) := Nat.one_le_two_pow
    push_cast [Nat.cast_sub h1]
    have hS_cast : (∑ k ∈ Finset.Ico 1 p, (k : ZMod (p ^ 2)) ^ (2 * p)) = S := rfl
    rw [hS_cast, sub_mul, one_mul, h2S, sub_self]
  have hdvd_mul : (p ^ 2 : ℤ) ∣ ((2 ^ (2 * p) - 1 : ℕ) : ℤ) * ∑ k ∈ Finset.Ico 1 p, (k : ℤ) ^ (2 * p) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa using hmul_zero)
  have hndvd : ¬ p ∣ (2 ^ (2 * p) - 1) := by
    have : Fact p.Prime := ⟨hp⟩
    intro hd
    have hz : ((2 ^ (2 * p) - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    have h1 : 1 ≤ 2 ^ (2 * p) := Nat.one_le_two_pow
    rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hz
    have hflt : (2 : ZMod p) ^ (2 * p) = 4 := by
      rw [mul_comm, pow_mul, ZMod.pow_card]
      norm_num
    rw [hflt] at hz
    have h3z : (3 : ZMod p) = 0 := by
      calc (3 : ZMod p) = 4 - 1 := by norm_num
        _ = 0 := hz
    have hp3 : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp (by simpa using h3z)
    have := Nat.le_of_dvd (by omega) hp3
    omega
  have hcop : Nat.Coprime (p ^ 2) (2 ^ (2 * p) - 1) :=
    ((hp.coprime_iff_not_dvd).mpr hndvd).pow_left 2
  have hicop : IsCoprime (p ^ 2 : ℤ) ((2 ^ (2 * p) - 1 : ℕ) : ℤ) := by
    exact_mod_cast Nat.isCoprime_iff_coprime.mpr hcop
  exact hicop.dvd_of_dvd_mul_left hdvd_mul

private lemma not_pow_sq_dvd_sum_pow_two_sub_one {p : ℕ} (hp' : (2 * p - 1).Prime) (h3 : 3 < p) :
    ¬ ((((2 * p - 1 : ℕ) : ℤ) ^ 2) ∣ ∑ k ∈ Finset.range (2 * p - 1), (k : ℤ) ^ (2 * p)) := by
  set q : ℕ := 2 * p - 1
  rw [sum_pow_range_eq_Ico q (2 * p) (by omega)]
  have hq_eq : q = 2 * (p - 1) + 1 := by omega
  have h2p_eq : 2 * p = q + 1 := by omega
  set T : ZMod (q ^ 2) := ∑ k ∈ Finset.Ico 1 q, (k : ZMod (q ^ 2)) ^ (2 * p)
  have hb : ((q : ZMod (q ^ 2))) ^ 2 = 0 := by
    norm_cast
    exact ZMod.natCast_self (q ^ 2)
  have hshift : ∀ a : ℕ, (((q + a : ℕ) : ZMod (q ^ 2)) ^ (2 * p)) =
      (a : ZMod (q ^ 2)) ^ (2 * p) + (a : ZMod (q ^ 2)) * (q : ZMod (q ^ 2)) := by
    intro a
    rw [Nat.cast_add, add_comm, add_pow_of_sq_eq_zero hb (2 * p) (by omega)]
    have h2p_sub : 2 * p - 1 = q := rfl
    rw [h2p_sub, h2p_eq]
    have : Fact q.Prime := ⟨hp'⟩
    have hflt_dvd : (q : ℤ) ∣ ((a : ℤ) ^ q - (a : ℤ)) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      rw [ZMod.pow_card, sub_self]
    rcases hflt_dvd with ⟨c, hc⟩
    have haq_mul : (a : ZMod (q ^ 2)) ^ q * (q : ZMod (q ^ 2)) =
        (a : ZMod (q ^ 2)) * (q : ZMod (q ^ 2)) := by
      have hdiff : ((a : ZMod (q ^ 2)) ^ q - (a : ZMod (q ^ 2))) * (q : ZMod (q ^ 2)) = 0 := by
        have hcast : (((((a : ℤ) ^ q - (a : ℤ)) * (q : ℤ)) : ℤ) : ZMod (q ^ 2)) = 0 := by
          rw [hc]
          have : (q : ℤ) * c * (q : ℤ) = (q ^ 2 : ℕ) * c := by push_cast; ring
          rw [this]
          push_cast
          rw [hb, zero_mul]
        simpa using hcast
      exact sub_eq_zero.mp (by linear_combination hdiff)
    have hq_mul : ((q + 1 : ℕ) : ZMod (q ^ 2)) * (a : ZMod (q ^ 2)) ^ q * (q : ZMod (q ^ 2)) =
        (a : ZMod (q ^ 2)) * (q : ZMod (q ^ 2)) := by
      push_cast
      calc ((q : ZMod (q ^ 2)) + 1) * (a : ZMod (q ^ 2)) ^ q * (q : ZMod (q ^ 2))
          = (a : ZMod (q ^ 2)) ^ q * ((q : ZMod (q ^ 2)) ^ 2) +
              (a : ZMod (q ^ 2)) ^ q * (q : ZMod (q ^ 2)) := by ring
        _ = (a : ZMod (q ^ 2)) * (q : ZMod (q ^ 2)) := by rw [hb, mul_zero, zero_add, haq_mul]
    rw [hq_mul]
  have h2T : ((2 : ZMod (q ^ 2)) ^ (2 * p)) * T =
      T + (((p - 1) ^ 2 : ℕ) : ZMod (q ^ 2)) * (q : ZMod (q ^ 2)) := by
    calc ((2 : ZMod (q ^ 2)) ^ (2 * p)) * T
        = ∑ k ∈ Finset.Ico 1 q, ((2 * k : ℕ) : ZMod (q ^ 2)) ^ (2 * p) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Nat.cast_mul, Nat.cast_ofNat, mul_pow]
      _ = ∑ k ∈ Finset.Ico 1 (2 * (p - 1) + 1), ((2 * k : ℕ) : ZMod (q ^ 2)) ^ (2 * p) := by
          rw [hq_eq]
      _ = (∑ j ∈ Finset.range (p - 1), ((2 * j + 2 : ℕ) : ZMod (q ^ 2)) ^ (2 * p)) +
          ∑ j ∈ Finset.range (p - 1),
            (((2 * (p - 1) + 1) + (2 * j + 1) : ℕ) : ZMod (q ^ 2)) ^ (2 * p) :=
          sum_Ico_two_mul (fun x => (x : ZMod (q ^ 2)) ^ (2 * p)) (p - 1)
      _ = (∑ j ∈ Finset.range (p - 1), ((2 * j + 2 : ℕ) : ZMod (q ^ 2)) ^ (2 * p)) +
          ∑ j ∈ Finset.range (p - 1),
            (((2 * j + 1 : ℕ) : ZMod (q ^ 2)) ^ (2 * p) +
              ((2 * j + 1 : ℕ) : ZMod (q ^ 2)) * (q : ZMod (q ^ 2))) := by
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← hq_eq]
          exact hshift (2 * j + 1)
      _ = ((∑ j ∈ Finset.range (p - 1), ((2 * j + 1 : ℕ) : ZMod (q ^ 2)) ^ (2 * p)) +
          ∑ j ∈ Finset.range (p - 1), ((2 * j + 2 : ℕ) : ZMod (q ^ 2)) ^ (2 * p)) +
          (∑ j ∈ Finset.range (p - 1), ((2 * j + 1 : ℕ) : ZMod (q ^ 2))) * (q : ZMod (q ^ 2)) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          abel
      _ = (∑ k ∈ Finset.Ico 1 (2 * (p - 1) + 1), (k : ZMod (q ^ 2)) ^ (2 * p)) +
          (((∑ j ∈ Finset.range (p - 1), (2 * j + 1)) : ℕ) : ZMod (q ^ 2)) * (q : ZMod (q ^ 2)) := by
          rw [← sum_Ico_odd_even (fun x => (x : ZMod (q ^ 2)) ^ (2 * p)) (p - 1)]
          push_cast
          rfl
      _ = T + (((p - 1) ^ 2 : ℕ) : ZMod (q ^ 2)) * (q : ZMod (q ^ 2)) := by
          rw [← hq_eq, sum_odd_range]
  intro hdvd
  have hTz : T = 0 := by
    have hcast : ((∑ k ∈ Finset.Ico 1 q, (k : ℤ) ^ (2 * p) : ℤ) : ZMod (q ^ 2)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simpa using hdvd)
    simpa [T] using hcast
  rw [hTz, mul_zero, zero_add] at h2T
  have hprod0 : (((p - 1) ^ 2 * q : ℕ) : ZMod (q ^ 2)) = 0 := by
    simpa [Nat.cast_mul] using h2T.symm
  have hq2_dvd : q ^ 2 ∣ (p - 1) ^ 2 * q := (ZMod.natCast_eq_zero_iff _ _).mp hprod0
  have hq_dvd_sq : q ∣ (p - 1) ^ 2 := by
    have hq_pos : 0 < q := hp'.pos
    rw [sq] at hq2_dvd
    exact (Nat.mul_dvd_mul_iff_right hq_pos).mp hq2_dvd
  have hq_dvd : q ∣ (p - 1) := hp'.dvd_of_dvd_pow hq_dvd_sq
  have hle : q ≤ p - 1 := Nat.le_of_dvd (by omega) hq_dvd
  omega

private lemma den_int_div_nat_of_coprime (C : ℤ) (D : ℕ) (hD : 0 < D)
    (hcop : C.natAbs.Coprime D) : ((C : ℚ) / (D : ℚ)).den = D := by
  set r : ℚ := (C : ℚ) / (D : ℚ)
  have h1 : r.den ∣ D := den_int_div_nat_dvd C D (by omega)
  have hD_ne : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hden_ne : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_ne_zero
  have hq : (C : ℚ) * (r.den : ℚ) = (r.num : ℚ) * (D : ℚ) := by
    have hr : (r.num : ℚ) / (r.den : ℚ) = (C : ℚ) / (D : ℚ) := Rat.num_div_den r
    field_simp [hden_ne, hD_ne] at hr
    linarith
  have hz : C * (r.den : ℤ) = r.num * (D : ℤ) := by exact_mod_cast hq
  have hD_dvd_z : (D : ℤ) ∣ C * (r.den : ℤ) := ⟨r.num, by linarith⟩
  have hD_dvd_nat : D ∣ C.natAbs * r.den := by
    have := Int.natCast_dvd.mp hD_dvd_z
    simpa [Int.natAbs_mul, Int.natAbs_natCast] using this
  have h2 : D ∣ r.den := hcop.symm.dvd_of_dvd_mul_left hD_dvd_nat
  exact Nat.dvd_antisymm h1 h2

theorem OMA.solution : type_of% @OeisA46969.conjecture1 := by
  intro p hp hp' h3
  set q : ℕ := 2 * p - 1 with hq_def
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  have hp_mod3 : p % 3 = 1 := by
    have h0 : p % 3 ≠ 0 := by
      intro h0
      have h3p : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3p
      omega
    have h2 : p % 3 ≠ 2 := by
      intro h2
      have h3q : 3 ∣ q := Nat.dvd_of_mod_eq_zero (by omega)
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp').mp h3q
      omega
    omega
  have hnot_p1 : ¬ (p + 1).Prime := by
    intro hpr
    have h2dvd : 2 ∣ p + 1 := by
      rcases hp_odd with ⟨k, hk⟩
      exact ⟨k + 1, by omega⟩
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpr).mp h2dvd
    omega
  have hnot_2p1 : ¬ (2 * p + 1).Prime := by
    intro hpr
    have h3dvd : 3 ∣ 2 * p + 1 := Nat.dvd_of_mod_eq_zero (by omega)
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).mp h3dvd
    omega
  have hset : (Finset.range (2 * p + 2)).filter (fun r => r.Prime ∧ (r - 1) ∣ 2 * p) = {2, 3} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hrp, hdvd⟩
      rcases Nat.dvd_mul.mp hdvd with ⟨a, b, ha, hb, hab⟩
      rcases Nat.prime_two.eq_one_or_self_of_dvd a ha with ha1 | ha2 <;>
      rcases hp.eq_one_or_self_of_dvd b hb with hb1 | hbp
      · rw [ha1, hb1] at hab; left; omega
      · rw [ha1, hbp] at hab
        have hr : r = p + 1 := by omega
        exact False.elim (hnot_p1 (hr ▸ hrp))
      · rw [ha2, hb1] at hab; right; omega
      · rw [ha2, hbp] at hab
        have hr : r = 2 * p + 1 := by omega
        exact False.elim (hnot_2p1 (hr ▸ hrp))
    · rintro (rfl | rfl)
      · exact ⟨by omega, Nat.prime_two, by omega⟩
      · exact ⟨by omega, Nat.prime_three, dvd_mul_right 2 p⟩
  obtain ⟨M, hM⟩ := Bernoulli.vonStaudt_clausen p
  rw [hset] at hM
  have hsum23 : (∑ r ∈ ({2, 3} : Finset ℕ), (1 : ℚ) / (r : ℚ)) = 5 / 6 := by
    norm_num
  rw [hsum23] at hM
  set N : ℤ := 6 * M - 5 with hN_def
  have hB : bernoulli (2 * p) = (N : ℚ) / 6 := by
    rw [hN_def]
    push_cast
    linarith
  have hp_nd_2p1 : ¬ p ∣ (2 * p + 1) := by
    intro hd
    have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_left p 2)).mp hd
    exact hp.not_dvd_one h1
  have hq_nd_2p1 : ¬ q ∣ (2 * p + 1) := by
    intro hd
    have h2 : q ∣ 2 := by
      have hEq : 2 * p + 1 = q + 2 := by omega
      rw [hEq] at hd
      exact (Nat.dvd_add_right dvd_rfl).mp hd
    have := Nat.le_of_dvd (by omega) h2
    omega
  have hfaul_p := faulhaber_mod_sq h3 hp (by omega) hp_nd_2p1 hB
  have hfaul_q := faulhaber_mod_sq h3 hp' (by omega) hq_nd_2p1 hB
  have hSp := pow_sq_dvd_sum_pow_self hp h3
  have hp2_pN : (p ^ 2 : ℤ) ∣ (p : ℤ) * N := by
    have h6Sp : (p ^ 2 : ℤ) ∣ 6 * ∑ k ∈ Finset.range p, (k : ℤ) ^ (2 * p) :=
      dvd_mul_of_dvd_right hSp 6
    have := dvd_sub h6Sp hfaul_p
    simpa using this
  have hp_N : (p : ℤ) ∣ N := by
    rw [sq] at hp2_pN
    exact (mul_dvd_mul_iff_left (Int.natCast_ne_zero.mpr hp.ne_zero)).mp hp2_pN
  have hq_not_N : ¬ (q : ℤ) ∣ N := by
    intro hqN
    have hq2_qN : (q ^ 2 : ℤ) ∣ (q : ℤ) * N := by
      rw [sq]
      exact mul_dvd_mul_left (q : ℤ) hqN
    have hq2_6T : (q ^ 2 : ℤ) ∣ 6 * ∑ k ∈ Finset.range q, (k : ℤ) ^ (2 * p) := by
      have := dvd_add hfaul_q hq2_qN
      simpa using this
    have hcop_q6 : Nat.Coprime (q ^ 2) 6 := by
      have hq2 : ¬ q ∣ 2 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
      have hq3 : ¬ q ∣ 3 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
      have hc2 : q.Coprime 2 := (hp'.coprime_iff_not_dvd).mpr hq2
      have hc3 : q.Coprime 3 := (hp'.coprime_iff_not_dvd).mpr hq3
      exact (hc2.mul_right hc3).pow_left 2
    have hicop : IsCoprime (q ^ 2 : ℤ) (6 : ℤ) := by
      exact_mod_cast Nat.isCoprime_iff_coprime.mpr hcop_q6
    exact not_pow_sq_dvd_sum_pow_two_sub_one hp' h3 (hicop.dvd_of_dvd_mul_left hq2_6T)
  rcases hp_N with ⟨C, hC⟩
  have hC_nd2 : ¬ (2 : ℤ) ∣ C := by
    intro h2C
    have h2N : (2 : ℤ) ∣ N := by rw [hC]; exact dvd_mul_of_dvd_right h2C _
    omega
  have hC_nd3 : ¬ (3 : ℤ) ∣ C := by
    intro h3C
    have h3N : (3 : ℤ) ∣ N := by rw [hC]; exact dvd_mul_of_dvd_right h3C _
    omega
  have hC_ndq : ¬ (q : ℤ) ∣ C := by
    intro hqC
    exact hq_not_N (by rw [hC]; exact dvd_mul_of_dvd_right hqC _)
  have hcop_C : C.natAbs.Coprime (12 * q) := by
    have hc2 : C.natAbs.Coprime 2 :=
      ((Nat.prime_two.coprime_iff_not_dvd).mpr (fun h => hC_nd2 (Int.natCast_dvd.mpr h))).symm
    have hc3 : C.natAbs.Coprime 3 :=
      ((Nat.prime_three.coprime_iff_not_dvd).mpr (fun h => hC_nd3 (Int.natCast_dvd.mpr h))).symm
    have hcq : C.natAbs.Coprime q :=
      ((hp'.coprime_iff_not_dvd).mpr (fun h => hC_ndq (Int.natCast_dvd.mpr h))).symm
    have hc12 : C.natAbs.Coprime 12 := by
      have : (12 : ℕ) = 2 * 2 * 3 := by norm_num
      rw [this]
      exact (hc2.mul_right hc2).mul_right hc3
    exact hc12.mul_right hcq
  have hap : OeisA46969.a p = 12 * q := by
    unfold OeisA46969.a
    rw [if_neg (by omega)]
    dsimp only
    have hfrac : bernoulli (2 * p) / ((2 * p * (2 * p - 1) : ℕ) : ℚ) =
        (C : ℚ) / ((12 * q : ℕ) : ℚ) := by
      rw [hB, hC, ← hq_def]
      have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      push_cast
      field_simp [hp_ne]
      ring
    rw [hfrac]
    exact den_int_div_nat_of_coprime C (12 * q) (by omega) hcop_C
  rw [hap, Nat.mul_div_right q (by omega)]
  exact hp'
