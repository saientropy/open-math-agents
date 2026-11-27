import FormalConjectures.OEIS.«212334»

/-!
Proof of `OeisA212334.conjecture_2`:
for all primes `p ≥ 5` and integers `r ≥ 2`,
`a (p ^ r) % (p ^ (3 * r + 3)) = a (p ^ (r - 1)) % (p ^ (3 * r + 3))`.
-/

namespace OeisA212334Conj2Proof

open Nat

private def T (n k : ℕ) : ℕ :=
  n.choose k * (n - 1).choose k * (n + k - 1).choose k ^ 2

private def U (p a : ℕ) : Finset ℕ :=
  (Finset.range (p ^ a)).filter (fun k => ¬ p ∣ k)

private lemma isUnit_natCast_zmod {n k : ℕ} (hk : k.Coprime n) : IsUnit (k : ZMod n) :=
  ⟨ZMod.unitOfCoprime k hk, ZMod.coe_unitOfCoprime k hk⟩

private lemma mul_inv_natCast_zmod {n k : ℕ} (hk : k.Coprime n) :
    (k : ZMod n) * (k : ZMod n)⁻¹ = 1 :=
  ZMod.mul_inv_of_unit (k : ZMod n) (isUnit_natCast_zmod hk)

private lemma isUnit_of_not_dvd_pow {p n k : ℕ} (hp : p.Prime) (hk : ¬ p ∣ k) :
    IsUnit (k : ZMod (p ^ n)) :=
  isUnit_natCast_zmod ((hp.coprime_iff_not_dvd.mpr hk).symm.pow_right n)

private lemma mul_inv_of_not_dvd_pow {p n k : ℕ} (hp : p.Prime) (hk : ¬ p ∣ k) :
    (k : ZMod (p ^ n)) * (k : ZMod (p ^ n))⁻¹ = 1 :=
  ZMod.mul_inv_of_unit (k : ZMod (p ^ n)) (isUnit_of_not_dvd_pow hp hk)

private lemma zmod_inv_unique {n : ℕ} {x y : ZMod n} (hx : IsUnit x) (hxy : x * y = 1) :
    x⁻¹ = y := by
  have h1 : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit x hx
  calc
    x⁻¹ = x⁻¹ * (x * y) := by rw [hxy, mul_one]
    _ = (x * x⁻¹) * y := by ring
    _ = y := by rw [h1, one_mul]

private lemma zmod_mul_inv_of_isUnit {n : ℕ} {x y : ZMod n} (hx : IsUnit x) (hy : IsUnit y) :
    (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
  refine zmod_inv_unique (hx.mul hy) ?_
  have h1 : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit x hx
  have h2 : y * y⁻¹ = 1 := ZMod.mul_inv_of_unit y hy
  calc
    x * y * (x⁻¹ * y⁻¹) = (x * x⁻¹) * (y * y⁻¹) := by ring
    _ = 1 := by rw [h1, h2, mul_one]

private lemma zmod_neg_inv_of_isUnit {n : ℕ} {x : ZMod n} (hx : IsUnit x) :
    (-x)⁻¹ = -(x⁻¹) := by
  refine zmod_inv_unique hx.neg ?_
  have h1 : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit x hx
  calc
    (-x) * (-(x⁻¹)) = x * x⁻¹ := by ring
    _ = 1 := h1

private lemma castHom_inv_of_isUnit {m n : ℕ} (hmn : m ∣ n) (x : ZMod n) (hx : IsUnit x) :
    ZMod.castHom hmn (ZMod m) x⁻¹ = (ZMod.castHom hmn (ZMod m) x)⁻¹ := by
  let f := ZMod.castHom hmn (ZMod m)
  have h1 : f x * f x⁻¹ = 1 := by rw [← map_mul, ZMod.mul_inv_of_unit x hx, map_one]
  exact (zmod_inv_unique (hx.map f) h1).symm

private lemma zmod_pow_eq_zero_of_ge {p n k : ℕ} (hk : n ≤ k) :
    (p : ZMod (p ^ n)) ^ k = 0 := by
  have h1 : (p : ZMod (p ^ n)) ^ n = 0 := by
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self (p ^ n)
  have hsplit : k = n + (k - n) := by omega
  rw [hsplit, pow_add, h1, zero_mul]

private lemma mul_eq_zero_of_dvd_of_castHom_eq_zero {p a N c : ℕ} (hp : 0 < p)
    (haN : a ≤ N) (hc : p ^ (N - a) ∣ c) (x : ZMod (p ^ N))
    (hx : ZMod.castHom (pow_dvd_pow p haN) (ZMod (p ^ a)) x = 0) :
    (c : ZMod (p ^ N)) * x = 0 := by
  have : NeZero (p ^ N) := ⟨pow_ne_zero _ (Nat.ne_of_gt hp)⟩
  have hval : (x.val : ZMod (p ^ a)) = 0 := by
    simpa [ZMod.natCast_zmod_val] using hx
  obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff x.val (p ^ a)).mp hval
  obtain ⟨d, hd⟩ := hc
  have hx_eq : x = ((p ^ a * q : ℕ) : ZMod (p ^ N)) := by
    rw [← hq, ZMod.natCast_zmod_val]
  rw [hx_eq, hd]
  have hmul : p ^ (N - a) * d * (p ^ a * q) = p ^ N * (d * q) := by
    have hpow : p ^ (N - a) * p ^ a = p ^ N := by rw [← pow_add, Nat.sub_add_cancel haN]
    calc
      p ^ (N - a) * d * (p ^ a * q) = (p ^ (N - a) * p ^ a) * (d * q) := by ring
      _ = p ^ N * (d * q) := by rw [hpow]
  rw [← Nat.cast_mul, hmul, Nat.cast_mul, ZMod.natCast_self, zero_mul]

private lemma mul_eq_zero_of_dvd_of_castHom_p_eq_zero {p N c : ℕ} (hp : 0 < p)
    (hN : 1 ≤ N) (hc : p ^ (N - 1) ∣ c) (x : ZMod (p ^ N))
    (hx : ZMod.castHom (dvd_pow_self p (by omega : N ≠ 0)) (ZMod p) x = 0) :
    (c : ZMod (p ^ N)) * x = 0 := by
  have : NeZero (p ^ N) := ⟨pow_ne_zero _ (Nat.ne_of_gt hp)⟩
  have hval : (x.val : ZMod p) = 0 := by
    simpa [ZMod.natCast_zmod_val] using hx
  obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff x.val p).mp hval
  obtain ⟨d, hd⟩ := hc
  have hx_eq : x = ((p * q : ℕ) : ZMod (p ^ N)) := by
    rw [← hq, ZMod.natCast_zmod_val]
  rw [hx_eq, hd]
  have hmul : p ^ (N - 1) * d * (p * q) = p ^ N * (d * q) := by
    have hpow : p ^ (N - 1) * p = p ^ N := by rw [← pow_succ, Nat.sub_add_cancel hN]
    calc
      p ^ (N - 1) * d * (p * q) = (p ^ (N - 1) * p) * (d * q) := by ring
      _ = p ^ N * (d * q) := by rw [hpow]
  rw [← Nat.cast_mul, hmul, Nat.cast_mul, ZMod.natCast_self, zero_mul]

private lemma prod_one_add_eq_one_add_sum {α R : Type*} [CommRing R] [DecidableEq α]
    (s : Finset α) (c : R) (hc : c ^ 2 = 0) (f : α → R) :
    ∏ i ∈ s, (1 + c * f i) = 1 + c * ∑ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
    linear_combination (f a * ∑ i ∈ s, f i) * hc

private lemma succ_mul_choose_eq' (n k : ℕ) :
    (n + 1) * n.choose k = (n + 1).choose (k + 1) * (k + 1) := by
  by_cases hkn : k ≤ n
  · have hpos : 0 < k.factorial * (n - k).factorial :=
      Nat.mul_pos (Nat.factorial_pos k) (Nat.factorial_pos (n - k))
    apply Nat.mul_right_cancel hpos
    have h1 := Nat.choose_mul_factorial_mul_factorial hkn
    have h2 := Nat.choose_mul_factorial_mul_factorial (Nat.succ_le_succ hkn)
    have hsub : n + 1 - (k + 1) = n - k := by omega
    rw [hsub] at h2
    calc
      (n + 1) * n.choose k * (k.factorial * (n - k).factorial)
          = (n + 1) * (n.choose k * k.factorial * (n - k).factorial) := by ring
      _ = (n + 1) * n.factorial := by rw [h1]
      _ = (n + 1).factorial := (Nat.factorial_succ n).symm
      _ = (n + 1).choose (k + 1) * (k + 1).factorial * (n - k).factorial := h2.symm
      _ = (n + 1).choose (k + 1) * ((k + 1) * k.factorial) * (n - k).factorial := by
        rw [Nat.factorial_succ]
      _ = (n + 1).choose (k + 1) * (k + 1) * (k.factorial * (n - k).factorial) := by ring
  · have h1 : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : (n + 1).choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h1, h2]

private lemma factorial_mul_choose_pred (n : ℕ) :
    ∀ k, k ≤ n - 1 → k.factorial * (n - 1).choose k = ∏ i ∈ Finset.Icc 1 k, (n - i)
  | 0, _ => by simp
  | k + 1, hk => by
    have ih := factorial_mul_choose_pred n k (by omega)
    have hchoose : (n - 1).choose (k + 1) * (k + 1) = (n - 1).choose k * (n - (k + 1)) := by
      have h := Nat.choose_succ_right_eq (n - 1) k
      have hsub : n - 1 - k = n - (k + 1) := by omega
      rwa [hsub] at h
    rw [Finset.prod_Icc_succ_top (by omega), ← ih, Nat.factorial_succ]
    calc
      (k + 1) * k.factorial * (n - 1).choose (k + 1)
          = k.factorial * ((n - 1).choose (k + 1) * (k + 1)) := by ring
      _ = k.factorial * ((n - 1).choose k * (n - (k + 1))) := by rw [hchoose]
      _ = k.factorial * (n - 1).choose k * (n - (k + 1)) := by ring

private lemma factorial_mul_choose_add (n : ℕ) (hn : 1 ≤ n) :
    ∀ k, k.factorial * (n - 1 + k).choose k = ∏ i ∈ Finset.range k, (n + i)
  | 0 => by simp
  | k + 1 => by
    have ih := factorial_mul_choose_add n hn k
    have h1 : n - 1 + (k + 1) = (n - 1 + k) + 1 := by omega
    have h2 : (n - 1 + k) + 1 = n + k := by omega
    have hchoose : (n + k) * (n - 1 + k).choose k = (n - 1 + (k + 1)).choose (k + 1) * (k + 1) := by
      rw [h1, ← h2]
      exact succ_mul_choose_eq' (n - 1 + k) k
    rw [Finset.prod_range_succ, ← ih, Nat.factorial_succ]
    calc
      (k + 1) * k.factorial * (n - 1 + (k + 1)).choose (k + 1)
          = k.factorial * ((n - 1 + (k + 1)).choose (k + 1) * (k + 1)) := by ring
      _ = k.factorial * ((n + k) * (n - 1 + k).choose k) := by rw [← hchoose]
      _ = k.factorial * (n - 1 + k).choose k * (n + k) := by ring

private lemma prod_Icc_eq_factorial : ∀ n : ℕ, ∏ i ∈ Finset.Icc 1 n, i = n.factorial
  | 0 => by simp
  | n + 1 => by
    rw [Finset.prod_Icc_succ_top (by omega), prod_Icc_eq_factorial n, Nat.factorial_succ]
    ring

private lemma term_prod_int {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n - 1) :
    ((k.factorial : ℤ) ^ 4) * (T n k : ℤ) =
      (n : ℤ) ^ 3 * ((n : ℤ) - k) *
        ∏ i ∈ Finset.Icc 1 (k - 1), ((n : ℤ) ^ 2 - (i : ℤ) ^ 2) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have h0_nat : k.factorial * n.choose k = n * ∏ i ∈ Finset.Icc 1 (k - 1), (n - i) := by
    have hk_eq : k = (k - 1) + 1 := by omega
    have hn_eq : n = (n - 1) + 1 := by omega
    have hch : n * (n - 1).choose (k - 1) = n.choose k * k := by
      conv_lhs => rw [hn_eq]
      conv_rhs => rw [hn_eq, hk_eq]
      exact succ_mul_choose_eq' (n - 1) (k - 1)
    have hfac : k.factorial = k * (k - 1).factorial := by
      cases k with
      | zero => omega
      | succ j => exact Nat.factorial_succ j
    calc
      k.factorial * n.choose k = (k - 1).factorial * (n.choose k * k) := by rw [hfac]; ring
      _ = (k - 1).factorial * (n * (n - 1).choose (k - 1)) := by rw [← hch]
      _ = n * ((k - 1).factorial * (n - 1).choose (k - 1)) := by ring
      _ = n * ∏ i ∈ Finset.Icc 1 (k - 1), (n - i) := by
        rw [factorial_mul_choose_pred n (k - 1) (by omega)]
  have hA_nat : k.factorial * (n - 1).choose k = (n - k) * ∏ i ∈ Finset.Icc 1 (k - 1), (n - i) := by
    rw [factorial_mul_choose_pred n k hkn]
    have hk_eq : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk_eq]
    rw [Finset.prod_Icc_succ_top (by omega), ← hk_eq, mul_comm]
  have hB_nat : k.factorial * (n + k - 1).choose k = n * ∏ i ∈ Finset.Icc 1 (k - 1), (n + i) := by
    have hsub : n + k - 1 = n - 1 + k := by omega
    rw [hsub, factorial_mul_choose_add n hn1 k]
    have hk_eq : k = (k - 1) + 1 := by omega
    rw [hk_eq, Finset.prod_range_succ']
    simp only [add_zero, mul_comm]
    congr 1
    refine Finset.prod_nbij (fun j => j + 1) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢
      omega
    · intro a _ b _ hab
      dsimp at hab
      omega
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_Icc] at hi
      exact ⟨i - 1, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp; omega⟩
    · intro j _; rfl
  have h0 : (k.factorial : ℤ) * (n.choose k : ℤ) =
      (n : ℤ) * ∏ i ∈ Finset.Icc 1 (k - 1), ((n : ℤ) - i) := by
    have h := congr_arg (Nat.cast (R := ℤ)) h0_nat
    push_cast at h
    rw [h]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    simp only [Finset.mem_Icc] at hi
    rw [Nat.cast_sub (by omega)]
  have hA : (k.factorial : ℤ) * ((n - 1).choose k : ℤ) =
      ((n : ℤ) - k) * ∏ i ∈ Finset.Icc 1 (k - 1), ((n : ℤ) - i) := by
    have h := congr_arg (Nat.cast (R := ℤ)) hA_nat
    push_cast at h
    rw [h, Nat.cast_sub (by omega)]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    simp only [Finset.mem_Icc] at hi
    rw [Nat.cast_sub (by omega)]
  have hB : (k.factorial : ℤ) * ((n + k - 1).choose k : ℤ) =
      (n : ℤ) * ∏ i ∈ Finset.Icc 1 (k - 1), ((n : ℤ) + i) := by
    have h := congr_arg (Nat.cast (R := ℤ)) hB_nat
    push_cast at h
    exact h
  have hprod :
      ((∏ i ∈ Finset.Icc 1 (k - 1), ((n : ℤ) - i)) *
        (∏ i ∈ Finset.Icc 1 (k - 1), ((n : ℤ) + i))) ^ 2 =
        ∏ i ∈ Finset.Icc 1 (k - 1), ((n : ℤ) ^ 2 - (i : ℤ) ^ 2) ^ 2 := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => by ring
  unfold T
  push_cast
  calc
    (k.factorial : ℤ) ^ 4 * ((n.choose k : ℤ) * ((n - 1).choose k : ℤ) * ((n + k - 1).choose k : ℤ) ^ 2)
        = ((k.factorial : ℤ) * (n.choose k : ℤ)) *
          ((k.factorial : ℤ) * ((n - 1).choose k : ℤ)) *
          ((k.factorial : ℤ) * ((n + k - 1).choose k : ℤ)) ^ 2 := by ring
    _ = ((n : ℤ) * ∏ i ∈ Finset.Icc 1 (k - 1), ((n : ℤ) - i)) *
        (((n : ℤ) - k) * ∏ i ∈ Finset.Icc 1 (k - 1), ((n : ℤ) - i)) *
        ((n : ℤ) * ∏ i ∈ Finset.Icc 1 (k - 1), ((n : ℤ) + i)) ^ 2 := by rw [h0, hA, hB]
    _ = (n : ℤ) ^ 3 * ((n : ℤ) - k) *
        (((∏ i ∈ Finset.Icc 1 (k - 1), ((n : ℤ) - i)) *
          (∏ i ∈ Finset.Icc 1 (k - 1), ((n : ℤ) + i))) ^ 2) := by ring
    _ = (n : ℤ) ^ 3 * ((n : ℤ) - k) *
        ∏ i ∈ Finset.Icc 1 (k - 1), ((n : ℤ) ^ 2 - (i : ℤ) ^ 2) ^ 2 := by rw [hprod]

private lemma sum_filter_range_mul_pow {α : Type*} [AddCommMonoid α]
    {p a u : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (g : ℕ → α) :
    ∑ j ∈ (Finset.range (u * p ^ a)).filter (fun j => ¬ p ∣ j), g j =
      ∑ b ∈ Finset.range u, ∑ t ∈ U p a, g (b * p ^ a + t) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij (fun x : ℕ × ℕ => x.1 * p ^ a + x.2) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range, U, Finset.mem_filter] at hx ⊢
    rcases hx with ⟨hx1, hx2_lt, hx2_ndvd⟩
    refine ⟨?_, ?_⟩
    · have h1 : x.1 * p ^ a + p ^ a = (x.1 + 1) * p ^ a := by ring
      have h2 : (x.1 + 1) * p ^ a ≤ u * p ^ a := Nat.mul_le_mul_right (p ^ a) (by omega)
      omega
    · intro hdvd
      have hp_pa : p ∣ x.1 * p ^ a := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) x.1
      exact hx2_ndvd ((Nat.dvd_add_right hp_pa).mp hdvd)
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, U, Finset.mem_filter] at hx hy
    dsimp at hxy
    have hpos : 0 < p ^ a := pow_pos hp.pos a
    have h1 : x.1 = y.1 := by
      have hdiv := congr_arg (fun z => z / p ^ a) hxy
      rw [mul_comm x.1, mul_comm y.1, Nat.mul_add_div hpos, Nat.mul_add_div hpos,
        Nat.div_eq_of_lt hx.2.1, Nat.div_eq_of_lt hy.2.1, add_zero, add_zero] at hdiv
      exact hdiv
    have h2 : x.2 = y.2 := by rw [h1] at hxy; omega
    exact Prod.ext h1 h2
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
    have hpos : 0 < p ^ a := pow_pos hp.pos a
    refine ⟨(j / p ^ a, j % p ^ a), ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, U, Finset.mem_filter]
      refine ⟨?_, Nat.mod_lt j hpos, ?_⟩
      · exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hj.1)
      · intro hdvd
        have hdm : j / p ^ a * p ^ a + j % p ^ a = j := by
          rw [mul_comm]
          exact Nat.div_add_mod j (p ^ a)
        have hp_pa : p ∣ j / p ^ a * p ^ a :=
          dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) (j / p ^ a)
        exact hj.2 (hdm ▸ dvd_add hp_pa hdvd)
    · dsimp
      rw [mul_comm]
      exact Nat.div_add_mod j (p ^ a)
  · intro _ _; rfl

private lemma sum_U_inv_sq_eq_zero {p a : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (ha : 1 ≤ a) :
    ∑ t ∈ U p a, (t : ZMod (p ^ a))⁻¹ ^ 2 = 0 := by
  have : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  have h2_ndvd : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have h3_ndvd : ¬ p ∣ 3 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have h2_unit : IsUnit ((2 : ℕ) : ZMod (p ^ a)) := isUnit_of_not_dvd_pow hp h2_ndvd
  have h3_unit : IsUnit ((3 : ℕ) : ZMod (p ^ a)) := isUnit_of_not_dvd_pow hp h3_ndvd
  let S : ZMod (p ^ a) := ∑ t ∈ U p a, (t : ZMod (p ^ a))⁻¹ ^ 2
  have h2inv : ((2 : ℕ) : ZMod (p ^ a)) * ((2 : ℕ) : ZMod (p ^ a))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ h2_unit
  have h4S : S = ((2 : ℕ) : ZMod (p ^ a)) ^ 2 * S := by
    rw [Finset.mul_sum]
    refine Finset.sum_nbij (fun t => (2 * t) % p ^ a) ?_ ?_ ?_ ?_
    · intro t ht
      simp only [U, Finset.mem_filter, Finset.mem_range] at ht ⊢
      refine ⟨Nat.mod_lt _ (pow_pos hp.pos a), ?_⟩
      intro hdvd
      have hdm : 2 * t / p ^ a * p ^ a + (2 * t) % p ^ a = 2 * t := by
        rw [mul_comm]; exact Nat.div_add_mod (2 * t) (p ^ a)
      have hp_pa : p ∣ 2 * t / p ^ a * p ^ a :=
        dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) _
      have h2t : p ∣ 2 * t := hdm ▸ dvd_add hp_pa hdvd
      rcases hp.dvd_mul.mp h2t with h | h
      · exact h2_ndvd h
      · exact ht.2 h
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, U, Finset.mem_filter, Finset.mem_range] at hx hy
      dsimp at hxy
      have hcast : ((2 : ℕ) : ZMod (p ^ a)) * (x : ZMod (p ^ a)) =
          ((2 : ℕ) : ZMod (p ^ a)) * (y : ZMod (p ^ a)) := by
        have h := congr_arg (Nat.cast (R := ZMod (p ^ a))) hxy
        simpa [ZMod.natCast_mod, Nat.cast_mul] using h
      have hxy_z : (x : ZMod (p ^ a)) = (y : ZMod (p ^ a)) := by
        calc
          (x : ZMod (p ^ a)) = (((2 : ℕ) : ZMod (p ^ a)) * ((2 : ℕ) : ZMod (p ^ a))⁻¹) * (x : ZMod (p ^ a)) := by
            rw [h2inv, one_mul]
          _ = ((2 : ℕ) : ZMod (p ^ a))⁻¹ * (((2 : ℕ) : ZMod (p ^ a)) * (x : ZMod (p ^ a))) := by ring
          _ = ((2 : ℕ) : ZMod (p ^ a))⁻¹ * (((2 : ℕ) : ZMod (p ^ a)) * (y : ZMod (p ^ a))) := by rw [hcast]
          _ = (((2 : ℕ) : ZMod (p ^ a)) * ((2 : ℕ) : ZMod (p ^ a))⁻¹) * (y : ZMod (p ^ a)) := by ring
          _ = (y : ZMod (p ^ a)) := by rw [h2inv, one_mul]
      have hv := congr_arg ZMod.val hxy_z
      rwa [ZMod.val_natCast_of_lt hx.1, ZMod.val_natCast_of_lt hy.1] at hv
    · intro y hy
      simp only [Finset.mem_coe, U, Finset.mem_filter, Finset.mem_range] at hy
      let x : ℕ := (((2 : ℕ) : ZMod (p ^ a))⁻¹ * (y : ZMod (p ^ a))).val
      have h2x_z : ((2 * x : ℕ) : ZMod (p ^ a)) = (y : ZMod (p ^ a)) := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val]
        calc
          ((2 : ℕ) : ZMod (p ^ a)) * (((2 : ℕ) : ZMod (p ^ a))⁻¹ * (y : ZMod (p ^ a)))
              = (((2 : ℕ) : ZMod (p ^ a)) * ((2 : ℕ) : ZMod (p ^ a))⁻¹) * (y : ZMod (p ^ a)) := by ring
          _ = (y : ZMod (p ^ a)) := by rw [h2inv, one_mul]
      have h2x_mod : (2 * x) % p ^ a = y := by
        have hv := congr_arg ZMod.val h2x_z
        rwa [ZMod.val_natCast, ZMod.val_natCast_of_lt hy.1] at hv
      refine ⟨x, ?_, h2x_mod⟩
      simp only [Finset.mem_coe, U, Finset.mem_filter, Finset.mem_range]
      refine ⟨ZMod.val_lt _, ?_⟩
      intro hpx
      have hdm : 2 * x / p ^ a * p ^ a + (2 * x) % p ^ a = 2 * x := by
        rw [mul_comm]; exact Nat.div_add_mod (2 * x) (p ^ a)
      have hp_pa : p ∣ 2 * x / p ^ a * p ^ a :=
        dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) _
      have hp_2x : p ∣ 2 * x := dvd_mul_of_dvd_right hpx 2
      rw [← hdm, h2x_mod] at hp_2x
      exact hy.2 ((Nat.dvd_add_right hp_pa).mp hp_2x)
    · intro t ht
      simp only [U, Finset.mem_filter] at ht
      have hcast : (((2 * t) % p ^ a : ℕ) : ZMod (p ^ a)) =
          ((2 : ℕ) : ZMod (p ^ a)) * (t : ZMod (p ^ a)) := by
        rw [ZMod.natCast_mod, Nat.cast_mul]
      rw [hcast, zmod_mul_inv_of_isUnit h2_unit (isUnit_of_not_dvd_pow hp ht.2), mul_pow]
      calc
        (t : ZMod (p ^ a))⁻¹ ^ 2
            = (((2 : ℕ) : ZMod (p ^ a)) * ((2 : ℕ) : ZMod (p ^ a))⁻¹) ^ 2 * (t : ZMod (p ^ a))⁻¹ ^ 2 := by
              rw [h2inv, one_pow, one_mul]
        _ = ((2 : ℕ) : ZMod (p ^ a)) ^ 2 * (((2 : ℕ) : ZMod (p ^ a))⁻¹ ^ 2 * (t : ZMod (p ^ a))⁻¹ ^ 2) := by
              ring
  have h3S : ((3 : ℕ) : ZMod (p ^ a)) * S = 0 := by
    have h2 : ((2 : ℕ) : ZMod (p ^ a)) ^ 2 - 1 = ((3 : ℕ) : ZMod (p ^ a)) := by
      push_cast; ring
    rw [← h2]
    linear_combination -h4S
  have h3inv : ((3 : ℕ) : ZMod (p ^ a)) * ((3 : ℕ) : ZMod (p ^ a))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ h3_unit
  calc
    S = (((3 : ℕ) : ZMod (p ^ a)) * ((3 : ℕ) : ZMod (p ^ a))⁻¹) * S := by rw [h3inv, one_mul]
    _ = ((3 : ℕ) : ZMod (p ^ a))⁻¹ * (((3 : ℕ) : ZMod (p ^ a)) * S) := by ring
    _ = 0 := by rw [h3S, mul_zero]

private lemma sum_U_inv_cube_eq_zero_zmod_p {p a : ℕ} (hp : p.Prime) (hp_ne2 : p ≠ 2) (ha : 1 ≤ a) :
    ∑ t ∈ U p a, (t : ZMod p)⁻¹ ^ 3 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  let S : ZMod p := ∑ t ∈ U p a, (t : ZMod p)⁻¹ ^ 3
  have hS_neg : S = -S := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_nbij (fun t => p ^ a - t) ?_ ?_ ?_ ?_
    · intro t ht
      simp only [U, Finset.mem_filter, Finset.mem_range] at ht ⊢
      have ht_pos : 0 < t := Nat.pos_of_ne_zero fun h0 => ht.2 (h0 ▸ dvd_zero p)
      refine ⟨by omega, ?_⟩
      intro hdvd
      have hpa : p ∣ p ^ a := dvd_pow_self p (by omega)
      have hsum : (p ^ a - t) + t = p ^ a := by omega
      exact ht.2 ((Nat.dvd_add_right hdvd).mp (hsum.symm ▸ hpa))
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, U, Finset.mem_filter, Finset.mem_range] at hx hy
      dsimp at hxy
      omega
    · intro y hy
      simp only [Finset.mem_coe, U, Finset.mem_filter, Finset.mem_range] at hy
      have hy_pos : 0 < y := Nat.pos_of_ne_zero fun h0 => hy.2 (h0 ▸ dvd_zero p)
      refine ⟨p ^ a - y, ?_, by dsimp; omega⟩
      simp only [Finset.mem_coe, U, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      intro hdvd
      have hpa : p ∣ p ^ a := dvd_pow_self p (by omega)
      have hsum : (p ^ a - y) + y = p ^ a := by omega
      exact hy.2 ((Nat.dvd_add_right hdvd).mp (hsum.symm ▸ hpa))
    · intro t ht
      simp only [U, Finset.mem_filter, Finset.mem_range] at ht
      have hpa0 : ((p ^ a : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_pow, ZMod.natCast_self, zero_pow (by omega)]
      have hcast : ((p ^ a - t : ℕ) : ZMod p) = -(t : ZMod p) := by
        rw [Nat.cast_sub (by omega : t ≤ p ^ a), hpa0, zero_sub]
      rw [hcast, inv_neg]
      ring
  have h2S : (2 : ZMod p) * S = 0 := by linear_combination hS_neg
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0)
    have : p = 2 := ((Nat.dvd_prime Nat.prime_two).mp hdvd).resolve_left hp.ne_one
    exact hp_ne2 this
  exact (mul_eq_zero.mp h2S).resolve_left h2ne

private lemma sum_U_inv_pow4_eq_zero_zmod_p {p r : ℕ} (hp : p.Prime) (hr2 : 2 ≤ r) :
    ∑ k ∈ U p r, (k : ZMod p)⁻¹ ^ 4 = 0 := by
  have hpow : p ^ r = p ^ (r - 1) * p ^ 1 := by
    rw [pow_one, ← pow_succ, Nat.sub_add_cancel (by omega)]
  have hsplit :
      ∑ k ∈ U p r, (k : ZMod p)⁻¹ ^ 4 =
        ∑ b ∈ Finset.range (p ^ (r - 1)), ∑ t ∈ U p 1, ((b * p ^ 1 + t : ℕ) : ZMod p)⁻¹ ^ 4 := by
    have hU : U p r = (Finset.range (p ^ (r - 1) * p ^ 1)).filter (fun k => ¬ p ∣ k) := by
      simp only [U, hpow]
    rw [hU]
    exact sum_filter_range_mul_pow hp (by omega) (fun k => (k : ZMod p)⁻¹ ^ 4)
  rw [hsplit]
  have hinner :
      ∀ b ∈ Finset.range (p ^ (r - 1)),
        ∑ t ∈ U p 1, ((b * p ^ 1 + t : ℕ) : ZMod p)⁻¹ ^ 4 =
          ∑ t ∈ U p 1, (t : ZMod p)⁻¹ ^ 4 := by
    intro b _
    refine Finset.sum_congr rfl fun t _ => ?_
    simp
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hpr0 : ((p ^ (r - 1) : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_pow, ZMod.natCast_self, zero_pow (by omega)]
  rw [hpr0, zero_mul]

private lemma sum_U_inv_cube_eq_zero_zmod_p3 {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr2 : 2 ≤ r) :
    ∑ k ∈ U p r, (k : ZMod (p ^ 3))⁻¹ ^ 3 = 0 := by
  let S : ZMod (p ^ 3) := ∑ k ∈ U p r, (k : ZMod (p ^ 3))⁻¹ ^ 3
  have h2_ndvd : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have h2inv : ((2 : ℕ) : ZMod (p ^ 3)) * ((2 : ℕ) : ZMod (p ^ 3))⁻¹ = 1 :=
    mul_inv_of_not_dvd_pow hp h2_ndvd
  have hrev : S = ∑ k ∈ U p r, ((p ^ r - k : ℕ) : ZMod (p ^ 3))⁻¹ ^ 3 := by
    refine Finset.sum_nbij (fun k => p ^ r - k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [U, Finset.mem_filter, Finset.mem_range] at hk ⊢
      have hk_pos : 0 < k := Nat.pos_of_ne_zero fun h0 => hk.2 (h0 ▸ dvd_zero p)
      refine ⟨by omega, ?_⟩
      intro hdvd
      have hpr : p ∣ p ^ r := dvd_pow_self p (by omega)
      have hsum : (p ^ r - k) + k = p ^ r := by omega
      exact hk.2 ((Nat.dvd_add_right hdvd).mp (hsum.symm ▸ hpr))
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, U, Finset.mem_filter, Finset.mem_range] at hx hy
      dsimp at hxy
      omega
    · intro y hy
      simp only [Finset.mem_coe, U, Finset.mem_filter, Finset.mem_range] at hy
      have hy_pos : 0 < y := Nat.pos_of_ne_zero fun h0 => hy.2 (h0 ▸ dvd_zero p)
      refine ⟨p ^ r - y, ?_, by dsimp; omega⟩
      simp only [Finset.mem_coe, U, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      intro hdvd
      have hpr : p ∣ p ^ r := dvd_pow_self p (by omega)
      have hsum : (p ^ r - y) + y = p ^ r := by omega
      exact hy.2 ((Nat.dvd_add_right hdvd).mp (hsum.symm ▸ hpr))
    · intro k hk
      simp only [U, Finset.mem_filter, Finset.mem_range] at hk
      have hsub : p ^ r - (p ^ r - k) = k := by omega
      rw [hsub]
  have h2S : 2 * S = 0 := by
    by_cases hr3 : 3 ≤ r
    · have hpr0 : ((p ^ r : ℕ) : ZMod (p ^ 3)) = 0 := by
        rw [Nat.cast_pow]; exact zmod_pow_eq_zero_of_ge hr3
      have hS_neg : S = -S := by
        conv_lhs => rw [hrev]
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k hk => ?_
        simp only [U, Finset.mem_filter, Finset.mem_range] at hk
        have hcast : ((p ^ r - k : ℕ) : ZMod (p ^ 3)) = -(k : ZMod (p ^ 3)) := by
          rw [Nat.cast_sub (by omega : k ≤ p ^ r), hpr0, zero_sub]
        rw [hcast, zmod_neg_inv_of_isUnit (isUnit_of_not_dvd_pow hp hk.2)]
        ring
      linear_combination hS_neg
    · have hr_eq : r = 2 := by omega
      subst hr_eq
      have hp4 : (p : ZMod (p ^ 3)) ^ 4 = 0 := zmod_pow_eq_zero_of_ge (by omega)
      have hpair :
          ∀ k ∈ U p 2,
            (k : ZMod (p ^ 3))⁻¹ ^ 3 + ((p ^ 2 - k : ℕ) : ZMod (p ^ 3))⁻¹ ^ 3 =
              -3 * ((p : ZMod (p ^ 3)) ^ 2 * (k : ZMod (p ^ 3))⁻¹ ^ 4) := by
        intro k hk
        simp only [U, Finset.mem_filter, Finset.mem_range] at hk
        have hk_pos : 0 < k := Nat.pos_of_ne_zero fun h0 => hk.2 (h0 ▸ dvd_zero p)
        have hpk_ndvd : ¬ p ∣ p ^ 2 - k := by
          intro hdvd
          have hp2 : p ∣ p ^ 2 := dvd_pow_self p (by norm_num)
          have hsum : (p ^ 2 - k) + k = p ^ 2 := by omega
          exact hk.2 ((Nat.dvd_add_right hdvd).mp (hsum.symm ▸ hp2))
        set u : ZMod (p ^ 3) := (k : ZMod (p ^ 3))
        set v : ZMod (p ^ 3) := ((p ^ 2 - k : ℕ) : ZMod (p ^ 3))
        have hu : u * u⁻¹ = 1 := mul_inv_of_not_dvd_pow hp hk.2
        have hv_unit : IsUnit v := isUnit_of_not_dvd_pow hp hpk_ndvd
        have hv_eq : v = (p : ZMod (p ^ 3)) ^ 2 - u := by
          simp only [u, v, Nat.cast_sub (by omega : k ≤ p ^ 2), Nat.cast_pow]
        have hvinv : v⁻¹ = (-u⁻¹) * (1 + (p : ZMod (p ^ 3)) ^ 2 * u⁻¹) := by
          refine zmod_inv_unique hv_unit ?_
          rw [hv_eq]
          linear_combination (1 + (p : ZMod (p ^ 3)) ^ 2 * u⁻¹) * hu - u⁻¹ ^ 2 * hp4
        rw [hvinv]
        linear_combination
          (-3 * u⁻¹ ^ 5 - (p : ZMod (p ^ 3)) ^ 2 * u⁻¹ ^ 6) * hp4
      have hsum_pair :
          2 * S = -3 * (((p ^ 2 : ℕ) : ZMod (p ^ 3)) *
            ∑ k ∈ U p 2, (k : ZMod (p ^ 3))⁻¹ ^ 4) := by
        calc
          2 * S = S + S := by ring
          _ = ∑ k ∈ U p 2,
                ((k : ZMod (p ^ 3))⁻¹ ^ 3 + ((p ^ 2 - k : ℕ) : ZMod (p ^ 3))⁻¹ ^ 3) := by
            conv_lhs => rhs; rw [hrev]
            rw [← Finset.sum_add_distrib]
          _ = ∑ k ∈ U p 2,
                (-3 * ((p : ZMod (p ^ 3)) ^ 2 * (k : ZMod (p ^ 3))⁻¹ ^ 4)) :=
            Finset.sum_congr rfl hpair
          _ = -3 * (((p ^ 2 : ℕ) : ZMod (p ^ 3)) *
                ∑ k ∈ U p 2, (k : ZMod (p ^ 3))⁻¹ ^ 4) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => by push_cast; ring
      have hcast_zero :
          ZMod.castHom (dvd_pow_self p (by norm_num : (3 : ℕ) ≠ 0)) (ZMod p)
            (∑ k ∈ U p 2, (k : ZMod (p ^ 3))⁻¹ ^ 4) = 0 := by
        rw [map_sum]
        have hcongr :
            ∑ k ∈ U p 2,
              ZMod.castHom (dvd_pow_self p (by norm_num : (3 : ℕ) ≠ 0)) (ZMod p)
                ((k : ZMod (p ^ 3))⁻¹ ^ 4) =
              ∑ k ∈ U p 2, (k : ZMod p)⁻¹ ^ 4 := by
          refine Finset.sum_congr rfl fun k hk => ?_
          simp only [U, Finset.mem_filter] at hk
          rw [map_pow, castHom_inv_of_isUnit _ _ (isUnit_of_not_dvd_pow hp hk.2), map_natCast]
        rw [hcongr]
        exact sum_U_inv_pow4_eq_zero_zmod_p hp (by omega)
      have hzero := mul_eq_zero_of_dvd_of_castHom_p_eq_zero (p := p) (N := 3) (c := p ^ 2)
        hp.pos (by omega) (dvd_refl _) _ hcast_zero
      rw [hsum_pair, hzero, mul_zero]
  calc
    S = (((2 : ℕ) : ZMod (p ^ 3)) * ((2 : ℕ) : ZMod (p ^ 3))⁻¹) * S := by rw [h2inv, one_mul]
    _ = ((2 : ℕ) : ZMod (p ^ 3))⁻¹ * (2 * S) := by push_cast; ring
    _ = 0 := by rw [h2S, mul_zero]

private lemma sum_block_inv_sq_zmod_pr {p r u : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr2 : 2 ≤ r) :
    ∑ j ∈ (Finset.range (u * p ^ (r - 1))).filter (fun j => ¬ p ∣ j), (j : ZMod (p ^ r))⁻¹ ^ 2 =
      (u : ZMod (p ^ r)) * ∑ t ∈ U p (r - 1), (t : ZMod (p ^ r))⁻¹ ^ 2 := by
  rw [sum_filter_range_mul_pow hp (by omega : 1 ≤ r - 1)]
  have hP2 : ((p : ZMod (p ^ r)) ^ (r - 1)) ^ 2 = 0 := by
    rw [← pow_mul]
    exact zmod_pow_eq_zero_of_ge (by omega)
  have hblock :
      ∀ b ∈ Finset.range u,
        ∑ t ∈ U p (r - 1), ((b * p ^ (r - 1) + t : ℕ) : ZMod (p ^ r))⁻¹ ^ 2 =
          ∑ t ∈ U p (r - 1), (t : ZMod (p ^ r))⁻¹ ^ 2 := by
    intro b _
    have hterm :
        ∀ t ∈ U p (r - 1),
          ((b * p ^ (r - 1) + t : ℕ) : ZMod (p ^ r))⁻¹ ^ 2 =
            (t : ZMod (p ^ r))⁻¹ ^ 2 -
              2 * (b : ZMod (p ^ r)) * (p : ZMod (p ^ r)) ^ (r - 1) * (t : ZMod (p ^ r))⁻¹ ^ 3 := by
      intro t ht
      simp only [U, Finset.mem_filter] at ht
      have hndvd : ¬ p ∣ b * p ^ (r - 1) + t := by
        intro hdvd
        have hp_pa : p ∣ b * p ^ (r - 1) :=
          dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) b
        exact ht.2 ((Nat.dvd_add_right hp_pa).mp hdvd)
      set P : ZMod (p ^ r) := (p : ZMod (p ^ r)) ^ (r - 1)
      set v : ZMod (p ^ r) := (t : ZMod (p ^ r))
      have hv : v * v⁻¹ = 1 := mul_inv_of_not_dvd_pow hp ht.2
      have hw_unit : IsUnit ((b * p ^ (r - 1) + t : ℕ) : ZMod (p ^ r)) :=
        isUnit_of_not_dvd_pow hp hndvd
      have hw_eq : ((b * p ^ (r - 1) + t : ℕ) : ZMod (p ^ r)) = (b : ZMod (p ^ r)) * P + v := by
        simp only [P, v]; push_cast; rfl
      have hwinv :
          ((b * p ^ (r - 1) + t : ℕ) : ZMod (p ^ r))⁻¹ =
            v⁻¹ * (1 - (b : ZMod (p ^ r)) * P * v⁻¹) := by
        refine zmod_inv_unique hw_unit ?_
        rw [hw_eq]
        linear_combination (1 - (b : ZMod (p ^ r)) * P * v⁻¹) * hv -
          (b : ZMod (p ^ r)) ^ 2 * v⁻¹ ^ 2 * hP2
      rw [hwinv]
      linear_combination (b : ZMod (p ^ r)) ^ 2 * v⁻¹ ^ 4 * hP2
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
    have htail :
        ∑ t ∈ U p (r - 1),
            2 * (b : ZMod (p ^ r)) * (p : ZMod (p ^ r)) ^ (r - 1) * (t : ZMod (p ^ r))⁻¹ ^ 3 = 0 := by
      have hfac :
          ∑ t ∈ U p (r - 1),
              2 * (b : ZMod (p ^ r)) * (p : ZMod (p ^ r)) ^ (r - 1) * (t : ZMod (p ^ r))⁻¹ ^ 3 =
            2 * (b : ZMod (p ^ r)) *
              (((p ^ (r - 1) : ℕ) : ZMod (p ^ r)) *
                ∑ t ∈ U p (r - 1), (t : ZMod (p ^ r))⁻¹ ^ 3) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => by push_cast; ring
      rw [hfac]
      have hcast_zero :
          ZMod.castHom (dvd_pow_self p (by omega : r ≠ 0)) (ZMod p)
            (∑ t ∈ U p (r - 1), (t : ZMod (p ^ r))⁻¹ ^ 3) = 0 := by
        rw [map_sum]
        have hcongr :
            ∑ t ∈ U p (r - 1),
              ZMod.castHom (dvd_pow_self p (by omega : r ≠ 0)) (ZMod p)
                ((t : ZMod (p ^ r))⁻¹ ^ 3) =
              ∑ t ∈ U p (r - 1), (t : ZMod p)⁻¹ ^ 3 := by
          refine Finset.sum_congr rfl fun t ht => ?_
          simp only [U, Finset.mem_filter] at ht
          rw [map_pow, castHom_inv_of_isUnit _ _ (isUnit_of_not_dvd_pow hp ht.2), map_natCast]
        rw [hcongr]
        exact sum_U_inv_cube_eq_zero_zmod_p hp (by omega) (by omega)
      have hz := mul_eq_zero_of_dvd_of_castHom_p_eq_zero (p := p) (N := r) (c := p ^ (r - 1))
        hp.pos (by omega) (dvd_refl _) _ hcast_zero
      rw [hz, mul_zero]
    rw [htail, sub_zero]
  rw [Finset.sum_congr rfl hblock, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

private lemma reduced_term_int {p d m : ℕ} (hp : p.Prime) (_hd : 1 ≤ d)
    (hm1 : 1 ≤ m) (hmd : m < p ^ d) :
    let s := m.factorization p
    let u := m / p ^ s
    let W : ℕ := u ^ 4 * ∏ j ∈ Finset.Icc 1 (m - 1), (j / p ^ (j.factorization p)) ^ 4
    (W : ℤ) * (T (p ^ d) m : ℤ) =
      (p : ℤ) ^ (3 * (d - s)) * ((p : ℤ) ^ (d - s) - u) *
        ∏ j ∈ Finset.Icc 1 (m - 1),
          ((p : ℤ) ^ (2 * (d - j.factorization p)) - ((j / p ^ (j.factorization p) : ℕ) : ℤ) ^ 2) ^ 2 := by
  intro s u W
  have hs_dvd : p ^ s ∣ m := Nat.ordProj_dvd m p
  have hs_lt : s < d := by
    have hle : p ^ s ≤ m := Nat.le_of_dvd (by omega) hs_dvd
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp (lt_of_le_of_lt hle hmd)
  have hm_eq : m = p ^ s * u := (Nat.mul_div_cancel' hs_dvd).symm
  have hmain := term_prod_int (n := p ^ d) (k := m) hm1 (by omega)
  have hfac_m : (m.factorial : ℤ) = (m : ℤ) * ((m - 1).factorial : ℤ) := by
    have hnat : m.factorial = m * (m - 1).factorial := by
      cases m with
      | zero => omega
      | succ j => exact Nat.factorial_succ j
    rw [hnat, Nat.cast_mul]
  have hfac_prod : ((m - 1).factorial : ℤ) = ∏ j ∈ Finset.Icc 1 (m - 1), (j : ℤ) := by
    rw [← prod_Icc_eq_factorial (m - 1), Nat.cast_prod]
  let P : ℤ := ∏ j ∈ Finset.Icc 1 (m - 1), ((p : ℤ) ^ (j.factorization p)) ^ 4
  have hP_pos : 0 < P :=
    Finset.prod_pos fun j _ => pow_pos (pow_pos (by exact_mod_cast hp.pos) _) 4
  have hLHS_fac :
      ((m - 1).factorial : ℤ) ^ 4 =
        P * ∏ j ∈ Finset.Icc 1 (m - 1), ((j / p ^ (j.factorization p) : ℕ) : ℤ) ^ 4 := by
    rw [hfac_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj_eq : j = p ^ (j.factorization p) * (j / p ^ (j.factorization p)) :=
      (Nat.mul_div_cancel' (Nat.ordProj_dvd j p)).symm
    conv_lhs => rw [hj_eq]
    push_cast
    ring
  have hRHS_prod :
      ∏ j ∈ Finset.Icc 1 (m - 1), (((p ^ d : ℕ) : ℤ) ^ 2 - (j : ℤ) ^ 2) ^ 2 =
        P * ∏ j ∈ Finset.Icc 1 (m - 1),
          ((p : ℤ) ^ (2 * (d - j.factorization p)) - ((j / p ^ (j.factorization p) : ℕ) : ℤ) ^ 2) ^ 2 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    simp only [Finset.mem_Icc] at hj
    have hj_dvd : p ^ (j.factorization p) ∣ j := Nat.ordProj_dvd j p
    have hj_lt : j.factorization p < d := by
      have hle : p ^ (j.factorization p) ≤ j := Nat.le_of_dvd (by omega) hj_dvd
      exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp (lt_of_le_of_lt hle (by omega))
    have hj_eq : (j : ℤ) = (p : ℤ) ^ (j.factorization p) * ((j / p ^ (j.factorization p) : ℕ) : ℤ) := by
      exact_mod_cast (Nat.mul_div_cancel' hj_dvd).symm
    have hp_split :
        ((p ^ d : ℕ) : ℤ) ^ 2 =
          ((p : ℤ) ^ (j.factorization p)) ^ 2 * (p : ℤ) ^ (2 * (d - j.factorization p)) := by
      push_cast
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      omega
    rw [hp_split, hj_eq]
    ring
  have hpd_sub :
      ((p ^ d : ℕ) : ℤ) - (m : ℤ) = (p : ℤ) ^ s * ((p : ℤ) ^ (d - s) - (u : ℤ)) := by
    have hpd : ((p ^ d : ℕ) : ℤ) = (p : ℤ) ^ s * (p : ℤ) ^ (d - s) := by
      push_cast
      rw [← pow_add, Nat.add_sub_cancel' (by omega)]
    have hm_z : (m : ℤ) = (p : ℤ) ^ s * (u : ℤ) := by exact_mod_cast hm_eq
    rw [hpd, hm_z]
    ring
  have hcancel_pos : 0 < P * (p : ℤ) ^ (4 * s) :=
    mul_pos hP_pos (pow_pos (by exact_mod_cast hp.pos) _)
  apply mul_left_cancel₀ (ne_of_gt hcancel_pos)
  have hW_cast :
      (W : ℤ) = (u : ℤ) ^ 4 * ∏ j ∈ Finset.Icc 1 (m - 1), ((j / p ^ (j.factorization p) : ℕ) : ℤ) ^ 4 := by
    simp only [W]
    push_cast
    rfl
  have hm_z : (m : ℤ) = (p : ℤ) ^ s * (u : ℤ) := by exact_mod_cast hm_eq
  have hpow3 :
      ((p ^ d : ℕ) : ℤ) ^ 3 * (p : ℤ) ^ s = (p : ℤ) ^ (4 * s) * (p : ℤ) ^ (3 * (d - s)) := by
    push_cast
    rw [← pow_mul, ← pow_add, ← pow_add]
    congr 1
    omega
  calc
    P * (p : ℤ) ^ (4 * s) * ((W : ℤ) * (T (p ^ d) m : ℤ))
        = (((p : ℤ) ^ s * (u : ℤ)) ^ 4 *
            (P * ∏ j ∈ Finset.Icc 1 (m - 1), ((j / p ^ (j.factorization p) : ℕ) : ℤ) ^ 4)) *
            (T (p ^ d) m : ℤ) := by rw [hW_cast]; ring
    _ = ((m : ℤ) * ((m - 1).factorial : ℤ)) ^ 4 * (T (p ^ d) m : ℤ) := by
          rw [← hLHS_fac, ← hm_z]; ring
    _ = ((m.factorial : ℤ) ^ 4) * (T (p ^ d) m : ℤ) := by rw [← hfac_m]
    _ = ((p ^ d : ℕ) : ℤ) ^ 3 * (((p ^ d : ℕ) : ℤ) - m) *
          ∏ j ∈ Finset.Icc 1 (m - 1), (((p ^ d : ℕ) : ℤ) ^ 2 - (j : ℤ) ^ 2) ^ 2 := hmain
    _ = ((p ^ d : ℕ) : ℤ) ^ 3 * ((p : ℤ) ^ s * ((p : ℤ) ^ (d - s) - u)) *
          (P * ∏ j ∈ Finset.Icc 1 (m - 1),
            ((p : ℤ) ^ (2 * (d - j.factorization p)) - ((j / p ^ (j.factorization p) : ℕ) : ℤ) ^ 2) ^ 2) := by
          rw [hpd_sub, hRHS_prod]
    _ = P * (((p ^ d : ℕ) : ℤ) ^ 3 * (p : ℤ) ^ s) * ((p : ℤ) ^ (d - s) - u) *
          ∏ j ∈ Finset.Icc 1 (m - 1),
            ((p : ℤ) ^ (2 * (d - j.factorization p)) - ((j / p ^ (j.factorization p) : ℕ) : ℤ) ^ 2) ^ 2 := by
          ring
    _ = P * (p : ℤ) ^ (4 * s) *
          ((p : ℤ) ^ (3 * (d - s)) * ((p : ℤ) ^ (d - s) - u) *
            ∏ j ∈ Finset.Icc 1 (m - 1),
              ((p : ℤ) ^ (2 * (d - j.factorization p)) - ((j / p ^ (j.factorization p) : ℕ) : ℤ) ^ 2) ^ 2) := by
          rw [hpow3]; ring

private lemma not_dvd_reduced_W {p m : ℕ} (hp : p.Prime) (hm1 : 1 ≤ m) :
    ¬ p ∣ (m / p ^ (m.factorization p)) ^ 4 *
      ∏ j ∈ Finset.Icc 1 (m - 1), (j / p ^ (j.factorization p)) ^ 4 := by
  have hu : ¬ p ∣ m / p ^ (m.factorization p) := Nat.not_dvd_ordCompl hp (by omega)
  have hprod : ¬ p ∣ ∏ j ∈ Finset.Icc 1 (m - 1), (j / p ^ (j.factorization p)) ^ 4 := by
    intro hdvd
    rw [Prime.dvd_finsetProd_iff hp.prime] at hdvd
    obtain ⟨j, hj, hjd⟩ := hdvd
    simp only [Finset.mem_Icc] at hj
    exact Nat.not_dvd_ordCompl hp (by omega) (hp.dvd_of_dvd_pow hjd)
  intro hdvd
  rcases hp.dvd_mul.mp hdvd with h | h
  · exact hu (hp.dvd_of_dvd_pow h)
  · exact hprod h

private lemma pow_dvd_T {p d m : ℕ} (hp : p.Prime) (hd : 1 ≤ d)
    (hm1 : 1 ≤ m) (hmd : m < p ^ d) :
    p ^ (3 * (d - m.factorization p)) ∣ T (p ^ d) m := by
  let s := m.factorization p
  let W : ℕ := (m / p ^ s) ^ 4 * ∏ j ∈ Finset.Icc 1 (m - 1), (j / p ^ (j.factorization p)) ^ 4
  have hid := reduced_term_int hp hd hm1 hmd
  have hdvd_int : ((p ^ (3 * (d - s)) : ℕ) : ℤ) ∣ ((W * T (p ^ d) m : ℕ) : ℤ) := by
    refine ⟨((p : ℤ) ^ (d - s) - (m / p ^ s : ℕ)) *
      ∏ j ∈ Finset.Icc 1 (m - 1),
        ((p : ℤ) ^ (2 * (d - j.factorization p)) - ((j / p ^ (j.factorization p) : ℕ) : ℤ) ^ 2) ^ 2, ?_⟩
    rw [Nat.cast_mul, Nat.cast_pow, ← mul_assoc]
    exact hid
  have hdvd_nat : p ^ (3 * (d - s)) ∣ W * T (p ^ d) m := Int.ofNat_dvd.mp hdvd_int
  have hcop : (p ^ (3 * (d - s))).Coprime W :=
    (hp.coprime_iff_not_dvd.mpr (not_dvd_reduced_W hp hm1)).pow_left _
  exact hcop.dvd_of_dvd_mul_left hdvd_nat

private lemma theoremA_term_zmod_p3 {p r k : ℕ} (hp : p.Prime) (hr2 : 2 ≤ r) (hk : k ∈ U p r) :
    ((T (p ^ r) k / p ^ (3 * r) : ℕ) : ZMod (p ^ 3)) =
      (p : ZMod (p ^ 3)) ^ r * (k : ZMod (p ^ 3))⁻¹ ^ 4 -
        (k : ZMod (p ^ 3))⁻¹ ^ 3 +
        2 * (p : ZMod (p ^ 3)) ^ 2 * (k : ZMod (p ^ 3))⁻¹ ^ 3 *
          ∑ u ∈ Finset.Icc 1 (k / p ^ (r - 1)), (u : ZMod (p ^ 3))⁻¹ ^ 2 := by
  simp only [U, Finset.mem_filter, Finset.mem_range] at hk
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun h0 => hk.2 (h0 ▸ dvd_zero p)
  have hs0 : k.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hk.2
  have hdvd : p ^ (3 * r) ∣ T (p ^ r) k := by
    have h := pow_dvd_T hp (by omega) hk1 hk.1
    simpa [hs0] using h
  have hid := reduced_term_int hp (by omega : 1 ≤ r) hk1 hk.1
  simp only [hs0, pow_zero, Nat.div_one, Nat.sub_zero] at hid
  let W_prod : ℕ := ∏ j ∈ Finset.Icc 1 (k - 1), (j / p ^ (j.factorization p)) ^ 4
  have hdiv_int :
      (((k ^ 4 * W_prod : ℕ) : ℤ)) * ((T (p ^ r) k / p ^ (3 * r) : ℕ) : ℤ) =
        ((p : ℤ) ^ r - (k : ℤ)) *
          ∏ j ∈ Finset.Icc 1 (k - 1),
            ((p : ℤ) ^ (2 * (r - j.factorization p)) - ((j / p ^ (j.factorization p) : ℕ) : ℤ) ^ 2) ^ 2 := by
    have hp3r_pos : (0 : ℤ) < (p : ℤ) ^ (3 * r) := pow_pos (by exact_mod_cast hp.pos) _
    apply mul_left_cancel₀ (ne_of_gt hp3r_pos)
    have hT_eq : (p : ℤ) ^ (3 * r) * ((T (p ^ r) k / p ^ (3 * r) : ℕ) : ℤ) = (T (p ^ r) k : ℤ) := by
      exact_mod_cast Nat.mul_div_cancel' hdvd
    calc
      (p : ℤ) ^ (3 * r) * (((k ^ 4 * W_prod : ℕ) : ℤ) * ((T (p ^ r) k / p ^ (3 * r) : ℕ) : ℤ))
          = ((k ^ 4 * W_prod : ℕ) : ℤ) * ((p : ℤ) ^ (3 * r) * ((T (p ^ r) k / p ^ (3 * r) : ℕ) : ℤ)) := by ring
      _ = ((k ^ 4 * W_prod : ℕ) : ℤ) * (T (p ^ r) k : ℤ) := by rw [hT_eq]
      _ = (p : ℤ) ^ (3 * r) * ((p : ℤ) ^ r - k) *
            ∏ j ∈ Finset.Icc 1 (k - 1),
              ((p : ℤ) ^ (2 * (r - j.factorization p)) - ((j / p ^ (j.factorization p) : ℕ) : ℤ) ^ 2) ^ 2 := hid
      _ = (p : ℤ) ^ (3 * r) * (((p : ℤ) ^ r - k) *
            ∏ j ∈ Finset.Icc 1 (k - 1),
              ((p : ℤ) ^ (2 * (r - j.factorization p)) - ((j / p ^ (j.factorization p) : ℕ) : ℤ) ^ 2) ^ 2) := by
            ring
  have hcast := congr_arg (Int.cast (R := ZMod (p ^ 3))) hdiv_int
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_prod, Int.cast_natCast,
    Nat.cast_mul, Nat.cast_pow] at hcast
  have hprod_eval :
      ∏ j ∈ Finset.Icc 1 (k - 1),
          ((p : ZMod (p ^ 3)) ^ (2 * (r - j.factorization p)) -
            ((j / p ^ (j.factorization p) : ℕ) : ZMod (p ^ 3)) ^ 2) ^ 2 =
        (W_prod : ZMod (p ^ 3)) *
          (1 - 2 * (p : ZMod (p ^ 3)) ^ 2 *
            ∑ u ∈ Finset.Icc 1 (k / p ^ (r - 1)), (u : ZMod (p ^ 3))⁻¹ ^ 2) := by
    have hsplit_RHS := (Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (k - 1))
      (fun j => p ^ (r - 1) ∣ j)
      (fun j => ((p : ZMod (p ^ 3)) ^ (2 * (r - j.factorization p)) -
        ((j / p ^ (j.factorization p) : ℕ) : ZMod (p ^ 3)) ^ 2) ^ 2)).symm
    have hsplit_W :
        (W_prod : ZMod (p ^ 3)) =
          (∏ j ∈ (Finset.Icc 1 (k - 1)).filter (fun j => p ^ (r - 1) ∣ j),
              ((j / p ^ (j.factorization p) : ℕ) : ZMod (p ^ 3)) ^ 4) *
            (∏ j ∈ (Finset.Icc 1 (k - 1)).filter (fun j => ¬ p ^ (r - 1) ∣ j),
              ((j / p ^ (j.factorization p) : ℕ) : ZMod (p ^ 3)) ^ 4) := by
      simp only [W_prod, Nat.cast_prod, Nat.cast_pow]
      exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
    have hnot_part :
        ∏ j ∈ (Finset.Icc 1 (k - 1)).filter (fun j => ¬ p ^ (r - 1) ∣ j),
            ((p : ZMod (p ^ 3)) ^ (2 * (r - j.factorization p)) -
              ((j / p ^ (j.factorization p) : ℕ) : ZMod (p ^ 3)) ^ 2) ^ 2 =
          ∏ j ∈ (Finset.Icc 1 (k - 1)).filter (fun j => ¬ p ^ (r - 1) ∣ j),
            ((j / p ^ (j.factorization p) : ℕ) : ZMod (p ^ 3)) ^ 4 := by
      refine Finset.prod_congr rfl fun j hj => ?_
      simp only [Finset.mem_filter, Finset.mem_Icc] at hj
      have hv_lt : j.factorization p < r - 1 := by
        by_contra hge
        have hdvd_j : p ^ (r - 1) ∣ j :=
          (hp.pow_dvd_iff_le_factorization (by omega)).mpr (by omega)
        exact hj.2 hdvd_j
      have hp0 : (p : ZMod (p ^ 3)) ^ (2 * (r - j.factorization p)) = 0 :=
        zmod_pow_eq_zero_of_ge (by omega)
      rw [hp0]
      ring
    have hbij_div :
        ∀ (F : ℕ → ZMod (p ^ 3)),
          ∏ j ∈ (Finset.Icc 1 (k - 1)).filter (fun j => p ^ (r - 1) ∣ j), F j =
            ∏ u ∈ Finset.Icc 1 (k / p ^ (r - 1)), F (u * p ^ (r - 1)) := by
      intro F
      symm
      refine Finset.prod_nbij (fun u => u * p ^ (r - 1)) ?_ ?_ ?_ ?_
      · intro u hu
        simp only [Finset.mem_Icc, Finset.mem_filter] at hu ⊢
        have hpos : 0 < p ^ (r - 1) := pow_pos hp.pos _
        have hle : u * p ^ (r - 1) ≤ k :=
          le_trans (Nat.mul_le_mul_right _ hu.2) (Nat.div_mul_le_self k _)
        have hne : u * p ^ (r - 1) ≠ k := by
          intro heq
          have hp_k : p ∣ k := heq ▸ dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) u
          exact hk.2 hp_k
        exact ⟨⟨Nat.mul_pos (by omega) hpos, by omega⟩, dvd_mul_left _ _⟩
      · intro a _ b _ hab
        dsimp at hab
        exact Nat.mul_right_cancel (pow_pos hp.pos _) hab
      · intro j hj
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hj
        obtain ⟨u, rfl⟩ := hj.2
        have hpos : 0 < p ^ (r - 1) := pow_pos hp.pos _
        have hu1 : 1 ≤ u := by
          by_contra hu0
          have : u = 0 := by omega
          subst this; simp at hj
        have hule : u ≤ k / p ^ (r - 1) := by
          have : u * p ^ (r - 1) ≤ k := by rw [mul_comm]; omega
          exact (Nat.le_div_iff_mul_le hpos).mpr this
        exact ⟨u, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hu1, hule⟩), by dsimp; ring⟩
      · intro _ _; rfl
    have hfact_u :
        ∀ u ∈ Finset.Icc 1 (k / p ^ (r - 1)),
          (u * p ^ (r - 1)).factorization p = r - 1 ∧
            (u * p ^ (r - 1)) / p ^ ((u * p ^ (r - 1)).factorization p) = u ∧ ¬ p ∣ u := by
      intro u hu
      simp only [Finset.mem_Icc] at hu
      have hpos : 0 < p ^ (r - 1) := pow_pos hp.pos _
      have hu_lt_p : u < p := by
        have h1 : u * p ^ (r - 1) ≤ k :=
          le_trans (Nat.mul_le_mul_right _ hu.2) (Nat.div_mul_le_self k _)
        have h2 : u * p ^ (r - 1) < p * p ^ (r - 1) := by
          have hpr : p * p ^ (r - 1) = p ^ r := by
            rw [← _root_.pow_succ', Nat.sub_add_cancel (by omega)]
          omega
        exact (Nat.mul_lt_mul_right hpos).mp h2
      have hu_ndvd : ¬ p ∣ u := Nat.not_dvd_of_pos_of_lt (by omega) hu_lt_p
      have hfu : u.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hu_ndvd
      have hfv : (u * p ^ (r - 1)).factorization p = r - 1 := by
        rw [Nat.factorization_mul (by omega) (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
          hfu, zero_add, hp.factorization_pow, Finsupp.single_eq_same]
      refine ⟨hfv, ?_, hu_ndvd⟩
      rw [hfv, Nat.mul_div_cancel u hpos]
    have hdiv_part :
        ∏ j ∈ (Finset.Icc 1 (k - 1)).filter (fun j => p ^ (r - 1) ∣ j),
            ((p : ZMod (p ^ 3)) ^ (2 * (r - j.factorization p)) -
              ((j / p ^ (j.factorization p) : ℕ) : ZMod (p ^ 3)) ^ 2) ^ 2 =
          (∏ j ∈ (Finset.Icc 1 (k - 1)).filter (fun j => p ^ (r - 1) ∣ j),
              ((j / p ^ (j.factorization p) : ℕ) : ZMod (p ^ 3)) ^ 4) *
            (1 - 2 * (p : ZMod (p ^ 3)) ^ 2 *
              ∑ u ∈ Finset.Icc 1 (k / p ^ (r - 1)), (u : ZMod (p ^ 3))⁻¹ ^ 2) := by
      rw [hbij_div, hbij_div]
      have hlin :
          ∏ u ∈ Finset.Icc 1 (k / p ^ (r - 1)),
              (1 + (-(2 * (p : ZMod (p ^ 3)) ^ 2)) * (u : ZMod (p ^ 3))⁻¹ ^ 2) =
            1 - 2 * (p : ZMod (p ^ 3)) ^ 2 *
              ∑ u ∈ Finset.Icc 1 (k / p ^ (r - 1)), (u : ZMod (p ^ 3))⁻¹ ^ 2 := by
        have hc2 : (-(2 * (p : ZMod (p ^ 3)) ^ 2)) ^ 2 = 0 := by
          have hp4 : (p : ZMod (p ^ 3)) ^ 4 = 0 := zmod_pow_eq_zero_of_ge (by omega)
          linear_combination 4 * hp4
        rw [prod_one_add_eq_one_add_sum _ _ hc2]
        ring
      rw [← hlin, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun u hu => ?_
      obtain ⟨hfv, hdiv_u, hu_ndvd⟩ := hfact_u u hu
      rw [hdiv_u, hfv]
      have h2r : 2 * (r - (r - 1)) = 2 := by omega
      rw [h2r]
      have hp4 : (p : ZMod (p ^ 3)) ^ 4 = 0 := zmod_pow_eq_zero_of_ge (by omega)
      have hu_inv : (u : ZMod (p ^ 3)) * (u : ZMod (p ^ 3))⁻¹ = 1 :=
        mul_inv_of_not_dvd_pow hp hu_ndvd
      have hu2 : (u : ZMod (p ^ 3)) ^ 2 * (u : ZMod (p ^ 3))⁻¹ ^ 2 = 1 := by
        rw [← mul_pow, hu_inv, one_pow]
      linear_combination hp4 + 2 * (p : ZMod (p ^ 3)) ^ 2 * (u : ZMod (p ^ 3)) ^ 2 * hu2
    rw [hsplit_RHS, hdiv_part, hnot_part, hsplit_W]
    ring
  rw [hprod_eval] at hcast
  have hW_ndvd : ¬ p ∣ W_prod := by
    intro hdvd
    rw [Prime.dvd_finsetProd_iff hp.prime] at hdvd
    obtain ⟨j, hj, hjd⟩ := hdvd
    simp only [Finset.mem_Icc] at hj
    exact Nat.not_dvd_ordCompl hp (by omega) (hp.dvd_of_dvd_pow hjd)
  have hW_inv : (W_prod : ZMod (p ^ 3)) * (W_prod : ZMod (p ^ 3))⁻¹ = 1 :=
    mul_inv_of_not_dvd_pow hp hW_ndvd
  have hk_inv : (k : ZMod (p ^ 3)) * (k : ZMod (p ^ 3))⁻¹ = 1 :=
    mul_inv_of_not_dvd_pow hp hk.2
  have hstep1 :
      (k : ZMod (p ^ 3)) ^ 4 * ((T (p ^ r) k / p ^ (3 * r) : ℕ) : ZMod (p ^ 3)) =
        ((p : ZMod (p ^ 3)) ^ r - (k : ZMod (p ^ 3))) *
          (1 - 2 * (p : ZMod (p ^ 3)) ^ 2 *
            ∑ u ∈ Finset.Icc 1 (k / p ^ (r - 1)), (u : ZMod (p ^ 3))⁻¹ ^ 2) := by
    have hmul := congr_arg (fun z => z * (W_prod : ZMod (p ^ 3))⁻¹) hcast
    calc
      (k : ZMod (p ^ 3)) ^ 4 * ((T (p ^ r) k / p ^ (3 * r) : ℕ) : ZMod (p ^ 3))
          = ((k : ZMod (p ^ 3)) ^ 4 * ((T (p ^ r) k / p ^ (3 * r) : ℕ) : ZMod (p ^ 3))) *
              ((W_prod : ZMod (p ^ 3)) * (W_prod : ZMod (p ^ 3))⁻¹) := by rw [hW_inv, mul_one]
      _ = ((k : ZMod (p ^ 3)) ^ 4 * (W_prod : ZMod (p ^ 3)) *
            ((T (p ^ r) k / p ^ (3 * r) : ℕ) : ZMod (p ^ 3))) * (W_prod : ZMod (p ^ 3))⁻¹ := by ring
      _ = (((p : ZMod (p ^ 3)) ^ r - (k : ZMod (p ^ 3))) *
            ((W_prod : ZMod (p ^ 3)) *
              (1 - 2 * (p : ZMod (p ^ 3)) ^ 2 *
                ∑ u ∈ Finset.Icc 1 (k / p ^ (r - 1)), (u : ZMod (p ^ 3))⁻¹ ^ 2))) *
            (W_prod : ZMod (p ^ 3))⁻¹ := hmul
      _ = (((p : ZMod (p ^ 3)) ^ r - (k : ZMod (p ^ 3))) *
            (1 - 2 * (p : ZMod (p ^ 3)) ^ 2 *
              ∑ u ∈ Finset.Icc 1 (k / p ^ (r - 1)), (u : ZMod (p ^ 3))⁻¹ ^ 2)) *
            ((W_prod : ZMod (p ^ 3)) * (W_prod : ZMod (p ^ 3))⁻¹) := by ring
      _ = ((p : ZMod (p ^ 3)) ^ r - (k : ZMod (p ^ 3))) *
            (1 - 2 * (p : ZMod (p ^ 3)) ^ 2 *
              ∑ u ∈ Finset.Icc 1 (k / p ^ (r - 1)), (u : ZMod (p ^ 3))⁻¹ ^ 2) := by
            rw [hW_inv, mul_one]
  have hpr2 : (p : ZMod (p ^ 3)) ^ r * (p : ZMod (p ^ 3)) ^ 2 = 0 := by
    rw [← pow_add]
    exact zmod_pow_eq_zero_of_ge (by omega)
  have hmul := congr_arg (fun z => z * (k : ZMod (p ^ 3))⁻¹ ^ 4) hstep1
  have hk4 : (k : ZMod (p ^ 3)) ^ 4 * (k : ZMod (p ^ 3))⁻¹ ^ 4 = 1 := by
    rw [← mul_pow, hk_inv, one_pow]
  have hk1_pow : (k : ZMod (p ^ 3)) * (k : ZMod (p ^ 3))⁻¹ ^ 4 = (k : ZMod (p ^ 3))⁻¹ ^ 3 := by
    have : (4 : ℕ) = 1 + 3 := rfl
    rw [this, pow_add, pow_one, ← mul_assoc, hk_inv, one_mul]
  set S_u : ZMod (p ^ 3) := ∑ u ∈ Finset.Icc 1 (k / p ^ (r - 1)), (u : ZMod (p ^ 3))⁻¹ ^ 2
  calc
    ((T (p ^ r) k / p ^ (3 * r) : ℕ) : ZMod (p ^ 3))
        = ((k : ZMod (p ^ 3)) ^ 4 * ((T (p ^ r) k / p ^ (3 * r) : ℕ) : ZMod (p ^ 3))) *
            (k : ZMod (p ^ 3))⁻¹ ^ 4 := by
          calc
            ((T (p ^ r) k / p ^ (3 * r) : ℕ) : ZMod (p ^ 3))
                = ((T (p ^ r) k / p ^ (3 * r) : ℕ) : ZMod (p ^ 3)) *
                    ((k : ZMod (p ^ 3)) ^ 4 * (k : ZMod (p ^ 3))⁻¹ ^ 4) := by rw [hk4, mul_one]
            _ = _ := by ring
    _ = (((p : ZMod (p ^ 3)) ^ r - (k : ZMod (p ^ 3))) *
          (1 - 2 * (p : ZMod (p ^ 3)) ^ 2 * S_u)) * (k : ZMod (p ^ 3))⁻¹ ^ 4 := hmul
    _ = (p : ZMod (p ^ 3)) ^ r * (k : ZMod (p ^ 3))⁻¹ ^ 4 -
          ((k : ZMod (p ^ 3)) * (k : ZMod (p ^ 3))⁻¹ ^ 4) +
          2 * (p : ZMod (p ^ 3)) ^ 2 * ((k : ZMod (p ^ 3)) * (k : ZMod (p ^ 3))⁻¹ ^ 4) * S_u -
          2 * ((p : ZMod (p ^ 3)) ^ r * (p : ZMod (p ^ 3)) ^ 2) * S_u * (k : ZMod (p ^ 3))⁻¹ ^ 4 := by
          ring
    _ = (p : ZMod (p ^ 3)) ^ r * (k : ZMod (p ^ 3))⁻¹ ^ 4 -
          (k : ZMod (p ^ 3))⁻¹ ^ 3 +
          2 * (p : ZMod (p ^ 3)) ^ 2 * (k : ZMod (p ^ 3))⁻¹ ^ 3 * S_u := by
          rw [hk1_pow, hpr2]; ring

private lemma theoremA_sum_zero {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr2 : 2 ≤ r) :
    ∑ k ∈ U p r, (T (p ^ r) k : ZMod (p ^ (3 * r + 3))) = 0 := by
  have hdvd_all : ∀ k ∈ U p r, p ^ (3 * r) ∣ T (p ^ r) k := by
    intro k hk
    simp only [U, Finset.mem_filter, Finset.mem_range] at hk
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun h0 => hk.2 (h0 ▸ dvd_zero p)
    have hs0 : k.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hk.2
    have h := pow_dvd_T hp (by omega) hk1 hk.1
    simpa [hs0] using h
  let S_div : ℕ := ∑ k ∈ U p r, T (p ^ r) k / p ^ (3 * r)
  have hsum_nat : ∑ k ∈ U p r, T (p ^ r) k = p ^ (3 * r) * S_div := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => (Nat.mul_div_cancel' (hdvd_all k hk)).symm
  have hS_zmod3 : (S_div : ZMod (p ^ 3)) = 0 := by
    simp only [S_div, Nat.cast_sum]
    rw [Finset.sum_congr rfl fun k hk => theoremA_term_zmod_p3 hp hr2 hk]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h1 :
        ∑ k ∈ U p r, (p : ZMod (p ^ 3)) ^ r * (k : ZMod (p ^ 3))⁻¹ ^ 4 = 0 := by
      rw [← Finset.mul_sum]
      have hcast_zero :
          ZMod.castHom (dvd_pow_self p (by norm_num : (3 : ℕ) ≠ 0)) (ZMod p)
            (∑ k ∈ U p r, (k : ZMod (p ^ 3))⁻¹ ^ 4) = 0 := by
        rw [map_sum]
        have hcongr :
            ∑ k ∈ U p r,
              ZMod.castHom (dvd_pow_self p (by norm_num : (3 : ℕ) ≠ 0)) (ZMod p)
                ((k : ZMod (p ^ 3))⁻¹ ^ 4) =
              ∑ k ∈ U p r, (k : ZMod p)⁻¹ ^ 4 := by
          refine Finset.sum_congr rfl fun k hk => ?_
          simp only [U, Finset.mem_filter] at hk
          rw [map_pow, castHom_inv_of_isUnit _ _ (isUnit_of_not_dvd_pow hp hk.2), map_natCast]
        rw [hcongr]
        exact sum_U_inv_pow4_eq_zero_zmod_p hp hr2
      have hz := mul_eq_zero_of_dvd_of_castHom_p_eq_zero (p := p) (N := 3) (c := p ^ r)
        hp.pos (by omega) (pow_dvd_pow p (by omega)) _ hcast_zero
      simpa [Nat.cast_pow] using hz
    have h2 : ∑ k ∈ U p r, (k : ZMod (p ^ 3))⁻¹ ^ 3 = 0 :=
      sum_U_inv_cube_eq_zero_zmod_p3 hp hp5 hr2
    have h3 :
        ∑ k ∈ U p r,
            2 * (p : ZMod (p ^ 3)) ^ 2 * (k : ZMod (p ^ 3))⁻¹ ^ 3 *
              ∑ u ∈ Finset.Icc 1 (k / p ^ (r - 1)), (u : ZMod (p ^ 3))⁻¹ ^ 2 = 0 := by
      have hpow : p ^ r = p * p ^ (r - 1) := by rw [← _root_.pow_succ', Nat.sub_add_cancel (by omega)]
      have hU : U p r = (Finset.range (p * p ^ (r - 1))).filter (fun k => ¬ p ∣ k) := by
        simp only [U, hpow]
      rw [hU, sum_filter_range_mul_pow hp (by omega : 1 ≤ r - 1)]
      refine Finset.sum_eq_zero fun q _ => ?_
      have hdiv_q :
          ∀ t ∈ U p (r - 1), (q * p ^ (r - 1) + t) / p ^ (r - 1) = q := by
        intro t ht
        simp only [U, Finset.mem_filter, Finset.mem_range] at ht
        rw [mul_comm q, Nat.mul_add_div (pow_pos hp.pos _), Nat.div_eq_of_lt ht.1, add_zero]
      have hrew :
          ∑ t ∈ U p (r - 1),
              2 * (p : ZMod (p ^ 3)) ^ 2 * ((q * p ^ (r - 1) + t : ℕ) : ZMod (p ^ 3))⁻¹ ^ 3 *
                ∑ u ∈ Finset.Icc 1 ((q * p ^ (r - 1) + t) / p ^ (r - 1)), (u : ZMod (p ^ 3))⁻¹ ^ 2 =
            (2 * ∑ u ∈ Finset.Icc 1 q, (u : ZMod (p ^ 3))⁻¹ ^ 2) *
              (((p ^ 2 : ℕ) : ZMod (p ^ 3)) *
                ∑ t ∈ U p (r - 1), ((q * p ^ (r - 1) + t : ℕ) : ZMod (p ^ 3))⁻¹ ^ 3) := by
        set A : ZMod (p ^ 3) := 2 * ∑ u ∈ Finset.Icc 1 q, (u : ZMod (p ^ 3))⁻¹ ^ 2
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [hdiv_q t ht]
        simp only [A]
        push_cast
        ring
      rw [hrew]
      have hcast_zero :
          ZMod.castHom (dvd_pow_self p (by norm_num : (3 : ℕ) ≠ 0)) (ZMod p)
            (∑ t ∈ U p (r - 1), ((q * p ^ (r - 1) + t : ℕ) : ZMod (p ^ 3))⁻¹ ^ 3) = 0 := by
        rw [map_sum]
        have hcongr :
            ∑ t ∈ U p (r - 1),
              ZMod.castHom (dvd_pow_self p (by norm_num : (3 : ℕ) ≠ 0)) (ZMod p)
                (((q * p ^ (r - 1) + t : ℕ) : ZMod (p ^ 3))⁻¹ ^ 3) =
              ∑ t ∈ U p (r - 1), (t : ZMod p)⁻¹ ^ 3 := by
          refine Finset.sum_congr rfl fun t ht => ?_
          simp only [U, Finset.mem_filter] at ht
          have hndvd : ¬ p ∣ q * p ^ (r - 1) + t := by
            intro hdvd
            have hp_pa : p ∣ q * p ^ (r - 1) :=
              dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) q
            exact ht.2 ((Nat.dvd_add_right hp_pa).mp hdvd)
          rw [map_pow, castHom_inv_of_isUnit _ _ (isUnit_of_not_dvd_pow hp hndvd), map_natCast]
          have hpr0 : ((p ^ (r - 1) : ℕ) : ZMod p) = 0 := by
            rw [Nat.cast_pow, ZMod.natCast_self, zero_pow (by omega)]
          simp [hpr0]
        rw [hcongr]
        exact sum_U_inv_cube_eq_zero_zmod_p hp (by omega) (by omega)
      have hz := mul_eq_zero_of_dvd_of_castHom_p_eq_zero (p := p) (N := 3) (c := p ^ 2)
        hp.pos (by omega) (dvd_refl _) _ hcast_zero
      rw [hz, mul_zero]
    rw [h1, h2, h3, sub_self, zero_add]
  have hp3_dvd : p ^ 3 ∣ S_div := (ZMod.natCast_eq_zero_iff S_div (p ^ 3)).mp hS_zmod3
  have hdvd_tot : p ^ (3 * r + 3) ∣ ∑ k ∈ U p r, T (p ^ r) k := by
    rw [hsum_nat, pow_add]
    exact Nat.mul_dvd_mul_left (p ^ (3 * r)) hp3_dvd
  rw [← Nat.cast_sum]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr hdvd_tot

private lemma step_down_int {p r m : ℕ} (hp : p.Prime) (hr2 : 2 ≤ r)
    (hm1 : 1 ≤ m) (hm_lt : m < p ^ (r - 1)) :
    (∏ j ∈ (Finset.range (p * m)).filter (fun j => ¬ p ∣ j), (j : ℤ) ^ 4) *
        (T (p ^ r) (p * m) : ℤ) =
      (T (p ^ (r - 1)) m : ℤ) *
        ∏ j ∈ (Finset.range (p * m)).filter (fun j => ¬ p ∣ j),
          ((p : ℤ) ^ (2 * r) - (j : ℤ) ^ 2) ^ 2 := by
  have hpr : p ^ r = p * p ^ (r - 1) := by rw [← _root_.pow_succ', Nat.sub_add_cancel (by omega)]
  have hpm_lt : p * m < p ^ r := by rw [hpr]; exact Nat.mul_lt_mul_of_pos_left hm_lt hp.pos
  have hmain_r := term_prod_int (n := p ^ r) (k := p * m) (Nat.mul_pos hp.pos (by omega)) (by omega)
  have hmain_r1 := term_prod_int (n := p ^ (r - 1)) (k := m) hm1 (by omega)
  have hfilter_eq :
      (Finset.Icc 1 (p * m)).filter (fun j => ¬ p ∣ j) =
        (Finset.range (p * m)).filter (fun j => ¬ p ∣ j) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hjle⟩, hndvd⟩
      have hne : j ≠ p * m := fun heq => hndvd (heq ▸ dvd_mul_right p m)
      exact ⟨by omega, hndvd⟩
    · rintro ⟨hjlt, hndvd⟩
      have hpos : 1 ≤ j := Nat.pos_of_ne_zero fun h0 => hndvd (h0 ▸ dvd_zero p)
      exact ⟨⟨hpos, by omega⟩, hndvd⟩
  have hfilter_eq' :
      (Finset.Icc 1 (p * m - 1)).filter (fun j => ¬ p ∣ j) =
        (Finset.range (p * m)).filter (fun j => ¬ p ∣ j) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hjle⟩, hndvd⟩
      exact ⟨by omega, hndvd⟩
    · rintro ⟨hjlt, hndvd⟩
      have hpos : 1 ≤ j := Nat.pos_of_ne_zero fun h0 => hndvd (h0 ▸ dvd_zero p)
      exact ⟨⟨hpos, by omega⟩, hndvd⟩
  have hfac_split :
      ((p * m).factorial : ℤ) ^ 4 =
        (p : ℤ) ^ (4 * m) * (m.factorial : ℤ) ^ 4 *
          ∏ j ∈ (Finset.range (p * m)).filter (fun j => ¬ p ∣ j), (j : ℤ) ^ 4 := by
    rw [← prod_Icc_eq_factorial (p * m), Nat.cast_prod, ← Finset.prod_pow,
      ← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (p * m)) (fun j => p ∣ j),
      hfilter_eq]
    congr 1
    have hdiv_prod :
        ∏ j ∈ (Finset.Icc 1 (p * m)).filter (fun j => p ∣ j), (j : ℤ) ^ 4 =
          ∏ i ∈ Finset.Icc 1 m, ((p : ℤ) * (i : ℤ)) ^ 4 := by
      symm
      refine Finset.prod_nbij (fun i => p * i) ?_ ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_Icc, Finset.mem_filter] at hi ⊢
        exact ⟨⟨Nat.mul_pos hp.pos (by omega), Nat.mul_le_mul_left p hi.2⟩, dvd_mul_right p i⟩
      · intro a _ b _ hab
        dsimp at hab
        exact Nat.mul_left_cancel hp.pos hab
      · intro j hj
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hj
        obtain ⟨i, rfl⟩ := hj.2
        have hi1 : 1 ≤ i := by
          by_contra hi0
          have : i = 0 := by omega
          subst this; simp at hj
        have hile : i ≤ m := Nat.le_of_mul_le_mul_left hj.1.2 hp.pos
        exact ⟨i, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hi1, hile⟩), rfl⟩
      · intro i _; push_cast; rfl
    rw [hdiv_prod]
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, Finset.prod_pow]
    rw [← Nat.cast_prod, prod_Icc_eq_factorial m]
    have hcard : m + 1 - 1 = m := by omega
    rw [hcard, ← pow_mul]
  have hprod_split :
      ∏ j ∈ Finset.Icc 1 (p * m - 1), (((p ^ r : ℕ) : ℤ) ^ 2 - (j : ℤ) ^ 2) ^ 2 =
        (p : ℤ) ^ (4 * (m - 1)) *
          (∏ i ∈ Finset.Icc 1 (m - 1), (((p ^ (r - 1) : ℕ) : ℤ) ^ 2 - (i : ℤ) ^ 2) ^ 2) *
          ∏ j ∈ (Finset.range (p * m)).filter (fun j => ¬ p ∣ j),
            ((p : ℤ) ^ (2 * r) - (j : ℤ) ^ 2) ^ 2 := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (p * m - 1)) (fun j => p ∣ j),
      hfilter_eq']
    have hndiv_eq :
        ∏ j ∈ (Finset.range (p * m)).filter (fun j => ¬ p ∣ j),
            (((p ^ r : ℕ) : ℤ) ^ 2 - (j : ℤ) ^ 2) ^ 2 =
          ∏ j ∈ (Finset.range (p * m)).filter (fun j => ¬ p ∣ j),
            ((p : ℤ) ^ (2 * r) - (j : ℤ) ^ 2) ^ 2 := by
      refine Finset.prod_congr rfl fun j _ => ?_
      push_cast
      rw [← pow_mul, mul_comm r 2]
    rw [hndiv_eq]
    congr 1
    have hdiv_prod :
        ∏ j ∈ (Finset.Icc 1 (p * m - 1)).filter (fun j => p ∣ j),
            (((p ^ r : ℕ) : ℤ) ^ 2 - (j : ℤ) ^ 2) ^ 2 =
          ∏ i ∈ Finset.Icc 1 (m - 1),
            ((p : ℤ) ^ 4 * ((((p ^ (r - 1) : ℕ) : ℤ) ^ 2 - (i : ℤ) ^ 2) ^ 2)) := by
      symm
      refine Finset.prod_nbij (fun i => p * i) ?_ ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_Icc, Finset.mem_filter] at hi ⊢
        have hlt : p * i < p * m := Nat.mul_lt_mul_of_pos_left (by omega) hp.pos
        exact ⟨⟨Nat.mul_pos hp.pos (by omega), by omega⟩, dvd_mul_right p i⟩
      · intro a _ b _ hab
        dsimp at hab
        exact Nat.mul_left_cancel hp.pos hab
      · intro j hj
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hj
        obtain ⟨i, rfl⟩ := hj.2
        have hi1 : 1 ≤ i := by
          by_contra hi0
          have : i = 0 := by omega
          subst this; simp at hj
        have hilt : i < m := by
          have : p * i < p * m := by omega
          exact (Nat.mul_lt_mul_left hp.pos).mp this
        exact ⟨i, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hi1, by omega⟩), rfl⟩
      · intro i _
        have hpr_z : ((p ^ r : ℕ) : ℤ) = (p : ℤ) * ((p ^ (r - 1) : ℕ) : ℤ) := by
          exact_mod_cast hpr
        rw [hpr_z]
        push_cast
        ring
    rw [hdiv_prod, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
    have hcard : m - 1 + 1 - 1 = m - 1 := by omega
    rw [hcard, ← pow_mul]
  have hcancel_pos : (0 : ℤ) < (p : ℤ) ^ (4 * m) * (m.factorial : ℤ) ^ 4 :=
    mul_pos (pow_pos (by exact_mod_cast hp.pos) _) (pow_pos (by exact_mod_cast Nat.factorial_pos m) _)
  apply mul_left_cancel₀ (ne_of_gt hcancel_pos)
  have hpr_z : ((p ^ r : ℕ) : ℤ) = (p : ℤ) * ((p ^ (r - 1) : ℕ) : ℤ) := by
    exact_mod_cast hpr
  have hpow4m : (p : ℤ) ^ 4 * (p : ℤ) ^ (4 * (m - 1)) = (p : ℤ) ^ (4 * m) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    (p : ℤ) ^ (4 * m) * (m.factorial : ℤ) ^ 4 *
        ((∏ j ∈ (Finset.range (p * m)).filter (fun j => ¬ p ∣ j), (j : ℤ) ^ 4) *
          (T (p ^ r) (p * m) : ℤ))
        = ((p * m).factorial : ℤ) ^ 4 * (T (p ^ r) (p * m) : ℤ) := by rw [hfac_split]; ring
    _ = ((p ^ r : ℕ) : ℤ) ^ 3 * (((p ^ r : ℕ) : ℤ) - ((p * m : ℕ) : ℤ)) *
          ∏ j ∈ Finset.Icc 1 (p * m - 1), (((p ^ r : ℕ) : ℤ) ^ 2 - (j : ℤ) ^ 2) ^ 2 := hmain_r
    _ = ((p : ℤ) ^ 4 * (p : ℤ) ^ (4 * (m - 1))) *
          (((p ^ (r - 1) : ℕ) : ℤ) ^ 3 * (((p ^ (r - 1) : ℕ) : ℤ) - (m : ℤ)) *
            ∏ i ∈ Finset.Icc 1 (m - 1), (((p ^ (r - 1) : ℕ) : ℤ) ^ 2 - (i : ℤ) ^ 2) ^ 2) *
          ∏ j ∈ (Finset.range (p * m)).filter (fun j => ¬ p ∣ j),
            ((p : ℤ) ^ (2 * r) - (j : ℤ) ^ 2) ^ 2 := by
          rw [hprod_split, hpr_z]; push_cast; ring
    _ = (p : ℤ) ^ (4 * m) * (((m.factorial : ℤ) ^ 4) * (T (p ^ (r - 1)) m : ℤ)) *
          ∏ j ∈ (Finset.range (p * m)).filter (fun j => ¬ p ∣ j),
            ((p : ℤ) ^ (2 * r) - (j : ℤ) ^ 2) ^ 2 := by rw [hpow4m, ← hmain_r1]
    _ = (p : ℤ) ^ (4 * m) * (m.factorial : ℤ) ^ 4 *
          ((T (p ^ (r - 1)) m : ℤ) *
            ∏ j ∈ (Finset.range (p * m)).filter (fun j => ¬ p ∣ j),
              ((p : ℤ) ^ (2 * r) - (j : ℤ) ^ 2) ^ 2) := by ring

private lemma T_p_u_mod_p4 {p u : ℕ} (hp : p.Prime) (hu1 : 1 ≤ u) (hup : u ≤ p - 1) :
    (T p u : ZMod (p ^ 4)) = -((p : ZMod (p ^ 4)) ^ 3 * (u : ZMod (p ^ 4))⁻¹ ^ 3) := by
  have hu_ndvd : ¬ p ∣ u := Nat.not_dvd_of_pos_of_lt hu1 (by omega)
  have hum1_ndvd : ¬ p ∣ (u - 1).factorial := hp.dvd_factorial.not.mpr (by omega)
  have hmain := term_prod_int (n := p) (k := u) hu1 hup
  have hprod_mod :
      ((p : ℤ) ^ 2) ∣
        (∏ i ∈ Finset.Icc 1 (u - 1), ((p : ℤ) ^ 2 - (i : ℤ) ^ 2) ^ 2) - ((u - 1).factorial : ℤ) ^ 4 := by
    have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := zmod_pow_eq_zero_of_ge (le_refl 2)
    have hcast :
        ((∏ i ∈ Finset.Icc 1 (u - 1), ((p : ℤ) ^ 2 - (i : ℤ) ^ 2) ^ 2 : ℤ) : ZMod (p ^ 2)) =
          ((((u - 1).factorial : ℤ) ^ 4 : ℤ) : ZMod (p ^ 2)) := by
      push_cast
      have hprod :
          ∏ i ∈ Finset.Icc 1 (u - 1), ((p : ZMod (p ^ 2)) ^ 2 - (i : ZMod (p ^ 2)) ^ 2) ^ 2 =
            ∏ i ∈ Finset.Icc 1 (u - 1), (i : ZMod (p ^ 2)) ^ 4 := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hp2]; ring
      rw [hprod, Finset.prod_pow, ← prod_Icc_eq_factorial (u - 1)]
      push_cast; rfl
    have hcast' :
        (((∏ i ∈ Finset.Icc 1 (u - 1), ((p : ℤ) ^ 2 - (i : ℤ) ^ 2) ^ 2) -
            ((u - 1).factorial : ℤ) ^ 4 : ℤ) : ZMod (p ^ 2)) = 0 := by
      rw [Int.cast_sub, hcast, sub_self]
    have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ 2)).mp hcast'
    simpa [Nat.cast_pow] using hdvd
  obtain ⟨q, hq⟩ := hprod_mod
  have hprod_eq :
      ∏ i ∈ Finset.Icc 1 (u - 1), ((p : ℤ) ^ 2 - (i : ℤ) ^ 2) ^ 2 =
        ((u - 1).factorial : ℤ) ^ 4 + (p : ℤ) ^ 2 * q := by linarith
  rw [hprod_eq] at hmain
  have hcast := congr_arg (Int.cast (R := ZMod (p ^ 4))) hmain
  push_cast at hcast
  have hp4 : (p : ZMod (p ^ 4)) ^ 4 = 0 := zmod_pow_eq_zero_of_ge (le_refl 4)
  have hfac_split : (u.factorial : ZMod (p ^ 4)) = (u : ZMod (p ^ 4)) * ((u - 1).factorial : ZMod (p ^ 4)) := by
    have hnat : u.factorial = u * (u - 1).factorial := by
      cases u with
      | zero => omega
      | succ j => exact Nat.factorial_succ j
    rw [hnat, Nat.cast_mul]
  rw [hfac_split] at hcast
  have hfac4_inv :
      ((u - 1).factorial : ZMod (p ^ 4)) ^ 4 * (((u - 1).factorial : ZMod (p ^ 4))⁻¹) ^ 4 = 1 := by
    rw [← mul_pow, mul_inv_of_not_dvd_pow hp hum1_ndvd, one_pow]
  have hu_inv : (u : ZMod (p ^ 4)) * (u : ZMod (p ^ 4))⁻¹ = 1 := mul_inv_of_not_dvd_pow hp hu_ndvd
  have h1 :
      ((u : ZMod (p ^ 4)) ^ 4 * (T p u : ZMod (p ^ 4))) * ((u - 1).factorial : ZMod (p ^ 4)) ^ 4 =
        (-((p : ZMod (p ^ 4)) ^ 3 * (u : ZMod (p ^ 4)))) * ((u - 1).factorial : ZMod (p ^ 4)) ^ 4 := by
    linear_combination
      hcast + (((u - 1).factorial : ZMod (p ^ 4)) ^ 4 +
        (p : ZMod (p ^ 4)) * ((p : ZMod (p ^ 4)) - (u : ZMod (p ^ 4))) * (q : ZMod (p ^ 4))) * hp4
  have h2 := congr_arg (fun z => z * (((u - 1).factorial : ZMod (p ^ 4))⁻¹) ^ 4) h1
  have hstep1 : (u : ZMod (p ^ 4)) ^ 4 * (T p u : ZMod (p ^ 4)) =
      -((p : ZMod (p ^ 4)) ^ 3 * (u : ZMod (p ^ 4))) := by
    calc
      (u : ZMod (p ^ 4)) ^ 4 * (T p u : ZMod (p ^ 4))
          = ((u : ZMod (p ^ 4)) ^ 4 * (T p u : ZMod (p ^ 4))) *
              (((u - 1).factorial : ZMod (p ^ 4)) ^ 4 * (((u - 1).factorial : ZMod (p ^ 4))⁻¹) ^ 4) := by
            rw [hfac4_inv, mul_one]
      _ = (((u : ZMod (p ^ 4)) ^ 4 * (T p u : ZMod (p ^ 4))) * ((u - 1).factorial : ZMod (p ^ 4)) ^ 4) *
            (((u - 1).factorial : ZMod (p ^ 4))⁻¹) ^ 4 := by ring
      _ = ((-((p : ZMod (p ^ 4)) ^ 3 * (u : ZMod (p ^ 4)))) * ((u - 1).factorial : ZMod (p ^ 4)) ^ 4) *
            (((u - 1).factorial : ZMod (p ^ 4))⁻¹) ^ 4 := h2
      _ = (-((p : ZMod (p ^ 4)) ^ 3 * (u : ZMod (p ^ 4)))) *
            (((u - 1).factorial : ZMod (p ^ 4)) ^ 4 * (((u - 1).factorial : ZMod (p ^ 4))⁻¹) ^ 4) := by
            ring
      _ = -((p : ZMod (p ^ 4)) ^ 3 * (u : ZMod (p ^ 4))) := by rw [hfac4_inv, mul_one]
  have hmul := congr_arg (fun z => z * (u : ZMod (p ^ 4))⁻¹ ^ 4) hstep1
  have hu4 : (u : ZMod (p ^ 4)) ^ 4 * (u : ZMod (p ^ 4))⁻¹ ^ 4 = 1 := by
    rw [← mul_pow, hu_inv, one_pow]
  have hu1_pow : (u : ZMod (p ^ 4)) * (u : ZMod (p ^ 4))⁻¹ ^ 4 = (u : ZMod (p ^ 4))⁻¹ ^ 3 := by
    rw [show (u : ZMod (p ^ 4))⁻¹ ^ 4 = (u : ZMod (p ^ 4))⁻¹ * (u : ZMod (p ^ 4))⁻¹ ^ 3 by ring,
      ← mul_assoc, hu_inv, one_mul]
  calc
    (T p u : ZMod (p ^ 4))
        = ((u : ZMod (p ^ 4)) ^ 4 * (T p u : ZMod (p ^ 4))) * (u : ZMod (p ^ 4))⁻¹ ^ 4 := by
          calc
            (T p u : ZMod (p ^ 4))
                = (T p u : ZMod (p ^ 4)) * ((u : ZMod (p ^ 4)) ^ 4 * (u : ZMod (p ^ 4))⁻¹ ^ 4) := by
                  rw [hu4, mul_one]
            _ = _ := by ring
    _ = (-((p : ZMod (p ^ 4)) ^ 3 * (u : ZMod (p ^ 4)))) * (u : ZMod (p ^ 4))⁻¹ ^ 4 := hmul
    _ = -((p : ZMod (p ^ 4)) ^ 3 * ((u : ZMod (p ^ 4)) * (u : ZMod (p ^ 4))⁻¹ ^ 4)) := by ring
    _ = -((p : ZMod (p ^ 4)) ^ 3 * (u : ZMod (p ^ 4))⁻¹ ^ 3) := by rw [hu1_pow]

private lemma T_top_slice_mod_p4 {p u : ℕ} (hp : p.Prime) (hu1 : 1 ≤ u) (hup : u ≤ p - 1) :
    ∀ d : ℕ, 1 ≤ d →
      (T (p ^ d) (u * p ^ (d - 1)) : ZMod (p ^ 4)) =
        -((p : ZMod (p ^ 4)) ^ 3 * (u : ZMod (p ^ 4))⁻¹ ^ 3)
  | 0, h => by omega
  | 1, _ => by
    simpa [pow_one, pow_zero, mul_one] using T_p_u_mod_p4 hp hu1 hup
  | d + 2, _ => by
    have ih := T_top_slice_mod_p4 hp hu1 hup (d + 1) (by omega)
    have hlt : u * p ^ d < p ^ (d + 1) := by
      rw [pow_succ']
      have : u < p := by omega
      exact Nat.mul_lt_mul_of_pos_right this (pow_pos hp.pos d)
    have hstep := step_down_int (p := p) (r := d + 2) (m := u * p ^ d) hp (by omega)
      (Nat.mul_pos (by omega) (pow_pos hp.pos d)) (by simpa using hlt)
    have hpm_eq : p * (u * p ^ d) = u * p ^ (d + 1) := by rw [pow_succ']; ring
    rw [hpm_eq] at hstep
    have hcast := congr_arg (Int.cast (R := ZMod (p ^ 4))) hstep
    push_cast at hcast
    have hprod_eq :
        ∏ j ∈ (Finset.range (u * p ^ (d + 1))).filter (fun j => ¬ p ∣ j),
            ((p : ZMod (p ^ 4)) ^ (2 * (d + 2)) - (j : ZMod (p ^ 4)) ^ 2) ^ 2 =
          ∏ j ∈ (Finset.range (u * p ^ (d + 1))).filter (fun j => ¬ p ∣ j),
            (j : ZMod (p ^ 4)) ^ 4 := by
      refine Finset.prod_congr rfl fun j _ => ?_
      have hp0 : (p : ZMod (p ^ 4)) ^ (2 * (d + 2)) = 0 := zmod_pow_eq_zero_of_ge (by omega)
      rw [hp0]; ring
    rw [hprod_eq] at hcast
    let Q : ℕ := ∏ j ∈ (Finset.range (u * p ^ (d + 1))).filter (fun j => ¬ p ∣ j), j ^ 4
    have hQ_ndvd : ¬ p ∣ Q := by
      intro hdvd
      rw [Prime.dvd_finsetProd_iff hp.prime] at hdvd
      obtain ⟨j, hj, hjd⟩ := hdvd
      simp only [Finset.mem_filter] at hj
      exact hj.2 (hp.dvd_of_dvd_pow hjd)
    have hQ_inv : (Q : ZMod (p ^ 4)) * (Q : ZMod (p ^ 4))⁻¹ = 1 :=
      mul_inv_of_not_dvd_pow hp hQ_ndvd
    have hQ_cast :
        (Q : ZMod (p ^ 4)) =
          ∏ j ∈ (Finset.range (u * p ^ (d + 1))).filter (fun j => ¬ p ∣ j), (j : ZMod (p ^ 4)) ^ 4 := by
      simp only [Q, Nat.cast_prod, Nat.cast_pow]
    rw [← hQ_cast] at hcast
    have heq : (T (p ^ (d + 2)) (u * p ^ (d + 1)) : ZMod (p ^ 4)) =
        (T (p ^ (d + 1)) (u * p ^ d) : ZMod (p ^ 4)) := by
      have hmul := congr_arg (fun z => z * (Q : ZMod (p ^ 4))⁻¹) hcast
      calc
        (T (p ^ (d + 2)) (u * p ^ (d + 1)) : ZMod (p ^ 4))
            = (T (p ^ (d + 2)) (u * p ^ (d + 1)) : ZMod (p ^ 4)) *
                ((Q : ZMod (p ^ 4)) * (Q : ZMod (p ^ 4))⁻¹) := by rw [hQ_inv, mul_one]
        _ = ((Q : ZMod (p ^ 4)) * (T (p ^ (d + 2)) (u * p ^ (d + 1)) : ZMod (p ^ 4))) *
              (Q : ZMod (p ^ 4))⁻¹ := by ring
        _ = ((T (p ^ (d + 1)) (u * p ^ d) : ZMod (p ^ 4)) * (Q : ZMod (p ^ 4))) *
              (Q : ZMod (p ^ 4))⁻¹ := by simpa using hmul
        _ = (T (p ^ (d + 1)) (u * p ^ d) : ZMod (p ^ 4)) *
              ((Q : ZMod (p ^ 4)) * (Q : ZMod (p ^ 4))⁻¹) := by ring
        _ = (T (p ^ (d + 1)) (u * p ^ d) : ZMod (p ^ 4)) := by rw [hQ_inv, mul_one]
    have ih' : (T (p ^ (d + 1)) (u * p ^ d) : ZMod (p ^ 4)) =
        -((p : ZMod (p ^ 4)) ^ 3 * (u : ZMod (p ^ 4))⁻¹ ^ 3) := by
      simpa using ih
    exact heq.trans ih'

private lemma step_down_diff_zmod {p r m : ℕ} (hp : p.Prime) (hr2 : 2 ≤ r)
    (hm1 : 1 ≤ m) (hm_lt : m < p ^ (r - 1)) :
    (T (p ^ r) (p * m) : ZMod (p ^ (3 * r + 3))) - (T (p ^ (r - 1)) m : ZMod (p ^ (3 * r + 3))) =
      -2 * ((p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) * (T (p ^ (r - 1)) m : ZMod (p ^ (3 * r + 3)))) *
        ∑ j ∈ (Finset.range (p * m)).filter (fun j => ¬ p ∣ j),
          (j : ZMod (p ^ (3 * r + 3)))⁻¹ ^ 2 := by
  have hstep := step_down_int hp hr2 hm1 hm_lt
  have hcast := congr_arg (Int.cast (R := ZMod (p ^ (3 * r + 3)))) hstep
  push_cast at hcast
  let S_j := (Finset.range (p * m)).filter (fun j => ¬ p ∣ j)
  let Q : ℕ := ∏ j ∈ S_j, j ^ 4
  have hQ_ndvd : ¬ p ∣ Q := by
    intro hdvd
    rw [Prime.dvd_finsetProd_iff hp.prime] at hdvd
    obtain ⟨j, hj, hjd⟩ := hdvd
    simp only [S_j, Finset.mem_filter] at hj
    exact hj.2 (hp.dvd_of_dvd_pow hjd)
  have hQ_inv : (Q : ZMod (p ^ (3 * r + 3))) * (Q : ZMod (p ^ (3 * r + 3)))⁻¹ = 1 :=
    mul_inv_of_not_dvd_pow hp hQ_ndvd
  have hQ_cast : (Q : ZMod (p ^ (3 * r + 3))) = ∏ j ∈ S_j, (j : ZMod (p ^ (3 * r + 3))) ^ 4 := by
    simp only [Q, Nat.cast_prod, Nat.cast_pow]
  have hprod_fac :
      ∏ j ∈ S_j, ((p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) - (j : ZMod (p ^ (3 * r + 3))) ^ 2) ^ 2 =
        (Q : ZMod (p ^ (3 * r + 3))) *
          ∏ j ∈ S_j, (1 - (p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) *
            (j : ZMod (p ^ (3 * r + 3)))⁻¹ ^ 2) ^ 2 := by
    rw [hQ_cast, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    simp only [S_j, Finset.mem_filter] at hj
    have hj_inv : (j : ZMod (p ^ (3 * r + 3))) * (j : ZMod (p ^ (3 * r + 3)))⁻¹ = 1 :=
      mul_inv_of_not_dvd_pow hp hj.2
    have hj2 : (j : ZMod (p ^ (3 * r + 3))) ^ 2 * (j : ZMod (p ^ (3 * r + 3)))⁻¹ ^ 2 = 1 := by
      rw [← mul_pow, hj_inv, one_pow]
    calc
      ((p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) - (j : ZMod (p ^ (3 * r + 3))) ^ 2) ^ 2
          = ((j : ZMod (p ^ (3 * r + 3))) ^ 2 *
              ((p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) * (j : ZMod (p ^ (3 * r + 3)))⁻¹ ^ 2 - 1)) ^ 2 := by
            congr 1
            linear_combination (p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) * hj2.symm
      _ = (j : ZMod (p ^ (3 * r + 3))) ^ 4 *
            (1 - (p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) * (j : ZMod (p ^ (3 * r + 3)))⁻¹ ^ 2) ^ 2 := by
            ring
  rw [← hQ_cast, hprod_fac] at hcast
  have hT_eq :
      (T (p ^ r) (p * m) : ZMod (p ^ (3 * r + 3))) =
        (T (p ^ (r - 1)) m : ZMod (p ^ (3 * r + 3))) *
          ∏ j ∈ S_j, (1 - (p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) *
            (j : ZMod (p ^ (3 * r + 3)))⁻¹ ^ 2) ^ 2 := by
    have hmul := congr_arg (fun z => z * (Q : ZMod (p ^ (3 * r + 3)))⁻¹) hcast
    calc
      (T (p ^ r) (p * m) : ZMod (p ^ (3 * r + 3)))
          = (T (p ^ r) (p * m) : ZMod (p ^ (3 * r + 3))) *
              ((Q : ZMod (p ^ (3 * r + 3))) * (Q : ZMod (p ^ (3 * r + 3)))⁻¹) := by
            rw [hQ_inv, mul_one]
      _ = ((Q : ZMod (p ^ (3 * r + 3))) * (T (p ^ r) (p * m) : ZMod (p ^ (3 * r + 3)))) *
            (Q : ZMod (p ^ (3 * r + 3)))⁻¹ := by ring
      _ = ((T (p ^ (r - 1)) m : ZMod (p ^ (3 * r + 3))) *
            ((Q : ZMod (p ^ (3 * r + 3))) *
              ∏ j ∈ S_j, (1 - (p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) *
                (j : ZMod (p ^ (3 * r + 3)))⁻¹ ^ 2) ^ 2)) *
            (Q : ZMod (p ^ (3 * r + 3)))⁻¹ := hmul
      _ = ((T (p ^ (r - 1)) m : ZMod (p ^ (3 * r + 3))) *
            ∏ j ∈ S_j, (1 - (p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) *
              (j : ZMod (p ^ (3 * r + 3)))⁻¹ ^ 2) ^ 2) *
            ((Q : ZMod (p ^ (3 * r + 3))) * (Q : ZMod (p ^ (3 * r + 3)))⁻¹) := by ring
      _ = _ := by rw [hQ_inv, mul_one]
  have hs_lt : m.factorization p < r - 1 := by
    have hle : p ^ (m.factorization p) ≤ m := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p)
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp (lt_of_le_of_lt hle hm_lt)
  have hp3_dvd_T : p ^ 3 ∣ T (p ^ (r - 1)) m :=
    dvd_trans (pow_dvd_pow p (by omega : 3 ≤ 3 * (r - 1 - m.factorization p)))
      (pow_dvd_T hp (by omega) hm1 hm_lt)
  have hcast_diff :
      ZMod.castHom (pow_dvd_pow p (by omega : 3 * r ≤ 3 * r + 3)) (ZMod (p ^ (3 * r)))
        ((∏ j ∈ S_j, (1 - (p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) *
            (j : ZMod (p ^ (3 * r + 3)))⁻¹ ^ 2) ^ 2) - 1 +
          2 * (p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) *
            ∑ j ∈ S_j, (j : ZMod (p ^ (3 * r + 3)))⁻¹ ^ 2) = 0 := by
    rw [map_add, map_sub, map_one, map_mul, map_mul, map_ofNat, map_pow, map_natCast,
      map_prod, map_sum]
    have hcongr_sum :
        ∑ j ∈ S_j,
            ZMod.castHom (pow_dvd_pow p (by omega : 3 * r ≤ 3 * r + 3)) (ZMod (p ^ (3 * r)))
              ((j : ZMod (p ^ (3 * r + 3)))⁻¹ ^ 2) =
          ∑ j ∈ S_j, (j : ZMod (p ^ (3 * r)))⁻¹ ^ 2 := by
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [S_j, Finset.mem_filter] at hj
      rw [map_pow, castHom_inv_of_isUnit _ _ (isUnit_of_not_dvd_pow hp hj.2), map_natCast]
    have hp4r : (p : ZMod (p ^ (3 * r))) ^ (4 * r) = 0 := zmod_pow_eq_zero_of_ge (by omega)
    have hcongr_prod :
        ∏ j ∈ S_j,
            ZMod.castHom (pow_dvd_pow p (by omega : 3 * r ≤ 3 * r + 3)) (ZMod (p ^ (3 * r)))
              ((1 - (p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) *
                (j : ZMod (p ^ (3 * r + 3)))⁻¹ ^ 2) ^ 2) =
          ∏ j ∈ S_j, (1 + (-(2 * (p : ZMod (p ^ (3 * r))) ^ (2 * r))) *
            (j : ZMod (p ^ (3 * r)))⁻¹ ^ 2) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      simp only [S_j, Finset.mem_filter] at hj
      rw [map_pow, map_sub, map_one, map_mul, map_pow, map_natCast, map_pow,
        castHom_inv_of_isUnit _ _ (isUnit_of_not_dvd_pow hp hj.2), map_natCast]
      have hsq : ((p : ZMod (p ^ (3 * r))) ^ (2 * r)) ^ 2 = 0 := by
        rw [← pow_mul]
        have : 2 * r * 2 = 4 * r := by omega
        rw [this]; exact hp4r
      linear_combination ((j : ZMod (p ^ (3 * r)))⁻¹ ^ 2) ^ 2 * hsq
    rw [hcongr_sum, hcongr_prod]
    have hc2 : (-(2 * (p : ZMod (p ^ (3 * r))) ^ (2 * r))) ^ 2 = 0 := by
      have hsq : ((p : ZMod (p ^ (3 * r))) ^ (2 * r)) ^ 2 = 0 := by
        rw [← pow_mul]
        have : 2 * r * 2 = 4 * r := by omega
        rw [this]; exact hp4r
      linear_combination 4 * hsq
    rw [prod_one_add_eq_one_add_sum _ _ hc2]
    ring
  have hzero := mul_eq_zero_of_dvd_of_castHom_eq_zero (p := p) (a := 3 * r) (N := 3 * r + 3)
    (c := T (p ^ (r - 1)) m) hp.pos (by omega)
    (by have hsub : 3 * r + 3 - 3 * r = 3 := by omega
        rw [hsub]; exact hp3_dvd_T) _ hcast_diff
  rw [hT_eq]
  linear_combination hzero

private lemma theoremB_sum_eq {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr2 : 2 ≤ r) :
    ∑ m ∈ Finset.Icc 1 (p ^ (r - 1) - 1),
        ((T (p ^ r) (p * m) : ZMod (p ^ (3 * r + 3))) -
          (T (p ^ (r - 1)) m : ZMod (p ^ (3 * r + 3)))) = 0 := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (p ^ (r - 1) - 1))
    (fun m => p ^ (r - 2) ∣ m)]
  have hnot_top :
      ∑ m ∈ (Finset.Icc 1 (p ^ (r - 1) - 1)).filter (fun m => ¬ p ^ (r - 2) ∣ m),
          ((T (p ^ r) (p * m) : ZMod (p ^ (3 * r + 3))) -
            (T (p ^ (r - 1)) m : ZMod (p ^ (3 * r + 3)))) = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    have hm_lt : m < p ^ (r - 1) := by
      have : 1 ≤ p ^ (r - 1) := Nat.one_le_pow _ _ hp.pos
      omega
    rw [step_down_diff_zmod hp hr2 hm.1.1 hm_lt]
    have hr3 : 3 ≤ r := by
      by_contra hlt
      have hr_eq : r = 2 := by omega
      subst hr_eq
      exact hm.2 (by simp)
    let s := m.factorization p
    have hs_le : s ≤ r - 3 := by
      have hlt : s < r - 2 := by
        by_contra hge
        have hdvd_m : p ^ (r - 2) ∣ m :=
          (hp.pow_dvd_iff_le_factorization (by omega)).mpr (by omega)
        exact hm.2 hdvd_m
      omega
    have hs_dvd : p ^ s ∣ m := Nat.ordProj_dvd m p
    let u := m / p ^ s
    have hpm_eq : p * m = u * p ^ (s + 1) := by
      have hm_eq : m = p ^ s * u := (Nat.mul_div_cancel' hs_dvd).symm
      rw [hm_eq, pow_succ]
      ring
    have hcast_zero :
        ZMod.castHom (pow_dvd_pow p (by omega : s + 1 ≤ 3 * r + 3)) (ZMod (p ^ (s + 1)))
          (∑ j ∈ (Finset.range (p * m)).filter (fun j => ¬ p ∣ j),
            (j : ZMod (p ^ (3 * r + 3)))⁻¹ ^ 2) = 0 := by
      rw [map_sum]
      have hcongr :
          ∑ j ∈ (Finset.range (p * m)).filter (fun j => ¬ p ∣ j),
              ZMod.castHom (pow_dvd_pow p (by omega : s + 1 ≤ 3 * r + 3)) (ZMod (p ^ (s + 1)))
                ((j : ZMod (p ^ (3 * r + 3)))⁻¹ ^ 2) =
            ∑ j ∈ (Finset.range (u * p ^ (s + 1))).filter (fun j => ¬ p ∣ j),
              (j : ZMod (p ^ (s + 1)))⁻¹ ^ 2 := by
        rw [hpm_eq]
        refine Finset.sum_congr rfl fun j hj => ?_
        simp only [Finset.mem_filter] at hj
        rw [map_pow, castHom_inv_of_isUnit _ _ (isUnit_of_not_dvd_pow hp hj.2), map_natCast]
      rw [hcongr, sum_filter_range_mul_pow hp (by omega : 1 ≤ s + 1)]
      refine Finset.sum_eq_zero fun b _ => ?_
      have hblock :
          ∑ t ∈ U p (s + 1), ((b * p ^ (s + 1) + t : ℕ) : ZMod (p ^ (s + 1)))⁻¹ ^ 2 =
            ∑ t ∈ U p (s + 1), (t : ZMod (p ^ (s + 1)))⁻¹ ^ 2 := by
        refine Finset.sum_congr rfl fun t _ => ?_
        simp
      rw [hblock]
      exact sum_U_inv_sq_eq_zero hp hp5 (by omega)
    have hcoeff_dvd : p ^ (3 * r + 3 - (s + 1)) ∣ p ^ (2 * r) * T (p ^ (r - 1)) m := by
      have hT_dvd : p ^ (3 * (r - 1 - s)) ∣ T (p ^ (r - 1)) m :=
        pow_dvd_T hp (by omega) hm.1.1 hm_lt
      have hmul : p ^ (2 * r + 3 * (r - 1 - s)) ∣ p ^ (2 * r) * T (p ^ (r - 1)) m := by
        rw [pow_add]
        exact Nat.mul_dvd_mul_left _ hT_dvd
      exact dvd_trans (pow_dvd_pow p (by omega)) hmul
    have hzero := mul_eq_zero_of_dvd_of_castHom_eq_zero (p := p) (a := s + 1) (N := 3 * r + 3)
      (c := p ^ (2 * r) * T (p ^ (r - 1)) m) hp.pos (by omega) hcoeff_dvd _ hcast_zero
    have hzero' :
        ((p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) * (T (p ^ (r - 1)) m : ZMod (p ^ (3 * r + 3)))) *
          ∑ j ∈ (Finset.range (p * m)).filter (fun j => ¬ p ∣ j),
            (j : ZMod (p ^ (3 * r + 3)))⁻¹ ^ 2 = 0 := by
      simpa [Nat.cast_mul, Nat.cast_pow] using hzero
    calc
      -2 * ((p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) * (T (p ^ (r - 1)) m : ZMod (p ^ (3 * r + 3)))) *
            ∑ j ∈ (Finset.range (p * m)).filter (fun j => ¬ p ∣ j),
              (j : ZMod (p ^ (3 * r + 3)))⁻¹ ^ 2
          = -2 * (((p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) * (T (p ^ (r - 1)) m : ZMod (p ^ (3 * r + 3)))) *
              ∑ j ∈ (Finset.range (p * m)).filter (fun j => ¬ p ∣ j),
                (j : ZMod (p ^ (3 * r + 3)))⁻¹ ^ 2) := by ring
      _ = 0 := by rw [hzero', mul_zero]
  have htop :
      ∑ m ∈ (Finset.Icc 1 (p ^ (r - 1) - 1)).filter (fun m => p ^ (r - 2) ∣ m),
          ((T (p ^ r) (p * m) : ZMod (p ^ (3 * r + 3))) -
            (T (p ^ (r - 1)) m : ZMod (p ^ (3 * r + 3)))) = 0 := by
    have hbij :
        ∑ m ∈ (Finset.Icc 1 (p ^ (r - 1) - 1)).filter (fun m => p ^ (r - 2) ∣ m),
            ((T (p ^ r) (p * m) : ZMod (p ^ (3 * r + 3))) -
              (T (p ^ (r - 1)) m : ZMod (p ^ (3 * r + 3)))) =
          ∑ u ∈ Finset.Icc 1 (p - 1),
            ((T (p ^ r) (p * (u * p ^ (r - 2))) : ZMod (p ^ (3 * r + 3))) -
              (T (p ^ (r - 1)) (u * p ^ (r - 2)) : ZMod (p ^ (3 * r + 3)))) := by
      symm
      refine Finset.sum_nbij (fun u => u * p ^ (r - 2)) ?_ ?_ ?_ ?_
      · intro u hu
        simp only [Finset.mem_Icc, Finset.mem_filter] at hu ⊢
        have hpr1 : p ^ (r - 1) = p * p ^ (r - 2) := by
          rw [← _root_.pow_succ']
          congr 1
          omega
        have hlt : u * p ^ (r - 2) < p ^ (r - 1) := by
          rw [hpr1]
          exact Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos hp.pos _)
        exact ⟨⟨Nat.mul_pos (by omega) (pow_pos hp.pos _), by omega⟩, dvd_mul_left _ _⟩
      · intro a _ b _ hab
        dsimp at hab
        exact Nat.mul_right_cancel (pow_pos hp.pos _) hab
      · intro m hm
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm
        obtain ⟨u, rfl⟩ := hm.2
        have hu1 : 1 ≤ u := by
          by_contra hu0
          have : u = 0 := by omega
          subst this; simp at hm
        have hpr1 : p ^ (r - 1) = p * p ^ (r - 2) := by
          rw [← _root_.pow_succ']
          congr 1
          omega
        have hlt : p ^ (r - 2) * u < p * p ^ (r - 2) := by
          have : 1 ≤ p ^ (r - 1) := Nat.one_le_pow _ _ hp.pos
          omega
        have hu_lt : u < p := by
          rw [mul_comm] at hlt
          exact (Nat.mul_lt_mul_right (pow_pos hp.pos _)).mp hlt
        exact ⟨u, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hu1, by omega⟩), by dsimp; ring⟩
      · intro _ _; rfl
    rw [hbij]
    let C_z : ZMod (p ^ r) := ∑ t ∈ U p (r - 1), (t : ZMod (p ^ r))⁻¹ ^ 2
    let C_nat : ℕ := C_z.val
    have : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
    have hC_dvd : p ^ (r - 1) ∣ C_nat := by
      have hcast_C :
          ZMod.castHom (pow_dvd_pow p (by omega : r - 1 ≤ r)) (ZMod (p ^ (r - 1))) C_z = 0 := by
        simp only [C_z, map_sum]
        have hcongr :
            ∑ t ∈ U p (r - 1),
              ZMod.castHom (pow_dvd_pow p (by omega : r - 1 ≤ r)) (ZMod (p ^ (r - 1)))
                ((t : ZMod (p ^ r))⁻¹ ^ 2) =
              ∑ t ∈ U p (r - 1), (t : ZMod (p ^ (r - 1)))⁻¹ ^ 2 := by
          refine Finset.sum_congr rfl fun t ht => ?_
          simp only [U, Finset.mem_filter] at ht
          rw [map_pow, castHom_inv_of_isUnit _ _ (isUnit_of_not_dvd_pow hp ht.2), map_natCast]
        rw [hcongr]
        exact sum_U_inv_sq_eq_zero hp hp5 (by omega)
      have hval : (C_nat : ZMod (p ^ (r - 1))) = 0 := by
        simpa [C_nat, ZMod.natCast_zmod_val] using hcast_C
      exact (ZMod.natCast_eq_zero_iff C_nat (p ^ (r - 1))).mp hval
    have hterm_u :
        ∀ u ∈ Finset.Icc 1 (p - 1),
          (T (p ^ r) (p * (u * p ^ (r - 2))) : ZMod (p ^ (3 * r + 3))) -
            (T (p ^ (r - 1)) (u * p ^ (r - 2)) : ZMod (p ^ (3 * r + 3))) =
          -2 * ((p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) * (C_nat : ZMod (p ^ (3 * r + 3)))) *
            ((u : ZMod (p ^ (3 * r + 3))) * (T (p ^ (r - 1)) (u * p ^ (r - 2)) : ZMod (p ^ (3 * r + 3)))) := by
      intro u hu
      simp only [Finset.mem_Icc] at hu
      have hpr1 : p ^ (r - 1) = p * p ^ (r - 2) := by
        rw [← _root_.pow_succ']
        congr 1
        omega
      have hm_lt : u * p ^ (r - 2) < p ^ (r - 1) := by
        rw [hpr1]
        exact Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos hp.pos _)
      have hm1 : 1 ≤ u * p ^ (r - 2) := Nat.mul_pos (by omega) (pow_pos hp.pos _)
      rw [step_down_diff_zmod hp hr2 hm1 hm_lt]
      have hpm_eq : p * (u * p ^ (r - 2)) = u * p ^ (r - 1) := by rw [hpr1]; ring
      have hcast_diff :
          ZMod.castHom (pow_dvd_pow p (by omega : r ≤ 3 * r + 3)) (ZMod (p ^ r))
            ((∑ j ∈ (Finset.range (p * (u * p ^ (r - 2)))).filter (fun j => ¬ p ∣ j),
                (j : ZMod (p ^ (3 * r + 3)))⁻¹ ^ 2) -
              (u : ZMod (p ^ (3 * r + 3))) * (C_nat : ZMod (p ^ (3 * r + 3)))) = 0 := by
        rw [map_sub, map_sum, map_mul, map_natCast, map_natCast]
        have hcongr :
            ∑ j ∈ (Finset.range (p * (u * p ^ (r - 2)))).filter (fun j => ¬ p ∣ j),
                ZMod.castHom (pow_dvd_pow p (by omega : r ≤ 3 * r + 3)) (ZMod (p ^ r))
                  ((j : ZMod (p ^ (3 * r + 3)))⁻¹ ^ 2) =
              ∑ j ∈ (Finset.range (u * p ^ (r - 1))).filter (fun j => ¬ p ∣ j),
                (j : ZMod (p ^ r))⁻¹ ^ 2 := by
          rw [hpm_eq]
          refine Finset.sum_congr rfl fun j hj => ?_
          simp only [Finset.mem_filter] at hj
          rw [map_pow, castHom_inv_of_isUnit _ _ (isUnit_of_not_dvd_pow hp hj.2), map_natCast]
        rw [hcongr, sum_block_inv_sq_zmod_pr hp hp5 hr2]
        have hC_eq : (C_nat : ZMod (p ^ r)) = C_z := ZMod.natCast_zmod_val C_z
        rw [hC_eq, sub_self]
      have hT_dvd : p ^ 3 ∣ T (p ^ (r - 1)) (u * p ^ (r - 2)) := by
        have h := pow_dvd_T hp (by omega) hm1 hm_lt
        have hlt_s : (u * p ^ (r - 2)).factorization p < r - 1 := by
          have hle : p ^ ((u * p ^ (r - 2)).factorization p) ≤ u * p ^ (r - 2) :=
            Nat.le_of_dvd (by omega) (Nat.ordProj_dvd _ p)
          exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp (lt_of_le_of_lt hle hm_lt)
        exact dvd_trans (pow_dvd_pow p (by omega)) h
      have hcoeff_dvd :
          p ^ (3 * r + 3 - r) ∣ p ^ (2 * r) * T (p ^ (r - 1)) (u * p ^ (r - 2)) := by
        have hmul : p ^ (2 * r + 3) ∣ p ^ (2 * r) * T (p ^ (r - 1)) (u * p ^ (r - 2)) := by
          rw [pow_add]; exact Nat.mul_dvd_mul_left _ hT_dvd
        exact dvd_trans (pow_dvd_pow p (by omega)) hmul
      have hzero := mul_eq_zero_of_dvd_of_castHom_eq_zero (p := p) (a := r) (N := 3 * r + 3)
        (c := p ^ (2 * r) * T (p ^ (r - 1)) (u * p ^ (r - 2))) hp.pos (by omega) hcoeff_dvd _ hcast_diff
      have hzero' :
          ((p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) *
              (T (p ^ (r - 1)) (u * p ^ (r - 2)) : ZMod (p ^ (3 * r + 3)))) *
            ((∑ j ∈ (Finset.range (p * (u * p ^ (r - 2)))).filter (fun j => ¬ p ∣ j),
                (j : ZMod (p ^ (3 * r + 3)))⁻¹ ^ 2) -
              (u : ZMod (p ^ (3 * r + 3))) * (C_nat : ZMod (p ^ (3 * r + 3)))) = 0 := by
        simpa [Nat.cast_mul, Nat.cast_pow] using hzero
      linear_combination -2 * hzero'
    rw [Finset.sum_congr rfl hterm_u, ← Finset.mul_sum]
    have hcast_sum_zero :
        ZMod.castHom (pow_dvd_pow p (by omega : 4 ≤ 3 * r + 3)) (ZMod (p ^ 4))
          (∑ u ∈ Finset.Icc 1 (p - 1),
            (u : ZMod (p ^ (3 * r + 3))) *
              (T (p ^ (r - 1)) (u * p ^ (r - 2)) : ZMod (p ^ (3 * r + 3)))) = 0 := by
      rw [map_sum]
      have hcongr :
          ∑ u ∈ Finset.Icc 1 (p - 1),
              ZMod.castHom (pow_dvd_pow p (by omega : 4 ≤ 3 * r + 3)) (ZMod (p ^ 4))
                ((u : ZMod (p ^ (3 * r + 3))) *
                  (T (p ^ (r - 1)) (u * p ^ (r - 2)) : ZMod (p ^ (3 * r + 3)))) =
            -((p : ZMod (p ^ 4)) ^ 3 * ∑ u ∈ Finset.Icc 1 (p - 1), (u : ZMod (p ^ 4))⁻¹ ^ 2) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun u hu => ?_
        simp only [Finset.mem_Icc] at hu
        rw [map_mul, map_natCast, map_natCast]
        have hT4 :
            (T (p ^ (r - 1)) (u * p ^ (r - 2)) : ZMod (p ^ 4)) =
              -((p : ZMod (p ^ 4)) ^ 3 * (u : ZMod (p ^ 4))⁻¹ ^ 3) := by
          have h := T_top_slice_mod_p4 hp hu.1 hu.2 (r - 1) (by omega)
          have hsub : r - 1 - 1 = r - 2 := by omega
          rwa [hsub] at h
        rw [hT4]
        have hu_ndvd : ¬ p ∣ u := Nat.not_dvd_of_pos_of_lt hu.1 (by omega)
        have hu_inv : (u : ZMod (p ^ 4)) * (u : ZMod (p ^ 4))⁻¹ = 1 :=
          mul_inv_of_not_dvd_pow hp hu_ndvd
        have hu13 : (u : ZMod (p ^ 4)) * (u : ZMod (p ^ 4))⁻¹ ^ 3 = (u : ZMod (p ^ 4))⁻¹ ^ 2 := by
          have : (3 : ℕ) = 1 + 2 := rfl
          rw [this, pow_add, pow_one, ← mul_assoc, hu_inv, one_mul]
        calc
          (u : ZMod (p ^ 4)) * -((p : ZMod (p ^ 4)) ^ 3 * (u : ZMod (p ^ 4))⁻¹ ^ 3)
              = -((p : ZMod (p ^ 4)) ^ 3 * ((u : ZMod (p ^ 4)) * (u : ZMod (p ^ 4))⁻¹ ^ 3)) := by
                ring
          _ = -((p : ZMod (p ^ 4)) ^ 3 * (u : ZMod (p ^ 4))⁻¹ ^ 2) := by rw [hu13]
      rw [hcongr]
      have hcast_p :
          ZMod.castHom (dvd_pow_self p (by norm_num : (4 : ℕ) ≠ 0)) (ZMod p)
            (∑ u ∈ Finset.Icc 1 (p - 1), (u : ZMod (p ^ 4))⁻¹ ^ 2) = 0 := by
        rw [map_sum]
        have hU1 : Finset.Icc 1 (p - 1) = U p 1 := by
          ext u
          simp only [Finset.mem_Icc, U, Finset.mem_filter, Finset.mem_range, pow_one]
          constructor
          · rintro ⟨hu1, hule⟩
            exact ⟨by omega, Nat.not_dvd_of_pos_of_lt hu1 (by omega)⟩
          · rintro ⟨hult, hndvd⟩
            have hu1 : 1 ≤ u := Nat.pos_of_ne_zero fun h0 => hndvd (h0 ▸ dvd_zero p)
            exact ⟨hu1, by omega⟩
        have hcongr2 :
            ∑ u ∈ Finset.Icc 1 (p - 1),
              ZMod.castHom (dvd_pow_self p (by norm_num : (4 : ℕ) ≠ 0)) (ZMod p)
                ((u : ZMod (p ^ 4))⁻¹ ^ 2) =
              ∑ u ∈ U p 1, (u : ZMod p)⁻¹ ^ 2 := by
          rw [hU1]
          refine Finset.sum_congr rfl fun u hu => ?_
          simp only [U, Finset.mem_filter] at hu
          rw [map_pow, castHom_inv_of_isUnit _ _ (isUnit_of_not_dvd_pow hp hu.2), map_natCast]
        rw [hcongr2]
        have h0 := congr_arg (ZMod.castHom (show p ∣ p ^ 1 by simp) (ZMod p))
          (sum_U_inv_sq_eq_zero hp hp5 (le_refl 1))
        rw [map_sum, map_zero] at h0
        rw [← h0]
        refine Finset.sum_congr rfl fun u hu => ?_
        simp only [U, Finset.mem_filter] at hu
        rw [map_pow, castHom_inv_of_isUnit _ _ (isUnit_of_not_dvd_pow hp hu.2), map_natCast]
      have hz := mul_eq_zero_of_dvd_of_castHom_p_eq_zero (p := p) (N := 4) (c := p ^ 3)
        hp.pos (by omega) (dvd_refl _) _ hcast_p
      simpa [Nat.cast_pow] using hz
    have hcoeff_dvd : p ^ (3 * r + 3 - 4) ∣ p ^ (2 * r) * C_nat := by
      have hmul : p ^ (2 * r + (r - 1)) ∣ p ^ (2 * r) * C_nat := by
        rw [pow_add]; exact Nat.mul_dvd_mul_left _ hC_dvd
      exact dvd_trans (pow_dvd_pow p (by omega)) hmul
    have hzero := mul_eq_zero_of_dvd_of_castHom_eq_zero (p := p) (a := 4) (N := 3 * r + 3)
      (c := p ^ (2 * r) * C_nat) hp.pos (by omega) hcoeff_dvd _ hcast_sum_zero
    have hzero' :
        ((p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) * (C_nat : ZMod (p ^ (3 * r + 3)))) *
          ∑ u ∈ Finset.Icc 1 (p - 1),
            (u : ZMod (p ^ (3 * r + 3))) *
              (T (p ^ (r - 1)) (u * p ^ (r - 2)) : ZMod (p ^ (3 * r + 3))) = 0 := by
      simpa [Nat.cast_mul, Nat.cast_pow] using hzero
    calc
      -2 * ((p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) * (C_nat : ZMod (p ^ (3 * r + 3)))) *
            ∑ u ∈ Finset.Icc 1 (p - 1),
              (u : ZMod (p ^ (3 * r + 3))) *
                (T (p ^ (r - 1)) (u * p ^ (r - 2)) : ZMod (p ^ (3 * r + 3)))
          = -2 * (((p : ZMod (p ^ (3 * r + 3))) ^ (2 * r) * (C_nat : ZMod (p ^ (3 * r + 3)))) *
              ∑ u ∈ Finset.Icc 1 (p - 1),
                (u : ZMod (p ^ (3 * r + 3))) *
                  (T (p ^ (r - 1)) (u * p ^ (r - 2)) : ZMod (p ^ (3 * r + 3)))) := by ring
      _ = 0 := by rw [hzero', mul_zero]
  rw [htop, hnot_top, add_zero]

private lemma a_congr_zmod {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr2 : 2 ≤ r) :
    (OeisA212334.a (p ^ r) : ZMod (p ^ (3 * r + 3))) =
      (OeisA212334.a (p ^ (r - 1)) : ZMod (p ^ (3 * r + 3))) := by
  have hpr_ne : p ^ r ≠ 0 := pow_ne_zero r hp.ne_zero
  have hpr1_ne : p ^ (r - 1) ≠ 0 := pow_ne_zero (r - 1) hp.ne_zero
  have ha_r :
      OeisA212334.a (p ^ r) =
        ∑ k ∈ (Finset.range (p ^ r)).filter (fun k => p ∣ k), T (p ^ r) k +
          ∑ k ∈ U p r, T (p ^ r) k := by
    rw [OeisA212334.a, if_neg hpr_ne]
    exact (Finset.sum_filter_add_sum_filter_not (Finset.range (p ^ r)) (fun k => p ∣ k) (T (p ^ r))).symm
  have hdiv_bij :
      ∑ k ∈ (Finset.range (p ^ r)).filter (fun k => p ∣ k), T (p ^ r) k =
        ∑ m ∈ Finset.range (p ^ (r - 1)), T (p ^ r) (p * m) := by
    symm
    refine Finset.sum_nbij (fun m => p * m) ?_ ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_range, Finset.mem_filter] at hm ⊢
      have hpr : p ^ r = p * p ^ (r - 1) := by rw [← _root_.pow_succ', Nat.sub_add_cancel (by omega)]
      exact ⟨by rw [hpr]; exact Nat.mul_lt_mul_of_pos_left hm hp.pos, dvd_mul_right p m⟩
    · intro a _ b _ hab
      dsimp at hab
      exact Nat.mul_left_cancel hp.pos hab
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨m, rfl⟩ := hk.2
      have hpr : p ^ r = p * p ^ (r - 1) := by rw [← _root_.pow_succ', Nat.sub_add_cancel (by omega)]
      have hm_lt : m < p ^ (r - 1) := by
        rw [hpr] at hk
        exact (Nat.mul_lt_mul_left hp.pos).mp hk.1
      exact ⟨m, Finset.mem_coe.mpr (Finset.mem_range.mpr hm_lt), rfl⟩
    · intro _ _; rfl
  have ha_r1 :
      OeisA212334.a (p ^ (r - 1)) = ∑ m ∈ Finset.range (p ^ (r - 1)), T (p ^ (r - 1)) m := by
    rw [OeisA212334.a, if_neg hpr1_ne]; rfl
  rw [ha_r, hdiv_bij, ha_r1, Nat.cast_add, Nat.cast_sum, Nat.cast_sum, Nat.cast_sum]
  rw [theoremA_sum_zero hp hp5 hr2, add_zero]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  have hrange : Finset.range (p ^ (r - 1)) = Finset.range ((p ^ (r - 1) - 1) + 1) := by
    have : 1 ≤ p ^ (r - 1) := Nat.one_le_pow _ _ hp.pos
    congr 1; omega
  rw [hrange, Finset.sum_range_succ']
  have h0 :
      (T (p ^ r) (p * 0) : ZMod (p ^ (3 * r + 3))) -
        (T (p ^ (r - 1)) 0 : ZMod (p ^ (3 * r + 3))) = 0 := by
    simp [T]
  rw [h0, add_zero]
  have hshift :
      ∑ k ∈ Finset.range (p ^ (r - 1) - 1),
          ((T (p ^ r) (p * (k + 1)) : ZMod (p ^ (3 * r + 3))) -
            (T (p ^ (r - 1)) (k + 1) : ZMod (p ^ (3 * r + 3)))) =
        ∑ m ∈ Finset.Icc 1 (p ^ (r - 1) - 1),
          ((T (p ^ r) (p * m) : ZMod (p ^ (3 * r + 3))) -
            (T (p ^ (r - 1)) m : ZMod (p ^ (3 * r + 3)))) := by
    refine Finset.sum_nbij (fun k => k + 1) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_range, Finset.mem_Icc] at hk ⊢
      omega
    · intro a _ b _ hab
      dsimp at hab; omega
    · intro m hm
      simp only [Finset.mem_coe, Finset.mem_Icc] at hm
      exact ⟨m - 1, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp; omega⟩
    · intro _ _; rfl
  rw [hshift]
  exact theoremB_sum_eq hp hp5 hr2

end OeisA212334Conj2Proof

theorem OMA.solution : type_of% @OeisA212334.conjecture_2 := by
  intro p r hp hp5 hr2
  have hcast := OeisA212334Conj2Proof.a_congr_zmod hp hp5 hr2
  have hval := congr_arg ZMod.val hcast
  have : NeZero (p ^ (3 * r + 3)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rwa [ZMod.val_natCast, ZMod.val_natCast] at hval
