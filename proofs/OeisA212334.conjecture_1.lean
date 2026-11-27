import FormalConjectures.OEIS.«212334»

/-!
Proof of `OeisA212334.conjecture_1`: `a p % (p ^ 5) = 1` for all primes `p ≥ 5`.
-/

namespace OeisA212334Conj1Proof

open Nat

private lemma isUnit_natCast_zmod {n k : ℕ} (hk : k.Coprime n) : IsUnit (k : ZMod n) :=
  ⟨ZMod.unitOfCoprime k hk, ZMod.coe_unitOfCoprime k hk⟩

private lemma mul_inv_natCast_zmod {n k : ℕ} (hk : k.Coprime n) :
    (k : ZMod n) * (k : ZMod n)⁻¹ = 1 :=
  ZMod.mul_inv_of_unit (k : ZMod n) (isUnit_natCast_zmod hk)

private lemma castHom_inv_of_isUnit {m n : ℕ} (hmn : m ∣ n) (x : ZMod n) (hx : IsUnit x) :
    ZMod.castHom hmn (ZMod m) x⁻¹ = (ZMod.castHom hmn (ZMod m) x)⁻¹ := by
  let f := ZMod.castHom hmn (ZMod m)
  have h1 : f x * f x⁻¹ = 1 := by rw [← map_mul, ZMod.mul_inv_of_unit x hx, map_one]
  have h2 : f x * (f x)⁻¹ = 1 := ZMod.mul_inv_of_unit (f x) (hx.map f)
  calc
    f x⁻¹ = f x⁻¹ * (f x * (f x)⁻¹) := by rw [h2, mul_one]
    _ = (f x * f x⁻¹) * (f x)⁻¹ := by ring
    _ = (f x)⁻¹ := by rw [h1, one_mul]

private lemma pow_mul_eq_zero_of_castHom_eq_zero {p a b : ℕ} (hp : 0 < p)
    (x : ZMod (p ^ (a + b)))
    (hx : ZMod.castHom (pow_dvd_pow p (Nat.le_add_right a b)) (ZMod (p ^ a)) x = 0) :
    (p : ZMod (p ^ (a + b))) ^ b * x = 0 := by
  have : NeZero (p ^ (a + b)) := ⟨pow_ne_zero _ (Nat.ne_of_gt hp)⟩
  have hval : (x.val : ZMod (p ^ a)) = 0 := by
    simpa [ZMod.natCast_zmod_val] using hx
  obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff x.val (p ^ a)).mp hval
  have hx_eq : x = ((p ^ a * q : ℕ) : ZMod (p ^ (a + b))) := by
    rw [← hq, ZMod.natCast_zmod_val]
  rw [hx_eq]
  have hcast :
      (p : ZMod (p ^ (a + b))) ^ b * ((p ^ a * q : ℕ) : ZMod (p ^ (a + b))) =
        ((p ^ (a + b) * q : ℕ) : ZMod (p ^ (a + b))) := by
    push_cast
    rw [pow_add]
    ring
  rw [hcast, Nat.cast_mul, ZMod.natCast_self, zero_mul]

private lemma pow_mul_eq_zero_of_castHom_p {p b : ℕ} (hp : 0 < p) (hb : 1 ≤ b)
    (x : ZMod (p ^ b))
    (hx : ZMod.castHom (dvd_pow_self p (by omega : b ≠ 0)) (ZMod p) x = 0) :
    (p : ZMod (p ^ b)) ^ (b - 1) * x = 0 := by
  have : NeZero (p ^ b) := ⟨pow_ne_zero _ (Nat.ne_of_gt hp)⟩
  have hval : (x.val : ZMod p) = 0 := by
    simpa [ZMod.natCast_zmod_val] using hx
  obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff x.val p).mp hval
  have hx_eq : x = ((p * q : ℕ) : ZMod (p ^ b)) := by
    rw [← hq, ZMod.natCast_zmod_val]
  rw [hx_eq]
  have hcast :
      (p : ZMod (p ^ b)) ^ (b - 1) * ((p * q : ℕ) : ZMod (p ^ b)) =
        ((p ^ b * q : ℕ) : ZMod (p ^ b)) := by
    push_cast
    have hpow : (p : ZMod (p ^ b)) ^ (b - 1) * (p : ZMod (p ^ b)) = (p : ZMod (p ^ b)) ^ b := by
      rw [← pow_succ, Nat.sub_add_cancel hb]
    calc
      (p : ZMod (p ^ b)) ^ (b - 1) * ((p : ZMod (p ^ b)) * (q : ZMod (p ^ b)))
          = ((p : ZMod (p ^ b)) ^ (b - 1) * (p : ZMod (p ^ b))) * (q : ZMod (p ^ b)) := by ring
      _ = (p : ZMod (p ^ b)) ^ b * (q : ZMod (p ^ b)) := by rw [hpow]
  rw [hcast, Nat.cast_mul, ZMod.natCast_self, zero_mul]

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
    ((k.factorial : ℤ) ^ 4) *
        ((n.choose k * (n - 1).choose k * (n + k - 1).choose k ^ 2 : ℕ) : ℤ) =
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

private lemma prod_p2_sub_i2_sq_mod (p n : ℕ) :
    ((p : ℤ) ^ 2) ∣
      (∏ i ∈ Finset.Icc 1 n, ((p : ℤ) ^ 2 - (i : ℤ) ^ 2) ^ 2) - (n.factorial : ℤ) ^ 4 := by
  have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self (p ^ 2)
  have hcast :
      ((∏ i ∈ Finset.Icc 1 n, ((p : ℤ) ^ 2 - (i : ℤ) ^ 2) ^ 2 : ℤ) : ZMod (p ^ 2)) =
        (((n.factorial : ℤ) ^ 4 : ℤ) : ZMod (p ^ 2)) := by
    push_cast
    have hprod :
        ∏ i ∈ Finset.Icc 1 n, ((p : ZMod (p ^ 2)) ^ 2 - (i : ZMod (p ^ 2)) ^ 2) ^ 2 =
          ∏ i ∈ Finset.Icc 1 n, (i : ZMod (p ^ 2)) ^ 4 := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hp2]
      ring
    rw [hprod, Finset.prod_pow, ← prod_Icc_eq_factorial n]
    push_cast
    rfl
  have hcast' :
      (((∏ i ∈ Finset.Icc 1 n, ((p : ℤ) ^ 2 - (i : ℤ) ^ 2) ^ 2) - (n.factorial : ℤ) ^ 4 : ℤ) :
        ZMod (p ^ 2)) = 0 := by
    rw [Int.cast_sub, hcast, sub_self]
  have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ 2)).mp hcast'
  simpa [Nat.cast_pow] using hdvd

private lemma term_eq_zmod_p5 {p k : ℕ} (hp : p.Prime) (hk1 : 1 ≤ k) (hkp : k ≤ p - 1) :
    ((p.choose k * (p - 1).choose k * (p + k - 1).choose k ^ 2 : ℕ) : ZMod (p ^ 5)) =
      (p : ZMod (p ^ 5)) ^ 4 * (k : ZMod (p ^ 5))⁻¹ ^ 4 -
        (p : ZMod (p ^ 5)) ^ 3 * (k : ZMod (p ^ 5))⁻¹ ^ 3 := by
  have hk_cop : k.Coprime (p ^ 5) :=
    ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk1 (by omega))).symm).pow_right 5
  have hkm1_cop : (k - 1).factorial.Coprime (p ^ 5) :=
    ((hp.coprime_iff_not_dvd.mpr (hp.dvd_factorial.not.mpr (by omega))).symm).pow_right 5
  have hmain_int := term_prod_int hk1 hkp
  obtain ⟨q, hq⟩ := prod_p2_sub_i2_sq_mod p (k - 1)
  have hprod_eq :
      ∏ i ∈ Finset.Icc 1 (k - 1), ((p : ℤ) ^ 2 - (i : ℤ) ^ 2) ^ 2 =
        ((k - 1).factorial : ℤ) ^ 4 + (p : ℤ) ^ 2 * q := by linarith
  rw [hprod_eq] at hmain_int
  have hcast := congr_arg (Int.cast (R := ZMod (p ^ 5))) hmain_int
  have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := by
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self (p ^ 5)
  push_cast at hcast
  have hfac_split : (k.factorial : ZMod (p ^ 5)) = (k : ZMod (p ^ 5)) * ((k - 1).factorial : ZMod (p ^ 5)) := by
    have hnat : k.factorial = k * (k - 1).factorial := by
      cases k with
      | zero => omega
      | succ j => exact Nat.factorial_succ j
    rw [hnat, Nat.cast_mul]
  have hkm1_inv : ((k - 1).factorial : ZMod (p ^ 5)) * ((k - 1).factorial : ZMod (p ^ 5))⁻¹ = 1 :=
    mul_inv_natCast_zmod hkm1_cop
  have hk_inv : (k : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹ = 1 :=
    mul_inv_natCast_zmod hk_cop
  set T : ZMod (p ^ 5) := ((p.choose k * (p - 1).choose k * (p + k - 1).choose k ^ 2 : ℕ) : ZMod (p ^ 5))
  have hcast' :
      ((k : ZMod (p ^ 5)) ^ 4 * T) * ((k - 1).factorial : ZMod (p ^ 5)) ^ 4 =
        ((p : ZMod (p ^ 5)) ^ 4 - (p : ZMod (p ^ 5)) ^ 3 * (k : ZMod (p ^ 5))) *
          ((k - 1).factorial : ZMod (p ^ 5)) ^ 4 := by
    have hT : T = (p.choose k : ZMod (p ^ 5)) * ((p - 1).choose k : ZMod (p ^ 5)) *
        ((p + k - 1).choose k : ZMod (p ^ 5)) ^ 2 := by
      simp [T]
    rw [hfac_split] at hcast
    rw [hT]
    linear_combination hcast + (((p : ZMod (p ^ 5)) - (k : ZMod (p ^ 5))) * (q : ZMod (p ^ 5))) * hp5
  have hstep1 :
      (k : ZMod (p ^ 5)) ^ 4 * T =
        (p : ZMod (p ^ 5)) ^ 4 - (p : ZMod (p ^ 5)) ^ 3 * (k : ZMod (p ^ 5)) := by
    have hunit4 :
        ((k - 1).factorial : ZMod (p ^ 5)) ^ 4 * (((k - 1).factorial : ZMod (p ^ 5))⁻¹) ^ 4 = 1 := by
      rw [← mul_pow, hkm1_inv, one_pow]
    have h2 := congr_arg (fun z => z * (((k - 1).factorial : ZMod (p ^ 5))⁻¹) ^ 4) hcast'
    calc
      (k : ZMod (p ^ 5)) ^ 4 * T
          = ((k : ZMod (p ^ 5)) ^ 4 * T) *
              (((k - 1).factorial : ZMod (p ^ 5)) ^ 4 * (((k - 1).factorial : ZMod (p ^ 5))⁻¹) ^ 4) := by
            rw [hunit4, mul_one]
      _ = (((k : ZMod (p ^ 5)) ^ 4 * T) * ((k - 1).factorial : ZMod (p ^ 5)) ^ 4) *
            (((k - 1).factorial : ZMod (p ^ 5))⁻¹) ^ 4 := by ring
      _ = (((p : ZMod (p ^ 5)) ^ 4 - (p : ZMod (p ^ 5)) ^ 3 * (k : ZMod (p ^ 5))) *
            ((k - 1).factorial : ZMod (p ^ 5)) ^ 4) *
            (((k - 1).factorial : ZMod (p ^ 5))⁻¹) ^ 4 := h2
      _ = ((p : ZMod (p ^ 5)) ^ 4 - (p : ZMod (p ^ 5)) ^ 3 * (k : ZMod (p ^ 5))) *
            (((k - 1).factorial : ZMod (p ^ 5)) ^ 4 * (((k - 1).factorial : ZMod (p ^ 5))⁻¹) ^ 4) := by
            ring
      _ = (p : ZMod (p ^ 5)) ^ 4 - (p : ZMod (p ^ 5)) ^ 3 * (k : ZMod (p ^ 5)) := by
            rw [hunit4, mul_one]
  have hmul := congr_arg (fun z => z * (k : ZMod (p ^ 5))⁻¹ ^ 4) hstep1
  have hk4 : (k : ZMod (p ^ 5)) ^ 4 * (k : ZMod (p ^ 5))⁻¹ ^ 4 = 1 := by
    rw [← mul_pow, hk_inv, one_pow]
  have hk1_pow : (k : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹ ^ 4 = (k : ZMod (p ^ 5))⁻¹ ^ 3 := by
    have : (4 : ℕ) = 1 + 3 := rfl
    rw [this, pow_add, pow_one, ← mul_assoc, hk_inv, one_mul]
  calc
    T = ((k : ZMod (p ^ 5)) ^ 4 * T) * (k : ZMod (p ^ 5))⁻¹ ^ 4 := by
          calc
            T = T * ((k : ZMod (p ^ 5)) ^ 4 * (k : ZMod (p ^ 5))⁻¹ ^ 4) := by rw [hk4, mul_one]
            _ = ((k : ZMod (p ^ 5)) ^ 4 * T) * (k : ZMod (p ^ 5))⁻¹ ^ 4 := by ring
    _ = ((p : ZMod (p ^ 5)) ^ 4 - (p : ZMod (p ^ 5)) ^ 3 * (k : ZMod (p ^ 5))) *
          (k : ZMod (p ^ 5))⁻¹ ^ 4 := hmul
    _ = (p : ZMod (p ^ 5)) ^ 4 * (k : ZMod (p ^ 5))⁻¹ ^ 4 -
          (p : ZMod (p ^ 5)) ^ 3 * ((k : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹ ^ 4) := by ring
    _ = (p : ZMod (p ^ 5)) ^ 4 * (k : ZMod (p ^ 5))⁻¹ ^ 4 -
          (p : ZMod (p ^ 5)) ^ 3 * (k : ZMod (p ^ 5))⁻¹ ^ 3 := by rw [hk1_pow]

private lemma sum_inv_pow_eq_zero_zmod_p {p e : ℕ} (hp : p.Prime) (he0 : 0 < e) (he : e < p - 1) :
    ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod p)⁻¹ ^ e = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hsum_univ :
      ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod p)⁻¹ ^ e = ∑ x : ZMod p, x⁻¹ ^ e := by
    have hrange :
        ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod p)⁻¹ ^ e =
          ∑ k ∈ Finset.range p, (k : ZMod p)⁻¹ ^ e := by
      have hp_eq : Finset.range p = Finset.range ((p - 1) + 1) := by
        congr 1; omega
      rw [hp_eq, Finset.sum_range_succ']
      simp only [Nat.cast_zero, inv_zero, zero_pow (Nat.ne_of_gt he0), add_zero]
      refine Finset.sum_nbij (fun k => k - 1) ?_ ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
        omega
      · intro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb
        dsimp at hab
        omega
      · intro j hj
        simp only [Finset.mem_coe, Finset.mem_range] at hj
        exact ⟨j + 1, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), by dsimp⟩
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        have : k - 1 + 1 = k := by omega
        rw [this]
    rw [hrange]
    refine Finset.sum_nbij (fun k => (k : ZMod p)) ?_ ?_ ?_ ?_
    · intro k _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_range] at ha hb
      dsimp at hab
      have h1 : ((a : ZMod p)).val = a := ZMod.val_natCast_of_lt ha
      have h2 : ((b : ZMod p)).val = b := ZMod.val_natCast_of_lt hb
      rw [← h1, ← h2, hab]
    · intro x _
      exact ⟨x.val, Finset.mem_coe.mpr (Finset.mem_range.mpr (ZMod.val_lt x)),
        ZMod.natCast_zmod_val x⟩
    · intro k _; rfl
  rw [hsum_univ]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units p]
  have hge_ne : (g : ZMod p) ^ e ≠ 1 := by
    intro h1
    have hgu : g ^ e = 1 := by
      ext
      simpa using h1
    have hdvd : orderOf g ∣ e := orderOf_dvd_of_pow_eq_one hgu
    rw [hord] at hdvd
    exact Nat.not_dvd_of_pos_of_lt he0 he hdvd
  have hginv_ne : (g : ZMod p)⁻¹ ^ e ≠ 1 := by
    intro h1
    apply hge_ne
    have hmul : (g : ZMod p)⁻¹ ^ e * (g : ZMod p) ^ e = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ g.ne_zero, one_pow]
    rwa [h1, one_mul] at hmul
  have hshift :
      ∑ x : ZMod p, x⁻¹ ^ e = (g : ZMod p)⁻¹ ^ e * ∑ x : ZMod p, x⁻¹ ^ e := by
    rw [Finset.mul_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft₀ (g : ZMod p) g.ne_zero)
      (fun x => (g : ZMod p)⁻¹ ^ e * x⁻¹ ^ e) (fun y => y⁻¹ ^ e) fun x => ?_).symm
    simp only [Equiv.mulLeft₀_apply, mul_inv, mul_pow]
  have hzero : ((g : ZMod p)⁻¹ ^ e - 1) * ∑ x : ZMod p, x⁻¹ ^ e = 0 := by
    linear_combination -hshift
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (sub_eq_zero.mp h) hginv_ne
  · exact h

private lemma one_add_mul_p_pow {p : ℕ} (x : ZMod (p ^ 2)) :
    ∀ n : ℕ, (1 + (p : ZMod (p ^ 2)) * x) ^ n = 1 + (n : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * x
  | 0 => by simp
  | n + 1 => by
    have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
      rw [← Nat.cast_pow]
      exact ZMod.natCast_self (p ^ 2)
    rw [pow_succ (1 + (p : ZMod (p ^ 2)) * x) n, one_add_mul_p_pow x n]
    push_cast
    linear_combination (n : ZMod (p ^ 2)) * x ^ 2 * hp2

private lemma sum_inv_pow_eq_zero_zmod_p_sq {p d : ℕ} (hp : p.Prime) (hp_ne2 : p ≠ 2)
    (hd_odd : Odd d) (hd_lt : d + 1 < p - 1) :
    ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ ^ d = 0 := by
  let S : ZMod (p ^ 2) := ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ ^ d
  have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self (p ^ 2)
  have hS_rev : S = ∑ k ∈ Finset.Icc 1 (p - 1), ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ ^ d := by
    refine Finset.sum_nbij (fun k => p - k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb
      dsimp at hab
      omega
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_Icc] at hj
      exact ⟨p - j, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), by dsimp; omega⟩
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      have hsub : p - (p - k) = k := by omega
      rw [hsub]
  have hpair :
      ∀ k ∈ Finset.Icc 1 (p - 1),
        (k : ZMod (p ^ 2))⁻¹ ^ d + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ ^ d =
          -(d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ ^ (d + 1) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk_cop : k.Coprime (p ^ 2) :=
      ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk.1 (by omega))).symm).pow_right 2
    have hpk_cop : (p - k).Coprime (p ^ 2) :=
      ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm).pow_right 2
    set u : ZMod (p ^ 2) := (k : ZMod (p ^ 2))
    set v : ZMod (p ^ 2) := ((p - k : ℕ) : ZMod (p ^ 2))
    have hu : u * u⁻¹ = 1 := mul_inv_natCast_zmod hk_cop
    have hv : v * v⁻¹ = 1 := mul_inv_natCast_zmod hpk_cop
    have hv_eq : v = (p : ZMod (p ^ 2)) - u := by
      simp only [u, v, Nat.cast_sub (by omega : k ≤ p)]
    have hvinv : v⁻¹ = (-u⁻¹) * (1 + (p : ZMod (p ^ 2)) * u⁻¹) := by
      have hmul : v * ((-u⁻¹) * (1 + (p : ZMod (p ^ 2)) * u⁻¹)) = 1 := by
        rw [hv_eq]
        linear_combination (1 + (p : ZMod (p ^ 2)) * u⁻¹) * hu - u⁻¹ ^ 2 * hp2
      calc
        v⁻¹ = v⁻¹ * (v * ((-u⁻¹) * (1 + (p : ZMod (p ^ 2)) * u⁻¹))) := by rw [hmul, mul_one]
        _ = (v * v⁻¹) * ((-u⁻¹) * (1 + (p : ZMod (p ^ 2)) * u⁻¹)) := by ring
        _ = (-u⁻¹) * (1 + (p : ZMod (p ^ 2)) * u⁻¹) := by rw [hv, one_mul]
    rw [hvinv, mul_pow, one_add_mul_p_pow u⁻¹ d, neg_eq_neg_one_mul, mul_pow,
      hd_odd.neg_one_pow, pow_succ u⁻¹ d]
    ring
  have h2S :
      2 * S = -(d : ZMod (p ^ 2)) *
        ((p : ZMod (p ^ 2)) * ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ ^ (d + 1)) := by
    calc
      2 * S = S + S := by ring
      _ = ∑ k ∈ Finset.Icc 1 (p - 1),
            ((k : ZMod (p ^ 2))⁻¹ ^ d + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ ^ d) := by
        conv_lhs => rhs; rw [hS_rev]
        rw [← Finset.sum_add_distrib]
      _ = ∑ k ∈ Finset.Icc 1 (p - 1),
            (-(d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ ^ (d + 1)) :=
        Finset.sum_congr rfl hpair
      _ = -(d : ZMod (p ^ 2)) *
            ((p : ZMod (p ^ 2)) * ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ ^ (d + 1)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
  have hmap :
      ZMod.castHom (show p ∣ p ^ 2 from dvd_pow_self p (by norm_num)) (ZMod p)
        (∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ ^ (d + 1)) = 0 := by
    rw [map_sum]
    have hcongr :
        ∑ k ∈ Finset.Icc 1 (p - 1),
          ZMod.castHom (show p ∣ p ^ 2 from dvd_pow_self p (by norm_num)) (ZMod p)
            ((k : ZMod (p ^ 2))⁻¹ ^ (d + 1)) =
          ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod p)⁻¹ ^ (d + 1) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_Icc] at hk
      have hk_cop : k.Coprime (p ^ 2) :=
        ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk.1 (by omega))).symm).pow_right 2
      rw [map_pow, castHom_inv_of_isUnit _ _ (isUnit_natCast_zmod hk_cop), map_natCast]
    rw [hcongr]
    exact sum_inv_pow_eq_zero_zmod_p hp (by omega) hd_lt
  have hp_mul_zero :
      (p : ZMod (p ^ 2)) * ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ ^ (d + 1) = 0 := by
    have h := pow_mul_eq_zero_of_castHom_p (p := p) (b := 2) hp.pos (by omega) _ hmap
    simpa using h
  rw [hp_mul_zero, mul_zero] at h2S
  have h2_cop : (2 : ℕ).Coprime (p ^ 2) :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr fun h2p =>
      hp_ne2 (((Nat.dvd_prime hp).mp h2p).resolve_left (by norm_num)).symm).pow_right 2
  have h2_inv : ((2 : ℕ) : ZMod (p ^ 2)) * ((2 : ℕ) : ZMod (p ^ 2))⁻¹ = 1 :=
    mul_inv_natCast_zmod h2_cop
  calc
    S = (((2 : ℕ) : ZMod (p ^ 2)) * ((2 : ℕ) : ZMod (p ^ 2))⁻¹) * S := by rw [h2_inv, one_mul]
    _ = ((2 : ℕ) : ZMod (p ^ 2))⁻¹ * (2 * S) := by push_cast; ring
    _ = 0 := by rw [h2S, mul_zero]

private lemma a_mod_p5_ge7 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    (OeisA212334.a p : ZMod (p ^ 5)) = 1 := by
  have hp_ne0 : p ≠ 0 := by omega
  have ha_split :
      OeisA212334.a p =
        1 + ∑ k ∈ Finset.Icc 1 (p - 1), p.choose k * (p - 1).choose k * (p + k - 1).choose k ^ 2 := by
    rw [OeisA212334.a, if_neg hp_ne0]
    have hrange : Finset.range p = Finset.range ((p - 1) + 1) := by congr 1; omega
    rw [hrange, Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, one_pow, mul_one, add_comm]
    congr 1
    refine Finset.sum_nbij (fun j => j + 1) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢
      omega
    · intro a _ b _ hab
      dsimp at hab
      omega
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_Icc] at hk
      exact ⟨k - 1, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp; omega⟩
    · intro j _; rfl
  rw [ha_split, Nat.cast_add, Nat.cast_one, Nat.cast_sum]
  have hsum_zero :
      ∑ k ∈ Finset.Icc 1 (p - 1),
        ((p.choose k * (p - 1).choose k * (p + k - 1).choose k ^ 2 : ℕ) : ZMod (p ^ 5)) = 0 := by
    have hrew :
        ∑ k ∈ Finset.Icc 1 (p - 1),
          ((p.choose k * (p - 1).choose k * (p + k - 1).choose k ^ 2 : ℕ) : ZMod (p ^ 5)) =
        (p : ZMod (p ^ 5)) ^ 4 *
            (∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 5))⁻¹ ^ 4) -
          (p : ZMod (p ^ 5)) ^ 3 *
            (∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 5))⁻¹ ^ 3) := by
      rw [Finset.sum_congr rfl fun k hk =>
        term_eq_zmod_p5 hp (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2]
      rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    rw [hrew]
    have hterm1 :
        (p : ZMod (p ^ 5)) ^ 4 *
          (∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 5))⁻¹ ^ 4) = 0 := by
      have hmap :
          ZMod.castHom (show p ∣ p ^ 5 from dvd_pow_self p (by norm_num)) (ZMod p)
            (∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 5))⁻¹ ^ 4) = 0 := by
        rw [map_sum]
        have hcongr :
            ∑ k ∈ Finset.Icc 1 (p - 1),
              ZMod.castHom (show p ∣ p ^ 5 from dvd_pow_self p (by norm_num)) (ZMod p)
                ((k : ZMod (p ^ 5))⁻¹ ^ 4) =
              ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod p)⁻¹ ^ 4 := by
          refine Finset.sum_congr rfl fun k hk => ?_
          simp only [Finset.mem_Icc] at hk
          have hk_cop : k.Coprime (p ^ 5) :=
            ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk.1 (by omega))).symm).pow_right 5
          rw [map_pow, castHom_inv_of_isUnit _ _ (isUnit_natCast_zmod hk_cop), map_natCast]
        rw [hcongr]
        exact sum_inv_pow_eq_zero_zmod_p hp (by omega) (by omega)
      exact pow_mul_eq_zero_of_castHom_p (p := p) (b := 5) hp.pos (by omega) _ hmap
    have hterm2 :
        (p : ZMod (p ^ 5)) ^ 3 *
          (∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 5))⁻¹ ^ 3) = 0 := by
      refine pow_mul_eq_zero_of_castHom_eq_zero (p := p) (a := 2) (b := 3) hp.pos _ ?_
      rw [map_sum]
      have hcongr :
          ∑ k ∈ Finset.Icc 1 (p - 1),
            ZMod.castHom (pow_dvd_pow p (show 2 ≤ 2 + 3 by omega)) (ZMod (p ^ 2))
              ((k : ZMod (p ^ 5))⁻¹ ^ 3) =
            ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ ^ 3 := by
        refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_Icc] at hk
        have hk_cop : k.Coprime (p ^ 5) :=
          ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk.1 (by omega))).symm).pow_right 5
        rw [map_pow, castHom_inv_of_isUnit _ _ (isUnit_natCast_zmod hk_cop), map_natCast]
      rw [hcongr]
      exact sum_inv_pow_eq_zero_zmod_p_sq hp (by omega) ⟨1, by omega⟩ (by omega)
    rw [hterm1, hterm2, sub_self]
  rw [hsum_zero, add_zero]

private lemma a_5_mod : OeisA212334.a 5 % 5 ^ 5 = 1 := by decide

end OeisA212334Conj1Proof

theorem OMA.solution : type_of% @OeisA212334.conjecture_1 := by
  intro p hp hp5
  by_cases h5 : p = 5
  · subst h5
    exact OeisA212334Conj1Proof.a_5_mod
  · have hp7 : 7 ≤ p := by
      by_contra hlt
      have : p = 6 := by omega
      subst this
      norm_num at hp
    have hcast : (OeisA212334.a p : ZMod (p ^ 5)) = ((1 : ℕ) : ZMod (p ^ 5)) := by
      simpa using OeisA212334Conj1Proof.a_mod_p5_ge7 hp hp7
    have hval := congr_arg ZMod.val hcast
    have : NeZero (p ^ 5) := ⟨pow_ne_zero 5 (by omega)⟩
    rw [ZMod.val_natCast, ZMod.val_natCast] at hval
    have h1lt : 1 < p ^ 5 := by
      have : 1 < p := by omega
      exact one_lt_pow₀ this (by norm_num)
    rwa [Nat.mod_eq_of_lt h1lt] at hval
