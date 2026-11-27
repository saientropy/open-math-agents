import FormalConjectures.OEIS.«189286»

/-!
Proof of `OeisA189286.conjecture_3`: for every positive integer $n$,
$$a(n) = \frac{\sum_{k=0}^n \binom{6k}{3k}\binom{3k}{k}\binom{6(n-k)}{3(n-k)}\binom{3(n-k)}{n-k}}{(2n-1)\binom{3n}{n}}$$
is an integer divisible by $8$, and $a(n)/8$ is odd if and only if $n$ is a power of $2$.

We prove termwise divisibility $(2n-1)\binom{3n}{n} \mid t_k t_{n-k}$ via Legendre's formula
and elementary floor inequalities for every prime $p$, and determine $v_2(a(n))$ via
$v_2(t_k) = 2 s_2(k)$ and Gould's count of odd binomial coefficients.
-/

namespace OeisA189286Proof

private def tNat (k : ℕ) : ℕ := (6 * k).choose (3 * k) * (3 * k).choose k

private def SNat (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), tNat k * tNat (n - k)

private lemma tNat_pos (k : ℕ) : 0 < tNat k :=
  Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))

private lemma tNat_factorial_eq (k : ℕ) :
    tNat k * (3 * k).factorial * (2 * k).factorial * k.factorial = (6 * k).factorial := by
  have h1 : (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial = (6 * k).factorial := by
    simpa [show 6 * k - 3 * k = 3 * k by omega] using
      Nat.choose_mul_factorial_mul_factorial (show 3 * k ≤ 6 * k by omega)
  have h2 : (3 * k).choose k * k.factorial * (2 * k).factorial = (3 * k).factorial := by
    simpa [show 3 * k - k = 2 * k by omega] using
      Nat.choose_mul_factorial_mul_factorial (show k ≤ 3 * k by omega)
  unfold tNat
  calc (6 * k).choose (3 * k) * (3 * k).choose k * (3 * k).factorial * (2 * k).factorial * k.factorial
      = (6 * k).choose (3 * k) * (3 * k).factorial * ((3 * k).choose k * k.factorial * (2 * k).factorial) := by
          ring
    _ = (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial := by rw [h2]
    _ = (6 * k).factorial := h1

private lemma choose3n_factorial_eq (n : ℕ) :
    (3 * n).choose n * n.factorial * (2 * n).factorial = (3 * n).factorial := by
  simpa [show 3 * n - n = 2 * n by omega] using
    Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n by omega)

private def fFloor (k d : ℕ) : ℕ := (6 * k) / d - (3 * k) / d - (2 * k) / d - k / d

private def gFloor (n d : ℕ) : ℕ := (3 * n) / d - (2 * n) / d - n / d

private lemma div_add_le_add_div (a b d : ℕ) : a / d + b / d ≤ (a + b) / d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rw [Nat.le_div_iff_mul_le hd]
    have h1 := Nat.div_mul_le_self a d
    have h2 := Nat.div_mul_le_self b d
    nlinarith only [h1, h2]

private lemma fFloor_sum_le (k d : ℕ) : (3 * k) / d + (2 * k) / d + k / d ≤ (6 * k) / d := by
  have h1 := div_add_le_add_div (3 * k) (2 * k) d
  have h2 := div_add_le_add_div (3 * k + 2 * k) k d
  have h3 : 3 * k + 2 * k + k = 6 * k := by omega
  rw [h3] at h2
  omega

private lemma gFloor_sum_le (n d : ℕ) : (2 * n) / d + n / d ≤ (3 * n) / d := by
  have h1 := div_add_le_add_div (2 * n) n d
  have h2 : 2 * n + n = 3 * n := by omega
  rw [h2] at h1
  omega

private lemma fFloor_eq_mod (k d : ℕ) (hd : 0 < d) :
    fFloor k d = (6 * (k % d)) / d - (3 * (k % d)) / d - (2 * (k % d)) / d := by
  unfold fFloor
  set q := k / d
  set r := k % d
  have hk : k = d * q + r := (Nat.div_add_mod k d).symm
  have h6 : (6 * k) / d = 6 * q + (6 * r) / d := by
    have : 6 * k = d * (6 * q) + 6 * r := by rw [hk]; ring
    rw [this, Nat.mul_add_div hd]
  have h3 : (3 * k) / d = 3 * q + (3 * r) / d := by
    have : 3 * k = d * (3 * q) + 3 * r := by rw [hk]; ring
    rw [this, Nat.mul_add_div hd]
  have h2 : (2 * k) / d = 2 * q + (2 * r) / d := by
    have : 2 * k = d * (2 * q) + 2 * r := by rw [hk]; ring
    rw [this, Nat.mul_add_div hd]
  have hr : r / d = 0 := Nat.div_eq_of_lt (Nat.mod_lt k hd)
  have hle := fFloor_sum_le r d
  rw [hr, add_zero] at hle
  rw [h6, h3, h2]
  omega

private lemma gFloor_eq_mod (n d : ℕ) (hd : 0 < d) :
    gFloor n d = (3 * (n % d)) / d - (2 * (n % d)) / d := by
  unfold gFloor
  set q := n / d
  set r := n % d
  have hn : n = d * q + r := (Nat.div_add_mod n d).symm
  have h3 : (3 * n) / d = 3 * q + (3 * r) / d := by
    have : 3 * n = d * (3 * q) + 3 * r := by rw [hn]; ring
    rw [this, Nat.mul_add_div hd]
  have h2 : (2 * n) / d = 2 * q + (2 * r) / d := by
    have : 2 * n = d * (2 * q) + 2 * r := by rw [hn]; ring
    rw [this, Nat.mul_add_div hd]
  have hr : r / d = 0 := Nat.div_eq_of_lt (Nat.mod_lt n hd)
  have hle := gFloor_sum_le r d
  rw [hr, add_zero] at hle
  rw [h3, h2]
  omega

private lemma fFloor_ge_one_of_six_mul {k d : ℕ} (hd : 0 < d) (h : d ≤ 6 * (k % d)) :
    1 ≤ fFloor k d := by
  rw [fFloor_eq_mod k d hd]
  set r := k % d
  have hr : r < d := Nat.mod_lt k hd
  have h6 : 1 ≤ (6 * r) / d := (Nat.le_div_iff_mul_le hd).mpr (by omega)
  by_cases h3 : 3 * r < d
  · have : (3 * r) / d = 0 := Nat.div_eq_of_lt h3
    have : (2 * r) / d = 0 := Nat.div_eq_of_lt (by omega)
    omega
  · by_cases h2 : 2 * r < d
    · have h3eq : (3 * r) / d = 1 := by
        apply le_antisymm
        · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hd).mpr (by omega))
        · exact (Nat.le_div_iff_mul_le hd).mpr (by omega)
      have h2eq : (2 * r) / d = 0 := Nat.div_eq_of_lt h2
      have h6ge : 2 ≤ (6 * r) / d := (Nat.le_div_iff_mul_le hd).mpr (by omega)
      omega
    · by_cases h32 : 3 * r < 2 * d
      · have h3eq : (3 * r) / d = 1 := by
          apply le_antisymm
          · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hd).mpr (by omega))
          · exact (Nat.le_div_iff_mul_le hd).mpr (by omega)
        have h2eq : (2 * r) / d = 1 := by
          apply le_antisymm
          · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hd).mpr (by omega))
          · exact (Nat.le_div_iff_mul_le hd).mpr (by omega)
        have h6ge : 3 ≤ (6 * r) / d := (Nat.le_div_iff_mul_le hd).mpr (by omega)
        omega
      · have h3eq : (3 * r) / d = 2 := by
          apply le_antisymm
          · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hd).mpr (by omega))
          · exact (Nat.le_div_iff_mul_le hd).mpr (by omega)
        have h2eq : (2 * r) / d = 1 := by
          apply le_antisymm
          · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hd).mpr (by omega))
          · exact (Nat.le_div_iff_mul_le hd).mpr (by omega)
        have h6ge : 4 ≤ (6 * r) / d := (Nat.le_div_iff_mul_le hd).mpr (by omega)
        omega

private lemma fFloor_ge_two_of_six_mul {k d : ℕ} (hd : 0 < d) (h : 5 * d ≤ 6 * (k % d)) :
    2 ≤ fFloor k d := by
  rw [fFloor_eq_mod k d hd]
  set r := k % d
  have hr : r < d := Nat.mod_lt k hd
  have h6ge : 5 ≤ (6 * r) / d := (Nat.le_div_iff_mul_le hd).mpr (by omega)
  have h3le : (3 * r) / d ≤ 2 := Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hd).mpr (by omega))
  have h2le : (2 * r) / d ≤ 1 := Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hd).mpr (by omega))
  omega

private lemma gFloor_le_one (n d : ℕ) (hd : 0 < d) : gFloor n d ≤ 1 := by
  rw [gFloor_eq_mod n d hd]
  set r := n % d
  have hr : r < d := Nat.mod_lt n hd
  set x := (3 * r) / d
  set y := (2 * r) / d
  change x - y ≤ 1
  have h3le : x ≤ 2 := Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hd).mpr (by omega))
  by_cases h2 : 2 * r < d
  · have h31 : x ≤ 1 := Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hd).mpr (by omega))
    exact le_trans (Nat.sub_le x y) h31
  · have h21 : 1 ≤ y := (Nat.le_div_iff_mul_le hd).mpr (by omega)
    exact Nat.sub_le_of_le_add (by omega)

private lemma gFloor_le_fFloor_add (k l d : ℕ) (hd : 0 < d) :
    gFloor (k + l) d ≤ fFloor k d + fFloor l d := by
  by_cases hk : d ≤ 6 * (k % d)
  · have h1 := fFloor_ge_one_of_six_mul hd hk
    have h2 := gFloor_le_one (k + l) d hd
    omega
  · by_cases hl : d ≤ 6 * (l % d)
    · have h1 := fFloor_ge_one_of_six_mul hd hl
      have h2 := gFloor_le_one (k + l) d hd
      omega
    · have hkl : k % d + l % d < d := by omega
      have hmod : (k + l) % d = k % d + l % d := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt hkl]
      rw [gFloor_eq_mod (k + l) d hd, hmod]
      have h3 : (3 * (k % d + l % d)) / d = 0 := Nat.div_eq_of_lt (by omega)
      rw [h3]
      simp

private lemma mod_eq_half_succ_of_dvd_two_mul_sub_one {n d : ℕ}
    (hn : 1 ≤ n) (hd : 3 ≤ d) (hodd : d % 2 = 1) (hdvd : d ∣ 2 * n - 1) :
    n % d = (d + 1) / 2 := by
  have h2n : (2 * n) % d = 1 := by
    obtain ⟨q, hq⟩ := hdvd
    have : 2 * n = d * q + 1 := by omega
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have h2r : (2 * (n % d)) % d = 1 := by
    rw [← Nat.mul_mod_mod] at h2n
    simpa [Nat.mul_mod] using h2n
  have hr : n % d < d := Nat.mod_lt n (by omega)
  by_cases hlt : 2 * (n % d) < d
  · rw [Nat.mod_eq_of_lt hlt] at h2r
    omega
  · have hlt2 : 2 * (n % d) - d < d := by omega
    have hsub : (2 * (n % d)) % d = 2 * (n % d) - d := by
      have := Nat.mod_eq_sub_mod (show d ≤ 2 * (n % d) by omega)
      rw [this, Nat.mod_eq_of_lt hlt2]
    omega

private lemma gFloor_eq_zero_of_dvd_odd {n d : ℕ}
    (hn : 1 ≤ n) (hd5 : 5 ≤ d) (hodd : d % 2 = 1) (hdvd : d ∣ 2 * n - 1) :
    gFloor n d = 0 := by
  rw [gFloor_eq_mod n d (by omega), mod_eq_half_succ_of_dvd_two_mul_sub_one hn (by omega) hodd hdvd]
  have h3 : (3 * ((d + 1) / 2)) / d = 1 := by
    apply le_antisymm
    · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega))
    · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have h2 : (2 * ((d + 1) / 2)) / d = 1 := by
    apply le_antisymm
    · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega))
    · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  rw [h3, h2]

private lemma delta_ge_one_of_dvd_odd {k l d : ℕ}
    (hkl : 1 ≤ k + l) (hd5 : 5 ≤ d) (hodd : d % 2 = 1) (hdvd : d ∣ 2 * (k + l) - 1) :
    gFloor (k + l) d + 1 ≤ fFloor k d + fFloor l d := by
  have hg : gFloor (k + l) d = 0 := gFloor_eq_zero_of_dvd_odd hkl hd5 hodd hdvd
  have hmod : (k + l) % d = (d + 1) / 2 :=
    mod_eq_half_succ_of_dvd_two_mul_sub_one hkl (by omega) hodd hdvd
  have hsum : (d + 1) / 2 ≤ k % d + l % d := by
    rw [← hmod, Nat.add_mod]
    exact Nat.mod_le _ _
  by_cases hk : d ≤ 6 * (k % d)
  · have := fFloor_ge_one_of_six_mul (by omega) hk
    omega
  · have hl : d ≤ 6 * (l % d) := by omega
    have := fFloor_ge_one_of_six_mul (by omega) hl
    omega

private lemma padicValNat_tNat {p k b : ℕ} [hp : Fact p.Prime] (hb : Nat.log p (6 * k) < b) :
    padicValNat p (tNat k) = ∑ i ∈ Finset.Ico 1 b, fFloor k (p ^ i) := by
  have hfac := congrArg (padicValNat p) (tNat_factorial_eq k)
  have ht0 : tNat k ≠ 0 := (tNat_pos k).ne'
  have h30 : (3 * k).factorial ≠ 0 := Nat.factorial_ne_zero _
  have h20 : (2 * k).factorial ≠ 0 := Nat.factorial_ne_zero _
  have h10 : k.factorial ≠ 0 := Nat.factorial_ne_zero _
  have hm1 : tNat k * (3 * k).factorial ≠ 0 := mul_ne_zero ht0 h30
  have hm2 : tNat k * (3 * k).factorial * (2 * k).factorial ≠ 0 := mul_ne_zero hm1 h20
  rw [padicValNat.mul hm2 h10, padicValNat.mul hm1 h20, padicValNat.mul ht0 h30] at hfac
  have hb3 : Nat.log p (3 * k) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb
  have hb2 : Nat.log p (2 * k) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb
  have hb1 : Nat.log p k < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb
  rw [padicValNat_factorial hb, padicValNat_factorial hb3, padicValNat_factorial hb2,
    padicValNat_factorial hb1] at hfac
  have hadd :
      (∑ i ∈ Finset.Ico 1 b, fFloor k (p ^ i)) +
        (∑ i ∈ Finset.Ico 1 b, (3 * k) / p ^ i) +
        (∑ i ∈ Finset.Ico 1 b, (2 * k) / p ^ i) +
        (∑ i ∈ Finset.Ico 1 b, k / p ^ i) =
      ∑ i ∈ Finset.Ico 1 b, (6 * k) / p ^ i := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hle := fFloor_sum_le k (p ^ i)
    unfold fFloor
    omega
  omega

private lemma padicValNat_choose3n {p n b : ℕ} [hp : Fact p.Prime] (hb : Nat.log p (3 * n) < b) :
    padicValNat p ((3 * n).choose n) = ∑ i ∈ Finset.Ico 1 b, gFloor n (p ^ i) := by
  have hfac := congrArg (padicValNat p) (choose3n_factorial_eq n)
  have hc0 : (3 * n).choose n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have h20 : (2 * n).factorial ≠ 0 := Nat.factorial_ne_zero _
  have h10 : n.factorial ≠ 0 := Nat.factorial_ne_zero _
  have hm1 : (3 * n).choose n * n.factorial ≠ 0 := mul_ne_zero hc0 h10
  rw [padicValNat.mul hm1 h20, padicValNat.mul hc0 h10] at hfac
  have hb2 : Nat.log p (2 * n) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb
  have hb1 : Nat.log p n < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb
  rw [padicValNat_factorial hb, padicValNat_factorial hb2, padicValNat_factorial hb1] at hfac
  have hadd :
      (∑ i ∈ Finset.Ico 1 b, gFloor n (p ^ i)) +
        (∑ i ∈ Finset.Ico 1 b, n / p ^ i) +
        (∑ i ∈ Finset.Ico 1 b, (2 * n) / p ^ i) =
      ∑ i ∈ Finset.Ico 1 b, (3 * n) / p ^ i := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hle := gFloor_sum_le n (p ^ i)
    unfold gFloor
    omega
  omega

private def deltaFloor (k l d : ℕ) : ℕ := fFloor k d + fFloor l d - gFloor (k + l) d

private lemma three_pow_odd (m : ℕ) : 3 ^ m % 2 = 1 := by
  induction m with
  | zero => decide
  | succ k ih => rw [pow_succ]; omega

private lemma three_ind_step (k l : ℕ) (hkl : 1 ≤ k + l) :
    ∀ m : ℕ, 1 ≤ m → 3 ^ m ∣ 2 * (k + l) - 1 →
      m ≤ ∑ i ∈ Finset.Icc 1 m, deltaFloor k l (3 ^ i) ∨
      (m - 1 ≤ ∑ i ∈ Finset.Icc 1 m, deltaFloor k l (3 ^ i) ∧
        ((k % 3 ^ m = (3 ^ m + 1) / 2 ∧ l % 3 ^ m = 0) ∨
         (k % 3 ^ m = 0 ∧ l % 3 ^ m = (3 ^ m + 1) / 2))) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro hdvd
    have hmod : (k + l) % 3 = 2 := by
      have := mod_eq_half_succ_of_dvd_two_mul_sub_one (d := 3) hkl (by decide) (by decide) (by simpa using hdvd)
      simpa using this
    have hklt : k % 3 < 3 := Nat.mod_lt k (by decide)
    have hllt : l % 3 < 3 := Nat.mod_lt l (by decide)
    have hsum : (k % 3 + l % 3) % 3 = 2 := by rw [← Nat.add_mod, hmod]
    simp only [Finset.Icc_self, Finset.sum_singleton, pow_one, deltaFloor]
    have h1 : k % 3 = 1 ∧ l % 3 = 1 ∨ k % 3 = 2 ∧ l % 3 = 0 ∨ k % 3 = 0 ∧ l % 3 = 2 := by omega
    rcases h1 with ⟨hk1, hl1⟩ | ⟨hk2, hl0⟩ | ⟨hk0, hl2⟩
    · left
      have hf1 : fFloor k 3 = 1 := by rw [fFloor_eq_mod k 3 (by decide), hk1]
      have hf2 : fFloor l 3 = 1 := by rw [fFloor_eq_mod l 3 (by decide), hl1]
      have hg : gFloor (k + l) 3 = 1 := by rw [gFloor_eq_mod (k + l) 3 (by decide), hmod]
      omega
    · right; exact ⟨by omega, Or.inl ⟨hk2, hl0⟩⟩
    · right; exact ⟨by omega, Or.inr ⟨hk0, hl2⟩⟩
  | succ m hm ih =>
    intro hdvd
    have hdvd_m : 3 ^ m ∣ 2 * (k + l) - 1 := dvd_trans (pow_dvd_pow 3 (Nat.le_succ m)) hdvd
    have hpow_ge9 : 9 ≤ 3 ^ (m + 1) := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hstep1 : 1 ≤ deltaFloor k l (3 ^ (m + 1)) := by
      have h := delta_ge_one_of_dvd_odd hkl (by omega) (three_pow_odd (m + 1)) hdvd
      unfold deltaFloor
      omega
    have hsplit : ∑ i ∈ Finset.Icc 1 (m + 1), deltaFloor k l (3 ^ i) =
        (∑ i ∈ Finset.Icc 1 m, deltaFloor k l (3 ^ i)) + deltaFloor k l (3 ^ (m + 1)) := by
      rw [show Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
      rw [Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), add_comm]
    rw [hsplit]
    rcases ih hdvd_m with hgood | ⟨hnear, hsym⟩
    · left; omega
    · set D := 3 ^ m
      have hDpos : 0 < D := Nat.pow_pos (by decide)
      have hDodd : D % 2 = 1 := three_pow_odd m
      have hD3 : 3 ^ (m + 1) = 3 * D := by rw [pow_succ']
      have hhg : gFloor (k + l) (3 * D) = 0 := by
        rw [← hD3]
        exact gFloor_eq_zero_of_dvd_odd hkl (by omega) (three_pow_odd (m + 1)) hdvd
      have hn_mod : (k + l) % (3 * D) = D + (D + 1) / 2 := by
        have h1 := mod_eq_half_succ_of_dvd_two_mul_sub_one (d := 3 * D) hkl (by omega)
          (by rw [← hD3]; exact three_pow_odd (m + 1)) (by rw [← hD3]; exact hdvd)
        omega
      have hcases : ∀ a b : ℕ, a + b = k + l → a % D = (D + 1) / 2 → b % D = 0 →
          (2 ≤ deltaFloor a b (3 * D)) ∨ (a % (3 * D) = (3 * D + 1) / 2 ∧ b % (3 * D) = 0) := by
        intro a b hab ha hb
        set ra := (a / D) % 3
        set rb := (b / D) % 3
        have ha_mod : a % (3 * D) = ra * D + (D + 1) / 2 := by
          have h1 := Nat.div_add_mod a D
          have h2 := Nat.div_add_mod (a / D) 3
          have h3 : a = (3 * D) * ((a / D) / 3) + (ra * D + a % D) := by
            have : D * (a / D) = D * (3 * ((a / D) / 3) + ra) := congrArg (D * ·) h2.symm
            linarith
          have hlt : ra * D + a % D < 3 * D := by
            have : ra < 3 := Nat.mod_lt _ (by decide)
            have : a % D < D := Nat.mod_lt a hDpos
            nlinarith only [‹ra < 3›, ‹a % D < D›, hDpos]
          rw [h3, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt, ha]
        have hb_mod : b % (3 * D) = rb * D := by
          have h1 := Nat.div_add_mod b D
          have h2 := Nat.div_add_mod (b / D) 3
          have h3 : b = (3 * D) * ((b / D) / 3) + (rb * D + b % D) := by
            have : D * (b / D) = D * (3 * ((b / D) / 3) + rb) := congrArg (D * ·) h2.symm
            linarith
          have hlt : rb * D + b % D < 3 * D := by
            have : rb < 3 := Nat.mod_lt _ (by decide)
            have : b % D < D := Nat.mod_lt b hDpos
            nlinarith only [‹rb < 3›, ‹b % D < D›, hDpos]
          rw [h3, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt, hb, add_zero]
        have hra : ra < 3 := Nat.mod_lt _ (by decide)
        have hrb : rb < 3 := Nat.mod_lt _ (by decide)
        have hsum_mod : ((ra + rb) * D + (D + 1) / 2) % (3 * D) = D + (D + 1) / 2 := by
          have hmul : (ra + rb) * D + (D + 1) / 2 = ra * D + (D + 1) / 2 + rb * D := by ring
          rw [hmul, ← ha_mod, ← hb_mod, ← Nat.add_mod, hab, hn_mod]
        have hr_sum : (ra + rb) % 3 = 1 := by
          have hDge3 : 3 ≤ D := le_trans (by decide : 3 ≤ 3 ^ 1) (Nat.pow_le_pow_right (by decide) hm)
          have hhalf : (D + 1) / 2 < D := by omega
          by_cases hs : ra + rb < 3
          · have hlt : (ra + rb) * D + (D + 1) / 2 < 3 * D := by nlinarith only [hs, hhalf]
            rw [Nat.mod_eq_of_lt hlt] at hsum_mod
            have : (ra + rb) * D = 1 * D := by omega
            have : ra + rb = 1 := Nat.eq_of_mul_eq_mul_right hDpos this
            omega
          · have hsub : (ra + rb) * D + (D + 1) / 2 = 3 * D + ((ra + rb - 3) * D + (D + 1) / 2) := by
              have : ra + rb = 3 + (ra + rb - 3) := by omega
              calc (ra + rb) * D + (D + 1) / 2 = (3 + (ra + rb - 3)) * D + (D + 1) / 2 := by rw [← this]
                _ = 3 * D + ((ra + rb - 3) * D + (D + 1) / 2) := by ring
            have hle1 : ra + rb - 3 ≤ 1 := by omega
            have hlt : (ra + rb - 3) * D + (D + 1) / 2 < 3 * D := by nlinarith only [hle1, hhalf]
            rw [hsub, Nat.add_mod_left, Nat.mod_eq_of_lt hlt] at hsum_mod
            have : (ra + rb - 3) * D = 1 * D := by omega
            have : ra + rb - 3 = 1 := Nat.eq_of_mul_eq_mul_right hDpos this
            omega
        have h3cases : (ra = 1 ∧ rb = 0) ∨ (ra = 0 ∧ rb = 1) ∨ (ra = 2 ∧ rb = 2) := by omega
        rcases h3cases with ⟨hra1, hrb0⟩ | ⟨hra0, hrb1⟩ | ⟨hra2, hrb2⟩
        · right
          rw [ha_mod, hb_mod, hra1, hrb0]
          omega
        · left
          unfold deltaFloor
          rw [hab, hhg, Nat.sub_zero]
          have hfa : 1 ≤ fFloor a (3 * D) := fFloor_ge_one_of_six_mul (by omega) (by rw [ha_mod, hra0]; omega)
          have hfb : 1 ≤ fFloor b (3 * D) := fFloor_ge_one_of_six_mul (by omega) (by rw [hb_mod, hrb1]; omega)
          omega
        · left
          unfold deltaFloor
          rw [hab, hhg, Nat.sub_zero]
          have hfa : 1 ≤ fFloor a (3 * D) := fFloor_ge_one_of_six_mul (by omega) (by rw [ha_mod, hra2]; omega)
          have hfb : 1 ≤ fFloor b (3 * D) := fFloor_ge_one_of_six_mul (by omega) (by rw [hb_mod, hrb2]; omega)
          omega
      rcases hsym with ⟨hkD, hlD⟩ | ⟨hkD, hlD⟩
      · rcases hcases k l rfl hkD hlD with h2 | hkeep
        · left; rw [hD3]; omega
        · right; rw [hD3] at hstep1 ⊢; exact ⟨by omega, Or.inl hkeep⟩
      · rcases hcases l k (add_comm l k) hlD hkD with h2 | hkeep
        · left
          have hcomm : deltaFloor k l (3 ^ (m + 1)) = deltaFloor l k (3 * D) := by
            rw [hD3]; unfold deltaFloor; rw [add_comm k l, add_comm (fFloor k _)]
          omega
        · right; rw [hD3] at hstep1 ⊢; exact ⟨by omega, Or.inr ⟨hkeep.2, hkeep.1⟩⟩

private lemma three_extra_step {k l E : ℕ} (hkl : 1 ≤ k + l)
    (hE : 1 ≤ E) (hndvd : ¬ 3 ^ (E + 1) ∣ 2 * (k + l) - 1)
    (hkE : k % 3 ^ E = (3 ^ E + 1) / 2) (hlE : l % 3 ^ E = 0) :
    1 ≤ deltaFloor k l (3 ^ (E + 1)) := by
  set D := 3 ^ E
  have hDge3 : 3 ≤ D := le_trans (by decide : 3 ≤ 3 ^ 1) (Nat.pow_le_pow_right (by decide) hE)
  have hDpos : 0 < D := by omega
  have hDodd : D % 2 = 1 := three_pow_odd E
  have hD3 : 3 ^ (E + 1) = 3 * D := by rw [pow_succ']
  rw [hD3]
  set rk := (k / D) % 3
  set rl := (l / D) % 3
  have hrk : rk < 3 := Nat.mod_lt _ (by decide)
  have hrl : rl < 3 := Nat.mod_lt _ (by decide)
  have hk_mod : k % (3 * D) = rk * D + (D + 1) / 2 := by
    have h1 := Nat.div_add_mod k D
    have h2 := Nat.div_add_mod (k / D) 3
    have h3 : k = (3 * D) * ((k / D) / 3) + (rk * D + k % D) := by
      have : D * (k / D) = D * (3 * ((k / D) / 3) + rk) := congrArg (D * ·) h2.symm
      linarith
    have hlt : rk * D + k % D < 3 * D := by
      have : k % D < D := Nat.mod_lt k hDpos
      nlinarith only [hrk, ‹k % D < D›, hDpos]
    rw [h3, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt, hkE]
  have hl_mod : l % (3 * D) = rl * D := by
    have h1 := Nat.div_add_mod l D
    have h2 := Nat.div_add_mod (l / D) 3
    have h3 : l = (3 * D) * ((l / D) / 3) + (rl * D + l % D) := by
      have : D * (l / D) = D * (3 * ((l / D) / 3) + rl) := congrArg (D * ·) h2.symm
      linarith
    have hlt : rl * D + l % D < 3 * D := by
      have : l % D < D := Nat.mod_lt l hDpos
      nlinarith only [hrl, ‹l % D < D›, hDpos]
    rw [h3, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt, hlE, add_zero]
  have hsum_ne1 : (rk + rl) % 3 ≠ 1 := by
    intro h1
    apply hndvd
    rw [hD3]
    have hkm := Nat.div_add_mod k (3 * D)
    have hlm := Nat.div_add_mod l (3 * D)
    have h2half : 2 * ((D + 1) / 2) = D + 1 := by omega
    have hrsum : rk + rl = 1 ∨ rk + rl = 4 := by omega
    rcases hrsum with h | h
    · refine ⟨2 * (k / (3 * D) + l / (3 * D)) + 1, ?_⟩
      have hrd : rk * D + rl * D = D := by nlinarith only [h]
      have h2kl : 2 * (k + l) = (3 * D) * (2 * (k / (3 * D) + l / (3 * D)) + 1) + 1 := by
        linarith only [hkm, hlm, hk_mod, hl_mod, h2half, hrd]
      omega
    · refine ⟨2 * (k / (3 * D) + l / (3 * D)) + 3, ?_⟩
      have hrd : rk * D + rl * D = 4 * D := by nlinarith only [h]
      have h2kl : 2 * (k + l) = (3 * D) * (2 * (k / (3 * D) + l / (3 * D)) + 3) + 1 := by
        linarith only [hkm, hlm, hk_mod, hl_mod, h2half, hrd]
      omega
  have hfk1 : 1 ≤ fFloor k (3 * D) := fFloor_ge_one_of_six_mul (by omega) (by rw [hk_mod]; omega)
  by_cases h0 : (rk + rl) % 3 = 0
  · have hkl_mod : (k + l) % (3 * D) = (D + 1) / 2 := by
      rw [Nat.add_mod, hk_mod, hl_mod]
      have : rk + rl = 0 ∨ rk + rl = 3 := by omega
      rcases this with h | h
      · have : rk * D + (D + 1) / 2 + rl * D = (D + 1) / 2 := by nlinarith only [h]
        rw [this, Nat.mod_eq_of_lt (by omega)]
      · have : rk * D + (D + 1) / 2 + rl * D = 3 * D + (D + 1) / 2 := by nlinarith only [h]
        rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have hg0 : gFloor (k + l) (3 * D) = 0 := by
      rw [gFloor_eq_mod (k + l) (3 * D) (by omega), hkl_mod]
      have h3 : (3 * ((D + 1) / 2)) / (3 * D) = 0 := Nat.div_eq_of_lt (by omega)
      rw [h3]
      simp
    unfold deltaFloor
    omega
  · have h2 : (rk + rl) % 3 = 2 := by omega
    have hg1 : gFloor (k + l) (3 * D) ≤ 1 := gFloor_le_one (k + l) (3 * D) (by omega)
    by_cases hrk2 : rk = 2
    · have hfk2 : 2 ≤ fFloor k (3 * D) :=
        fFloor_ge_two_of_six_mul (by omega) (by rw [hk_mod, hrk2]; omega)
      unfold deltaFloor
      omega
    · have hrl1 : 1 ≤ rl := by omega
      have hfl1 : 1 ≤ fFloor l (3 * D) :=
        fFloor_ge_one_of_six_mul (by omega) (by rw [hl_mod]; nlinarith only [hrl1, hDpos])
      unfold deltaFloor
      omega

private lemma denom_dvd_term {n k : ℕ} (hn : 1 ≤ n) (hkn : k ≤ n) :
    (2 * n - 1) * (3 * n).choose n ∣ tNat k * tNat (n - k) := by
  set l := n - k
  have hkl : k + l = n := by omega
  have hDpos : 0 < (2 * n - 1) * (3 * n).choose n :=
    Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  have hTpos : 0 < tNat k * tNat l := Nat.mul_pos (tNat_pos k) (tNat_pos l)
  rw [← Nat.factorization_le_iff_dvd hDpos.ne' hTpos.ne']
  intro p
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    rw [padicValNat.mul (by omega) (Nat.choose_pos (by omega)).ne',
      padicValNat.mul (tNat_pos k).ne' (tNat_pos l).ne']
    set E := padicValNat p (2 * n - 1)
    set b := max (Nat.log p (6 * n) + 1) (E + 2)
    have hbk : Nat.log p (6 * k) < b :=
      lt_of_le_of_lt (Nat.log_mono_right (by omega)) (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _))
    have hbl : Nat.log p (6 * l) < b :=
      lt_of_le_of_lt (Nat.log_mono_right (by omega)) (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _))
    have hbn : Nat.log p (3 * n) < b :=
      lt_of_le_of_lt (Nat.log_mono_right (by omega)) (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _))
    rw [padicValNat_tNat hbk, padicValNat_tNat hbl, padicValNat_choose3n hbn]
    have hsum_delta :
        (∑ i ∈ Finset.Ico 1 b, gFloor n (p ^ i)) +
          ∑ i ∈ Finset.Ico 1 b, deltaFloor k l (p ^ i) =
        (∑ i ∈ Finset.Ico 1 b, fFloor k (p ^ i)) +
          ∑ i ∈ Finset.Ico 1 b, fFloor l (p ^ i) := by
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hle := gFloor_le_fFloor_add k l (p ^ i) (pow_pos hp.pos i)
      unfold deltaFloor
      rw [hkl] at hle ⊢
      omega
    suffices hE : E ≤ ∑ i ∈ Finset.Ico 1 b, deltaFloor k l (p ^ i) by omega
    by_cases hE0 : E = 0
    · omega
    · have hp_ne2 : p ≠ 2 := by
        intro hp2
        subst hp2
        have h2dvd : 2 ∣ 2 * n - 1 := by
          have := (padicValNat_dvd_iff_le (show 2 * n - 1 ≠ 0 by omega)).mpr (show 1 ≤ E by omega)
          simpa using this
        omega
      have hp_odd : p % 2 = 1 := by
        rcases hp.eq_two_or_odd with h | h
        · exact absurd h hp_ne2
        · exact h
      have hpow_odd : ∀ i : ℕ, p ^ i % 2 = 1 := fun i => by
        induction i with
        | zero => simp
        | succ j ih => rw [pow_succ, Nat.mul_mod, ih, hp_odd]
      by_cases hp3 : p = 3
      · subst hp3
        have h3dvd : 3 ^ E ∣ 2 * (k + l) - 1 := by
          rw [hkl]
          exact (padicValNat_dvd_iff_le (show 2 * n - 1 ≠ 0 by omega)).mpr le_rfl
        have h3ndvd : ¬ 3 ^ (E + 1) ∣ 2 * (k + l) - 1 := by
          rw [hkl]
          intro h
          have := (padicValNat_dvd_iff_le (show 2 * n - 1 ≠ 0 by omega)).mp h
          omega
        have hsub : Finset.Icc 1 (E + 1) ⊆ Finset.Ico 1 b := by
          intro x hx
          simp only [Finset.mem_Icc, Finset.mem_Ico] at hx ⊢
          have : E + 2 ≤ b := le_max_right _ _
          omega
        have hsplit : ∑ i ∈ Finset.Icc 1 (E + 1), deltaFloor k l (3 ^ i) =
            (∑ i ∈ Finset.Icc 1 E, deltaFloor k l (3 ^ i)) + deltaFloor k l (3 ^ (E + 1)) := by
          rw [show Finset.Icc 1 (E + 1) = insert (E + 1) (Finset.Icc 1 E) by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
          rw [Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), add_comm]
        have hle_sum : E ≤ ∑ i ∈ Finset.Icc 1 (E + 1), deltaFloor k l (3 ^ i) := by
          rw [hsplit]
          rcases three_ind_step k l (by omega) E (by omega) h3dvd with hgood | ⟨hnear, hsym⟩
          · omega
          · rcases hsym with ⟨hkE, hlE⟩ | ⟨hkE, hlE⟩
            · have := three_extra_step (by omega) (by omega) h3ndvd hkE hlE
              omega
            · have hndvd' : ¬ 3 ^ (E + 1) ∣ 2 * (l + k) - 1 := by rwa [add_comm k l] at h3ndvd
              have h1 := three_extra_step (by omega) (by omega) hndvd' hlE hkE
              have hcomm : deltaFloor k l (3 ^ (E + 1)) = deltaFloor l k (3 ^ (E + 1)) := by
                unfold deltaFloor; rw [add_comm k l, add_comm (fFloor k _)]
              omega
        exact le_trans hle_sum (Finset.sum_le_sum_of_subset hsub)
      · have hp5 : 5 ≤ p := by
          have := hp.two_le
          have h4 : p ≠ 4 := fun h => by subst h; norm_num at hp
          omega
        have hsub : Finset.Icc 1 E ⊆ Finset.Ico 1 b := by
          intro x hx
          simp only [Finset.mem_Icc, Finset.mem_Ico] at hx ⊢
          have : E + 2 ≤ b := le_max_right _ _
          omega
        calc E = ∑ _i ∈ Finset.Icc 1 E, 1 := by simp
          _ ≤ ∑ i ∈ Finset.Icc 1 E, deltaFloor k l (p ^ i) := by
              refine Finset.sum_le_sum fun i hi => ?_
              simp only [Finset.mem_Icc] at hi
              have hd5 : 5 ≤ p ^ i := le_trans hp5 (Nat.le_self_pow (by omega) p)
              have hdvd : p ^ i ∣ 2 * (k + l) - 1 := by
                rw [hkl]
                exact (padicValNat_dvd_iff_le (show 2 * n - 1 ≠ 0 by omega)).mpr hi.2
              have h := delta_ge_one_of_dvd_odd (by omega) hd5 (hpow_odd i) hdvd
              unfold deltaFloor
              omega
          _ ≤ ∑ i ∈ Finset.Ico 1 b, deltaFloor k l (p ^ i) :=
              Finset.sum_le_sum_of_subset hsub
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private lemma denom_dvd_SNat {n : ℕ} (hn : 1 ≤ n) :
    (2 * n - 1) * (3 * n).choose n ∣ SNat n := by
  unfold SNat
  refine Finset.dvd_sum fun k hk => ?_
  exact denom_dvd_term hn (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

private def s2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

private lemma s2_two_mul (n : ℕ) : s2 (2 * n) = s2 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [s2]
  · unfold s2
    rw [Nat.digits_def' (by decide) (by omega)]
    simp [Nat.mul_mod_right, Nat.mul_div_right _ (by decide : 0 < 2)]

private lemma s2_two_mul_add_one (n : ℕ) : s2 (2 * n + 1) = s2 n + 1 := by
  unfold s2
  rw [Nat.digits_def' (by decide) (by omega)]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2]
  simp [add_comm]

private lemma s2_pos {n : ℕ} (hn : 0 < n) : 1 ≤ s2 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hpar : n % 2 = 0
    · have : n = 2 * (n / 2) := by omega
      rw [this, s2_two_mul]
      exact ih (n / 2) (by omega) (by omega)
    · have : n = 2 * (n / 2) + 1 := by omega
      rw [this, s2_two_mul_add_one]
      omega

private lemma s2_eq_one_iff {n : ℕ} (hn : 0 < n) : s2 n = 1 ↔ ∃ k : ℕ, n = 2 ^ k := by
  constructor
  · intro hs
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hpar : n % 2 = 0
      · have heq : n = 2 * (n / 2) := by omega
        rw [heq, s2_two_mul] at hs
        obtain ⟨k, hk⟩ := ih (n / 2) (by omega) (by omega) hs
        exact ⟨k + 1, by rw [heq, hk, pow_succ']⟩
      · have heq : n = 2 * (n / 2) + 1 := by omega
        rw [heq, s2_two_mul_add_one] at hs
        have h0 : n / 2 = 0 := by
          by_contra h
          have := s2_pos (Nat.pos_of_ne_zero h)
          omega
        exact ⟨0, by omega⟩
  · rintro ⟨k, rfl⟩
    clear hn
    induction k with
    | zero => decide
    | succ k ih => rw [pow_succ', s2_two_mul, ih]

private lemma s2_three_mul_ge_two {n : ℕ} (hn : 0 < n) : 2 ≤ s2 (3 * n) := by
  have h1 : 1 ≤ s2 (3 * n) := s2_pos (by omega)
  by_contra h
  have hs1 : s2 (3 * n) = 1 := by omega
  obtain ⟨k, hk⟩ := (s2_eq_one_iff (by omega)).mp hs1
  have h3dvd : 3 ∣ 2 ^ k := ⟨n, hk.symm⟩
  have h3_2 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3dvd
  omega

private lemma s2_three_mul_two_pow (k : ℕ) : s2 (3 * 2 ^ k) = 2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) by ring, s2_two_mul, ih]

private lemma padicValNat_two_factorial (n : ℕ) : padicValNat 2 n.factorial = n - s2 n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simpa [s2] using sub_one_mul_padicValNat_factorial (p := 2) n

private lemma s2_le (n : ℕ) : s2 n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [s2]
    · by_cases hpar : n % 2 = 0
      · have heq : n = 2 * (n / 2) := by omega
        have hih := ih (n / 2) (by omega)
        conv_lhs => rw [heq]
        rw [s2_two_mul]
        omega
      · have heq : n = 2 * (n / 2) + 1 := by omega
        have hih := ih (n / 2) (by omega)
        conv_lhs => rw [heq]
        rw [s2_two_mul_add_one]
        omega

private lemma padicValNat_two_tNat (k : ℕ) : padicValNat 2 (tNat k) = 2 * s2 k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac := congrArg (padicValNat 2) (tNat_factorial_eq k)
  have ht0 : tNat k ≠ 0 := (tNat_pos k).ne'
  have h30 : (3 * k).factorial ≠ 0 := Nat.factorial_ne_zero _
  have h20 : (2 * k).factorial ≠ 0 := Nat.factorial_ne_zero _
  have h10 : k.factorial ≠ 0 := Nat.factorial_ne_zero _
  have hm1 : tNat k * (3 * k).factorial ≠ 0 := mul_ne_zero ht0 h30
  have hm2 : tNat k * (3 * k).factorial * (2 * k).factorial ≠ 0 := mul_ne_zero hm1 h20
  rw [padicValNat.mul hm2 h10, padicValNat.mul hm1 h20, padicValNat.mul ht0 h30] at hfac
  simp only [padicValNat_two_factorial] at hfac
  have h6 : s2 (6 * k) = s2 (3 * k) := by
    rw [show 6 * k = 2 * (3 * k) by omega, s2_two_mul]
  have h2 : s2 (2 * k) = s2 k := s2_two_mul k
  have hle6 := s2_le (6 * k)
  have hle3 := s2_le (3 * k)
  have hle2 := s2_le (2 * k)
  have hle1 := s2_le k
  omega

private lemma padicValNat_two_choose3n (n : ℕ) :
    padicValNat 2 ((3 * n).choose n) + s2 (3 * n) = 2 * s2 n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac := congrArg (padicValNat 2) (choose3n_factorial_eq n)
  have hc0 : (3 * n).choose n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have h10 : n.factorial ≠ 0 := Nat.factorial_ne_zero _
  have h20 : (2 * n).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hm1 : (3 * n).choose n * n.factorial ≠ 0 := mul_ne_zero hc0 h10
  rw [padicValNat.mul hm1 h20, padicValNat.mul hc0 h10] at hfac
  simp only [padicValNat_two_factorial] at hfac
  have h2 : s2 (2 * n) = s2 n := s2_two_mul n
  have hle3 := s2_le (3 * n)
  have hle2 := s2_le (2 * n)
  have hle1 := s2_le n
  omega

private lemma padicValNat_two_choose {n k : ℕ} (hkn : k ≤ n) :
    padicValNat 2 (n.choose k) + s2 n = s2 k + s2 (n - k) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac := congrArg (padicValNat 2) (Nat.choose_mul_factorial_mul_factorial hkn)
  have hc0 : n.choose k ≠ 0 := (Nat.choose_pos hkn).ne'
  have h10 : k.factorial ≠ 0 := Nat.factorial_ne_zero _
  have h20 : (n - k).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hm1 : n.choose k * k.factorial ≠ 0 := mul_ne_zero hc0 h10
  rw [padicValNat.mul hm1 h20, padicValNat.mul hc0 h10] at hfac
  simp only [padicValNat_two_factorial] at hfac
  have hlen := s2_le n
  have hlek := s2_le k
  have hles := s2_le (n - k)
  omega

private lemma count_odd_choose (n : ℕ) :
    ((Finset.range (n + 1)).filter (fun k => n.choose k % 2 = 1)).card = 2 ^ s2 n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · decide
    · set m := n / 2
      have hmlt : m < n := by omega
      have hlucas : ∀ k : ℕ, n.choose k % 2 = ((n % 2).choose (k % 2) * m.choose (k / 2)) % 2 := by
        intro k
        exact Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := 2)
      by_cases hpar : n % 2 = 0
      · have heq : n = 2 * m := by omega
        have hbij :
            (Finset.range (n + 1)).filter (fun k => n.choose k % 2 = 1) =
              ((Finset.range (m + 1)).filter (fun j => m.choose j % 2 = 1)).image (fun j => 2 * j) := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
          constructor
          · rintro ⟨hk, hodd⟩
            have hl := hlucas k
            rw [hpar] at hl
            have hk0 : k % 2 = 0 := by
              by_contra h
              have hk1 : k % 2 = 1 := by omega
              rw [hk1] at hl
              simp at hl
              omega
            refine ⟨k / 2, ⟨by omega, ?_⟩, by omega⟩
            rw [hk0] at hl
            simpa using hodd.symm.trans hl |>.symm
          · rintro ⟨j, ⟨hj, hodd⟩, rfl⟩
            refine ⟨by omega, ?_⟩
            have hl := hlucas (2 * j)
            rw [hpar, Nat.mul_mod_right, Nat.mul_div_right _ (by decide : 0 < 2)] at hl
            simpa [hl] using hodd
        rw [hbij, Finset.card_image_of_injective _ (fun a b h => by omega), ih m hmlt, heq,
          s2_two_mul]
      · have heq : n = 2 * m + 1 := by omega
        have hpar1 : n % 2 = 1 := by omega
        set S := (Finset.range (m + 1)).filter (fun j => m.choose j % 2 = 1)
        have hunion :
            (Finset.range (n + 1)).filter (fun k => n.choose k % 2 = 1) =
              S.image (fun j => 2 * j) ∪ S.image (fun j => 2 * j + 1) := by
          ext k
          simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range, S]
          constructor
          · rintro ⟨hk, hodd⟩
            have hl := hlucas k
            rw [hpar1] at hl
            have hchoose1 : (1 : ℕ).choose (k % 2) = 1 := by
              have : k % 2 = 0 ∨ k % 2 = 1 := by omega
              rcases this with h | h <;> simp [h]
            rw [hchoose1, one_mul] at hl
            have hm_odd : m.choose (k / 2) % 2 = 1 := by omega
            by_cases hkpar : k % 2 = 0
            · left; exact ⟨k / 2, ⟨by omega, hm_odd⟩, by omega⟩
            · right; exact ⟨k / 2, ⟨by omega, hm_odd⟩, by omega⟩
          · rintro (⟨j, ⟨hj, hodd⟩, rfl⟩ | ⟨j, ⟨hj, hodd⟩, rfl⟩)
            · refine ⟨by omega, ?_⟩
              have hl := hlucas (2 * j)
              rw [hpar1, Nat.mul_mod_right, Nat.mul_div_right _ (by decide : 0 < 2)] at hl
              simpa [hl] using hodd
            · refine ⟨by omega, ?_⟩
              have hl := hlucas (2 * j + 1)
              have h1 : (2 * j + 1) % 2 = 1 := by omega
              have h2 : (2 * j + 1) / 2 = j := by omega
              rw [hpar1, h1, h2] at hl
              simpa [hl] using hodd
        have hdisj : Disjoint (S.image (fun j => 2 * j)) (S.image (fun j => 2 * j + 1)) := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          simp only [Finset.mem_image] at hx1 hx2
          rcases hx1 with ⟨a, _, rfl⟩
          rcases hx2 with ⟨b, _, hab⟩
          omega
        rw [hunion, Finset.card_union_of_disjoint hdisj,
          Finset.card_image_of_injective _ (fun a b h => by omega),
          Finset.card_image_of_injective _ (fun a b h => by omega),
          ih m hmlt, heq, s2_two_mul_add_one, pow_succ]
        ring

private lemma central_choose_even {m : ℕ} (hm : 1 ≤ m) : (2 * m).choose m % 2 = 0 := by
  have h1 : (2 * m).choose m = (2 * m - 1).choose (m - 1) + (2 * m - 1).choose m := by
    have h := Nat.choose_succ_succ (2 * m - 1) (m - 1)
    have ha : 2 * m - 1 + 1 = 2 * m := by omega
    have hb : m - 1 + 1 = m := by omega
    simp only [Nat.succ_eq_add_one, ha, hb] at h
    exact h
  have hsymm : (2 * m - 1).choose m = (2 * m - 1).choose (m - 1) := by
    have h := Nat.choose_symm (show m ≤ 2 * m - 1 by omega)
    have hsub : 2 * m - 1 - m = m - 1 := by omega
    rw [hsub] at h
    exact h.symm
  omega

private lemma SNat_two_valuation {n : ℕ} (hn : 1 ≤ n) :
    2 ^ (2 * s2 n + 1) ∣ SNat n ∧
      (2 ^ (2 * s2 n + 2) ∣ SNat n ↔ 2 ≤ s2 n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e := 2 * s2 n
  have hterm_val : ∀ k ≤ n, padicValNat 2 (tNat k * tNat (n - k)) =
      e + 2 * padicValNat 2 (n.choose k) := by
    intro k hkn
    rw [padicValNat.mul (tNat_pos k).ne' (tNat_pos (n - k)).ne',
      padicValNat_two_tNat k, padicValNat_two_tNat (n - k)]
    have hc := padicValNat_two_choose hkn
    omega
  have hterm_dvd : ∀ k ≤ n, 2 ^ e ∣ tNat k * tNat (n - k) := by
    intro k hkn
    rw [padicValNat_dvd_iff_le (Nat.mul_pos (tNat_pos k) (tNat_pos (n - k))).ne', hterm_val k hkn]
    omega
  set u : ℕ → ℕ := fun k => (tNat k * tNat (n - k)) / 2 ^ e
  have hSNat_eq : SNat n = 2 ^ e * ∑ k ∈ Finset.range (n + 1), u k := by
    rw [Finset.mul_sum]
    unfold SNat
    refine Finset.sum_congr rfl fun k hk => ?_
    exact (Nat.mul_div_cancel' (hterm_dvd k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))).symm
  have hu_symm : ∀ k ≤ n, u (n - k) = u k := by
    intro k hkn
    dsimp [u]
    rw [show n - (n - k) = k by omega, mul_comm]
  have hu_mod4_of_even : ∀ k ≤ n, n.choose k % 2 = 0 → u k % 4 = 0 := by
    intro k hkn hev
    have h2c : 2 ^ 1 ∣ n.choose k := by simpa [pow_one] using Nat.dvd_of_mod_eq_zero hev
    have hvc : 1 ≤ padicValNat 2 (n.choose k) :=
      (padicValNat_dvd_iff_le (Nat.choose_pos hkn).ne').mp h2c
    have hdvd4 : 2 ^ (e + 2) ∣ tNat k * tNat (n - k) := by
      rw [padicValNat_dvd_iff_le (Nat.mul_pos (tNat_pos k) (tNat_pos (n - k))).ne', hterm_val k hkn]
      omega
    obtain ⟨q, hq⟩ := hdvd4
    have huq : u k = 4 * q := by
      dsimp [u]
      rw [hq, show 2 ^ (e + 2) = 2 ^ e * 4 by rw [pow_add]; norm_num, mul_assoc,
        Nat.mul_div_cancel_left _ (Nat.two_pow_pos e)]
    omega
  have hu_odd_of_odd : ∀ k ≤ n, n.choose k % 2 = 1 → u k % 2 = 1 := by
    intro k hkn hodd
    have hvc0 : padicValNat 2 (n.choose k) = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      omega
    have hndvd : ¬ 2 ^ (e + 1) ∣ tNat k * tNat (n - k) := by
      rw [padicValNat_dvd_iff_le (Nat.mul_pos (tNat_pos k) (tNat_pos (n - k))).ne',
        hterm_val k hkn, hvc0]
      omega
    by_contra hnot
    have h2u : 2 ∣ u k := Nat.dvd_of_mod_eq_zero (by omega)
    obtain ⟨q, hq⟩ := h2u
    apply hndvd
    refine ⟨q, ?_⟩
    have hmul := Nat.mul_div_cancel' (hterm_dvd k hkn)
    dsimp [u] at hq
    rw [hq] at hmul
    rw [← hmul, pow_succ]
    ring
  set R := Finset.range (n + 1)
  set A := R.filter (fun k => 2 * k < n)
  set B := R.filter (fun k => n < 2 * k)
  set M := R.filter (fun k => 2 * k = n)
  have hsum_split : ∑ k ∈ R, u k = 2 * (∑ k ∈ A, u k) + ∑ k ∈ M, u k := by
    have hR : R = (A ∪ B) ∪ M := by
      ext k
      simp only [Finset.mem_union, Finset.mem_filter, A, B, M]
      constructor
      · intro hk
        by_cases h1 : 2 * k < n
        · exact Or.inl (Or.inl ⟨hk, h1⟩)
        · by_cases h2 : n < 2 * k
          · exact Or.inl (Or.inr ⟨hk, h2⟩)
          · exact Or.inr ⟨hk, by omega⟩
      · rintro ((⟨hk, _⟩ | ⟨hk, _⟩) | ⟨hk, _⟩) <;> exact hk
    have hdAB : Disjoint A B := by
      rw [Finset.disjoint_left]; intro k h1 h2
      simp only [Finset.mem_filter, A, B] at h1 h2; omega
    have hdABM : Disjoint (A ∪ B) M := by
      rw [Finset.disjoint_left]; intro k h1 h2
      simp only [Finset.mem_union, Finset.mem_filter, A, B, M] at h1 h2
      rcases h1 with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    have hsumB : ∑ k ∈ B, u k = ∑ k ∈ A, u k := by
      refine Finset.sum_bij (fun k _ => n - k) ?_ ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_range, A, B, R] at hk ⊢
        omega
      · intro a ha b hb hab
        simp only [Finset.mem_filter, Finset.mem_range, B, R] at ha hb
        omega
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_range, A, B, R] at hk ⊢
        exact ⟨n - k, ⟨by omega, by omega⟩, by omega⟩
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_range, B, R] at hk
        exact (hu_symm k (by omega)).symm
    conv_lhs => rw [hR]
    rw [Finset.sum_union hdABM, Finset.sum_union hdAB, hsumB, two_mul]
  have hM_mod4 : (∑ k ∈ M, u k) % 4 = 0 := by
    have hdvd : 4 ∣ ∑ k ∈ M, u k := by
      refine Finset.dvd_sum fun k hk => ?_
      simp only [Finset.mem_filter, Finset.mem_range, M, R] at hk
      have heq : n = 2 * k := by omega
      have hce : n.choose k % 2 = 0 := by rw [heq]; exact central_choose_even (by omega)
      exact Nat.dvd_of_mod_eq_zero (hu_mod4_of_even k (by omega) hce)
    exact Nat.mod_eq_zero_of_dvd hdvd
  have hA_odd_card : 2 * (A.filter (fun k => n.choose k % 2 = 1)).card = 2 ^ s2 n := by
    rw [← count_odd_choose n]
    set O := R.filter (fun k => n.choose k % 2 = 1)
    set OA := A.filter (fun k => n.choose k % 2 = 1)
    set OB := B.filter (fun k => n.choose k % 2 = 1)
    have hO : O = OA ∪ OB := by
      ext k
      simp only [Finset.mem_union, Finset.mem_filter, O, OA, OB, A, B, R, Finset.mem_range]
      constructor
      · rintro ⟨hk, hodd⟩
        by_cases h1 : 2 * k < n
        · exact Or.inl ⟨⟨hk, h1⟩, hodd⟩
        · by_cases h2 : n < 2 * k
          · exact Or.inr ⟨⟨hk, h2⟩, hodd⟩
          · exfalso
            have heq : n = 2 * k := by omega
            have := central_choose_even (m := k) (by omega)
            rw [← heq] at this
            omega
      · rintro (⟨⟨hk, _⟩, hodd⟩ | ⟨⟨hk, _⟩, hodd⟩) <;> exact ⟨hk, hodd⟩
    have hdO : Disjoint OA OB := by
      rw [Finset.disjoint_left]; intro k h1 h2
      simp only [Finset.mem_filter, OA, OB, A, B] at h1 h2; omega
    have hcardOB : OB.card = OA.card := by
      refine Finset.card_bij (fun k _ => n - k) ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_range, OA, OB, A, B, R] at hk ⊢
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        rw [Nat.choose_symm (by omega)]
        exact hk.2
      · intro a ha b hb hab
        simp only [Finset.mem_filter, Finset.mem_range, OB, B, R] at ha hb
        omega
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_range, OA, OB, A, B, R] at hk ⊢
        refine ⟨n - k, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
        rw [Nat.choose_symm (by omega)]
        exact hk.2
    rw [hO, Finset.card_union_of_disjoint hdO, hcardOB, two_mul]
  have hsumA_mod2 : (∑ k ∈ A, u k) % 2 = (A.filter (fun k => n.choose k % 2 = 1)).card % 2 := by
    have h1 : ∀ k ∈ A, u k % 2 = if n.choose k % 2 = 1 then 1 else 0 := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range, A, R] at hk
      by_cases hodd : n.choose k % 2 = 1
      · simp [hodd, hu_odd_of_odd k (by omega) hodd]
      · have hev : n.choose k % 2 = 0 := by omega
        have h4 := hu_mod4_of_even k (by omega) hev
        simp [hodd]
        omega
    rw [Finset.sum_nat_mod, Finset.sum_congr rfl h1, ← Finset.card_filter]
  have hA_card_eq : (A.filter (fun k => n.choose k % 2 = 1)).card = 2 ^ (s2 n - 1) := by
    have hs1 : 1 ≤ s2 n := s2_pos hn
    have hpow : 2 ^ s2 n = 2 * 2 ^ (s2 n - 1) := by
      conv_lhs => rw [show s2 n = (s2 n - 1) + 1 by omega]
      rw [pow_succ']
    omega
  have hsum_even : 2 ∣ ∑ k ∈ R, u k := by
    rw [hsum_split]
    omega
  constructor
  · rw [hSNat_eq, pow_succ]
    exact Nat.mul_dvd_mul_left (2 ^ e) hsum_even
  · rw [hSNat_eq, pow_add, Nat.mul_dvd_mul_iff_left (Nat.two_pow_pos e)]
    have hmod4 : (∑ k ∈ R, u k) % 4 = (2 * (2 ^ (s2 n - 1) % 2)) % 4 := by
      rw [hsum_split]
      have : (2 * ∑ k ∈ A, u k) % 4 = 2 * ((∑ k ∈ A, u k) % 2) := by omega
      rw [hsumA_mod2, hA_card_eq] at this
      omega
    rw [show (2 : ℕ) ^ 2 = 4 by decide, Nat.dvd_iff_mod_eq_zero, hmod4]
    constructor
    · intro h0
      by_contra hlt
      have hs1 : s2 n = 1 := by have := s2_pos hn; omega
      rw [hs1] at h0
      norm_num at h0
    · intro hs2
      have hpow2 : 2 ^ (s2 n - 1) % 2 = 0 := by
        conv_lhs => rw [show s2 n - 1 = (s2 n - 2) + 1 by omega]
        rw [pow_succ]
        omega
      rw [hpow2]

end OeisA189286Proof

theorem OMA.solution : type_of% @OeisA189286.conjecture_3 := by
  intro n hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := (2 * n - 1) * (3 * n).choose n
  have hDpos : 0 < D := Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  have hdvd : D ∣ OeisA189286Proof.SNat n := OeisA189286Proof.denom_dvd_SNat hn
  set q := OeisA189286Proof.SNat n / D
  have hSNat : OeisA189286Proof.SNat n = D * q := (Nat.mul_div_cancel' hdvd).symm
  have ha_eq : OeisA189286.a n = (q : ℚ) := by
    unfold OeisA189286.a
    have hnum : (∑ k ∈ Finset.range (n + 1), OeisA189286.tTerm k * OeisA189286.tTerm (n - k)) =
        (OeisA189286Proof.SNat n : ℚ) := by
      unfold OeisA189286Proof.SNat OeisA189286.tTerm OeisA189286Proof.tNat
      push_cast
      rfl
    have hden : ((2 * (n : ℚ)) - 1) * ((3 * n).choose n : ℚ) = (D : ℚ) := by
      dsimp [D]
      have hsub : ((2 * n - 1 : ℕ) : ℚ) = 2 * (n : ℚ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        rfl
      rw [Nat.cast_mul, hsub]
    rw [hnum, hden, hSNat]
    have hDQ : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hDpos.ne'
    push_cast
    field_simp
  have hSpos : 0 < OeisA189286Proof.SNat n := by
    unfold OeisA189286Proof.SNat
    have h0 : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    calc 0 < OeisA189286Proof.tNat 0 * OeisA189286Proof.tNat (n - 0) :=
          Nat.mul_pos (OeisA189286Proof.tNat_pos 0) (OeisA189286Proof.tNat_pos _)
      _ ≤ ∑ k ∈ Finset.range (n + 1),
            OeisA189286Proof.tNat k * OeisA189286Proof.tNat (n - k) :=
          Finset.single_le_sum
            (f := fun k => OeisA189286Proof.tNat k * OeisA189286Proof.tNat (n - k))
            (fun _ _ => Nat.zero_le _) h0
  have hqpos : 0 < q := by
    by_contra h
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos h
    have hS0 : OeisA189286Proof.SNat n = 0 := by rw [hSNat, hq0, mul_zero]
    omega
  have hvD : padicValNat 2 D + OeisA189286Proof.s2 (3 * n) = 2 * OeisA189286Proof.s2 n := by
    dsimp [D]
    rw [padicValNat.mul (by omega) (Nat.choose_pos (by omega)).ne',
      padicValNat.eq_zero_of_not_dvd (by omega), zero_add]
    exact OeisA189286Proof.padicValNat_two_choose3n n
  have hvS : padicValNat 2 (OeisA189286Proof.SNat n) = padicValNat 2 D + padicValNat 2 q := by
    rw [hSNat, padicValNat.mul hDpos.ne' hqpos.ne']
  obtain ⟨hdvd1, hdvd2_iff⟩ := OeisA189286Proof.SNat_two_valuation hn
  have hvS_ge1 : 2 * OeisA189286Proof.s2 n + 1 ≤ padicValNat 2 (OeisA189286Proof.SNat n) :=
    (padicValNat_dvd_iff_le hSpos.ne').mp hdvd1
  have hvq_ge3 : 3 ≤ padicValNat 2 q := by
    have hs3 := OeisA189286Proof.s2_three_mul_ge_two hn
    omega
  have h8q : 8 ∣ q := by
    have := (padicValNat_dvd_iff_le hqpos.ne').mpr hvq_ge3
    simpa using this
  refine ⟨(q / 8 : ℕ), ?_, ?_⟩
  · rw [ha_eq]
    have hmul : 8 * (q / 8) = q := Nat.mul_div_cancel' h8q
    exact_mod_cast hmul.symm
  · rw [← OeisA189286Proof.s2_eq_one_iff hn]
    have hodd_iff : Odd ((q / 8 : ℕ) : ℤ) ↔ ¬ (16 ∣ q) := by
      have hmul : 8 * (q / 8) = q := Nat.mul_div_cancel' h8q
      constructor
      · rintro ⟨t, ht⟩ ⟨r, hr⟩
        have : (q / 8 : ℕ) = 2 * r := by omega
        omega
      · intro hnot16
        have hodd_nat : (q / 8) % 2 = 1 := by
          by_contra h
          have : 2 ∣ (q / 8) := Nat.dvd_of_mod_eq_zero (by omega)
          obtain ⟨r, hr⟩ := this
          exact hnot16 ⟨r, by omega⟩
        refine ⟨((q / 8) / 2 : ℕ), ?_⟩
        exact_mod_cast (show q / 8 = 2 * ((q / 8) / 2) + 1 by omega)
    rw [hodd_iff]
    have h16_iff : 16 ∣ q ↔ 4 ≤ padicValNat 2 q := by
      simpa using (padicValNat_dvd_iff_le (p := 2) (n := 4) hqpos.ne')
    rw [h16_iff]
    constructor
    · intro hlt4
      by_contra hne1
      have hs2 : 2 ≤ OeisA189286Proof.s2 n := by
        have := OeisA189286Proof.s2_pos hn
        omega
      have hdvd2 : 2 ^ (2 * OeisA189286Proof.s2 n + 2) ∣ OeisA189286Proof.SNat n :=
        hdvd2_iff.mpr hs2
      have hvS_ge2 : 2 * OeisA189286Proof.s2 n + 2 ≤ padicValNat 2 (OeisA189286Proof.SNat n) :=
        (padicValNat_dvd_iff_le hSpos.ne').mp hdvd2
      have hs3 := OeisA189286Proof.s2_three_mul_ge_two hn
      omega
    · intro hs1
      obtain ⟨k, rfl⟩ := (OeisA189286Proof.s2_eq_one_iff hn).mp hs1
      have hs3 : OeisA189286Proof.s2 (3 * 2 ^ k) = 2 := OeisA189286Proof.s2_three_mul_two_pow k
      have hndvd2 : ¬ 2 ^ (2 * OeisA189286Proof.s2 (2 ^ k) + 2) ∣ OeisA189286Proof.SNat (2 ^ k) := by
        rw [hdvd2_iff, hs1]
        omega
      have hvS_lt2 : ¬ 2 * OeisA189286Proof.s2 (2 ^ k) + 2 ≤
          padicValNat 2 (OeisA189286Proof.SNat (2 ^ k)) := by
        intro h
        exact hndvd2 ((padicValNat_dvd_iff_le hSpos.ne').mpr h)
      omega
