import FormalConjectures.ErdosProblems.«700»

/-!
Proof of `Erdos700.erdos_700.parts.ii`: there are infinitely many composite $n > 1$ with
$f(n)^2 > n$, constructed as $n = p q r$ for prime triples $p < q < r$ satisfying
$q - p < r - q$ and $2(r - p)^2 < p$.
-/

namespace Erdos700Proof

private lemma lucas_dvd_of_mod_lt {P A B : ℕ} (hP : P.Prime) (hlt : A % P < B % P) :
    P ∣ A.choose B := by
  have : Fact P.Prime := ⟨hP⟩
  have hmod : A.choose B ≡ (A % P).choose (B % P) * (A / P).choose (B / P) [MOD P] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  rw [Nat.choose_eq_zero_of_lt hlt, zero_mul] at hmod
  exact Nat.modEq_zero_iff_dvd.mp hmod

private lemma lucas_dvd_of_div_dvd {P A B : ℕ} (hP : P.Prime) (hdvd : P ∣ (A / P).choose (B / P)) :
    P ∣ A.choose B := by
  have : Fact P.Prime := ⟨hP⟩
  have hmod : A.choose B ≡ (A % P).choose (B % P) * (A / P).choose (B / P) [MOD P] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have h0 : (A / P).choose (B / P) ≡ 0 [MOD P] := Nat.modEq_zero_iff_dvd.mpr hdvd
  have hmul : (A % P).choose (B % P) * (A / P).choose (B / P) ≡ 0 [MOD P] := by
    simpa using h0.mul_left ((A % P).choose (B % P))
  exact Nat.modEq_zero_iff_dvd.mp (hmod.trans hmul)

private lemma lucas_dvd_of_div_mod_lt {P A B : ℕ} (hP : P.Prime)
    (hlt : (A / P) % P < (B / P) % P) : P ∣ A.choose B :=
  lucas_dvd_of_div_dvd hP (lucas_dvd_of_mod_lt hP hlt)

private lemma case_pq {p q r m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hqr : q < r) (hgap : q - p < r - q) (hsq : 2 * (r - p) ^ 2 < p)
    (hm1 : 1 ≤ m) (hmr : m ≤ r / 2) :
    p ∣ (p * q * r).choose (m * p * q) ∨ q ∣ (p * q * r).choose (m * p * q) := by
  set a := q - p
  set b := r - p
  set c := r - q
  have hq_eq : q = p + a := by omega
  have hr_eq : r = p + b := by omega
  have hrc_eq : r = q + c := by omega
  have hb_eq : b = a + c := by omega
  have ha_pos : 0 < a := by omega
  have hc_gt : a < c := hgap
  have hb_ge2 : 2 ≤ b := by omega
  have h2b2 : 2 * b * b < p := by nlinarith only [hsq]
  have h2b_lt_p : 2 * b < p := by nlinarith only [h2b2, hb_ge2]
  have h2m_le : 2 * m ≤ r := by omega
  have hmq_lt : m * q < p * p := by
    have h1 : 2 * (m * q) ≤ r * q := by nlinarith only [h2m_le]
    have h2 : r * q = p * p + (a + b) * p + a * b := by rw [hq_eq, hr_eq]; ring
    have h3 : a + b < p := by omega
    have h4 : a * b < p := by nlinarith only [h2b2, hb_eq]
    nlinarith only [h1, h2, h3, h4, hp.pos]
  by_cases hm_big : a + b < m
  · left
    have hdiv1 : (p * q * r) / p = q * r := by
      rw [show p * q * r = p * (q * r) by ring, Nat.mul_div_cancel_left _ hp.pos]
    have hdiv2 : (m * p * q) / p = m * q := by
      rw [show m * p * q = p * (m * q) by ring, Nat.mul_div_cancel_left _ hp.pos]
    apply lucas_dvd_of_div_dvd hp
    rw [hdiv1, hdiv2]
    apply lucas_dvd_of_div_mod_lt hp
    have hqr_exp : q * r = p * (p + (a + b)) + a * b := by rw [hq_eq, hr_eq]; ring
    have hab_lt : a * b < p := by nlinarith only [h2b2, hb_eq]
    have hab_sum_lt : a + b < p := by omega
    have hqr_div : (q * r) / p = p + (a + b) := by
      rw [hqr_exp, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hab_lt, add_zero]
    have hqr_d1 : ((q * r) / p) % p = a + b := by
      rw [hqr_div, Nat.add_mod_left, Nat.mod_eq_of_lt hab_sum_lt]
    have hmq_div_lt : (m * q) / p < p := (Nat.div_lt_iff_lt_mul hp.pos).mpr hmq_lt
    have hmq_d1 : ((m * q) / p) % p = (m * q) / p := Nat.mod_eq_of_lt hmq_div_lt
    have hmq_ge : m ≤ (m * q) / p := by
      rw [Nat.le_div_iff_mul_le hp.pos]
      nlinarith only [hpq]
    omega
  · right
    have hdiv1 : (p * q * r) / q = p * r := by
      rw [show p * q * r = q * (p * r) by ring, Nat.mul_div_cancel_left _ hq.pos]
    have hdiv2 : (m * p * q) / q = m * p := by
      rw [show m * p * q = q * (m * p) by ring, Nat.mul_div_cancel_left _ hq.pos]
    apply lucas_dvd_of_div_dvd hq
    rw [hdiv1, hdiv2]
    have hac_pos : 0 < a * c := Nat.mul_pos ha_pos (by omega)
    have hma_pos : 0 < m * a := Nat.mul_pos hm1 ha_pos
    have hac_lt : a * c < q := by nlinarith only [h2b2, hb_eq, hpq]
    have hma_lt : m * a < q := by nlinarith only [hm_big, h2b2, hb_eq, hpq]
    have hca_lt : c - a - 1 < q := by omega
    have hpr_exp : p * r = q * (q + (c - a - 1)) + (q - a * c) := by
      set t := c - a - 1
      have hc_decomp : c = t + a + 1 := by omega
      have h1 : p * r + a * c = q * (q + t) + q := by
        rw [hrc_eq, hq_eq, hc_decomp]; ring
      omega
    have hmp_exp : m * p = q * (m - 1) + (q - m * a) := by
      set m' := m - 1
      have hm_decomp : m = m' + 1 := by omega
      have h1 : m * p + m * a = q * m' + q := by
        calc m * p + m * a = m * (p + a) := by ring
          _ = m * q := by rw [← hq_eq]
          _ = q * m' + q := by rw [hm_decomp]; ring
      omega
    have hpr_mod : (p * r) % q = q - a * c := by
      rw [hpr_exp, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    have hmp_mod : (m * p) % q = q - m * a := by
      rw [hmp_exp, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    by_cases hmc : m < c
    · apply lucas_dvd_of_mod_lt hq
      rw [hpr_mod, hmp_mod]
      have : m * a < a * c := by nlinarith only [hmc, ha_pos]
      omega
    · apply lucas_dvd_of_div_mod_lt hq
      have hpr_div : (p * r) / q = q + (c - a - 1) := by
        rw [hpr_exp, Nat.mul_add_div hq.pos, Nat.div_eq_of_lt (by omega), add_zero]
      have hpr_d1 : ((p * r) / q) % q = c - a - 1 := by
        rw [hpr_div, Nat.add_mod_left, Nat.mod_eq_of_lt hca_lt]
      have hmp_div : (m * p) / q = m - 1 := by
        rw [hmp_exp, Nat.mul_add_div hq.pos, Nat.div_eq_of_lt (by omega), add_zero]
      have hm1_lt : m - 1 < q := by omega
      have hmp_d1 : ((m * p) / q) % q = m - 1 := by
        rw [hmp_div, Nat.mod_eq_of_lt hm1_lt]
      omega

private lemma case_pr {p q r m : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (hsq : 2 * (r - p) ^ 2 < p)
    (hm1 : 1 ≤ m) (hmq : m ≤ q / 2) :
    p ∣ (p * q * r).choose (m * p * r) ∨ r ∣ (p * q * r).choose (m * p * r) := by
  set a := q - p
  set b := r - p
  set c := r - q
  have hq_eq : q = p + a := by omega
  have hr_eq : r = p + b := by omega
  have hb_eq : b = a + c := by omega
  have hb_ge2 : 2 ≤ b := by omega
  have h2b2 : 2 * b * b < p := by nlinarith only [hsq]
  have h2b_lt_p : 2 * b < p := by nlinarith only [h2b2, hb_ge2]
  have h2m_le : 2 * m ≤ q := by omega
  have hmr_lt : m * r < p * p := by
    have h1 : 2 * (m * r) ≤ q * r := by nlinarith only [h2m_le]
    have h2 : q * r = p * p + (a + b) * p + a * b := by rw [hq_eq, hr_eq]; ring
    have h3 : a + b < p := by omega
    have h4 : a * b < p := by nlinarith only [h2b2, hb_eq]
    nlinarith only [h1, h2, h3, h4, hp.pos]
  by_cases hm_big : a + b < m
  · left
    have hdiv1 : (p * q * r) / p = q * r := by
      rw [show p * q * r = p * (q * r) by ring, Nat.mul_div_cancel_left _ hp.pos]
    have hdiv2 : (m * p * r) / p = m * r := by
      rw [show m * p * r = p * (m * r) by ring, Nat.mul_div_cancel_left _ hp.pos]
    apply lucas_dvd_of_div_dvd hp
    rw [hdiv1, hdiv2]
    apply lucas_dvd_of_div_mod_lt hp
    have hqr_exp : q * r = p * (p + (a + b)) + a * b := by rw [hq_eq, hr_eq]; ring
    have hab_lt : a * b < p := by nlinarith only [h2b2, hb_eq]
    have hab_sum_lt : a + b < p := by omega
    have hqr_div : (q * r) / p = p + (a + b) := by
      rw [hqr_exp, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hab_lt, add_zero]
    have hqr_d1 : ((q * r) / p) % p = a + b := by
      rw [hqr_div, Nat.add_mod_left, Nat.mod_eq_of_lt hab_sum_lt]
    have hmr_div_lt : (m * r) / p < p := (Nat.div_lt_iff_lt_mul hp.pos).mpr hmr_lt
    have hmr_d1 : ((m * r) / p) % p = (m * r) / p := Nat.mod_eq_of_lt hmr_div_lt
    have hmr_ge : m ≤ (m * r) / p := by
      rw [Nat.le_div_iff_mul_le hp.pos]
      nlinarith only [hpq, hqr]
    omega
  · right
    have hdiv1 : (p * q * r) / r = p * q := Nat.mul_div_cancel _ hr.pos
    have hdiv2 : (m * p * r) / r = m * p := Nat.mul_div_cancel _ hr.pos
    apply lucas_dvd_of_div_dvd hr
    rw [hdiv1, hdiv2]
    apply lucas_dvd_of_mod_lt hr
    have hmb_pos : 0 < m * b := Nat.mul_pos hm1 (by omega)
    have hbc_lt : b * c < r := by nlinarith only [h2b2, hb_eq, hpq, hqr]
    have hmb_lt : m * b < r := by nlinarith only [hm_big, h2b2, hb_eq, hpq, hqr]
    have hbc_le_r : b + c ≤ r := by omega
    have hpq_exp : p * q = r * (r - b - c) + b * c := by
      have hr_decomp : r = (r - b - c) + b + c := by omega
      have h1 : p * q + r * (b + c) = r * r + b * c := by
        have hp1 : p + b = r := by omega
        have hq1 : q + c = r := by omega
        nlinarith only [hp1, hq1]
      have h2 : r * r = r * (r - b - c) + r * (b + c) := by
        calc r * r = r * ((r - b - c) + b + c) := by rw [← hr_decomp]
          _ = r * (r - b - c) + r * (b + c) := by ring
      omega
    have hmp_exp : m * p = r * (m - 1) + (r - m * b) := by
      set m' := m - 1
      have hm_decomp : m = m' + 1 := by omega
      have h1 : m * p + m * b = r * m' + r := by
        calc m * p + m * b = m * (p + b) := by ring
          _ = m * r := by rw [← hr_eq]
          _ = r * m' + r := by rw [hm_decomp]; ring
      omega
    have hpq_mod : (p * q) % r = b * c := by
      rw [hpq_exp, Nat.mul_add_mod, Nat.mod_eq_of_lt hbc_lt]
    have hmp_mod : (m * p) % r = r - m * b := by
      rw [hmp_exp, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    rw [hpq_mod, hmp_mod]
    have hsum : b * c + m * b < r := by nlinarith only [hm_big, h2b2, hb_eq, hpq, hqr]
    omega

private lemma case_qr {p q r m : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (hgap : q - p < r - q) (hsq : 2 * (r - p) ^ 2 < p)
    (hm1 : 1 ≤ m) (hmp : m ≤ p / 2) :
    q ∣ (p * q * r).choose (m * q * r) ∨ r ∣ (p * q * r).choose (m * q * r) := by
  set a := q - p
  set b := r - p
  set c := r - q
  have hq_eq : q = p + a := by omega
  have hr_eq : r = p + b := by omega
  have hrc_eq : r = q + c := by omega
  have hb_eq : b = a + c := by omega
  have hb_ge2 : 2 ≤ b := by omega
  have h2b2 : 2 * b * b < p := by nlinarith only [hsq]
  have h2b_lt_p : 2 * b < p := by nlinarith only [h2b2, hb_ge2]
  have h2m_le : 2 * m ≤ p := by omega
  have hmr_lt : m * r < q * q := by
    have h1 : 2 * (m * r) ≤ p * r := by nlinarith only [h2m_le]
    have h2 : p * r < 2 * (q * q) := by nlinarith only [hr_eq, h2b_lt_p, hpq]
    omega
  by_cases hm_big : c - a ≤ m
  · left
    have hdiv1 : (p * q * r) / q = p * r := by
      rw [show p * q * r = q * (p * r) by ring, Nat.mul_div_cancel_left _ hq.pos]
    have hdiv2 : (m * q * r) / q = m * r := by
      rw [show m * q * r = q * (m * r) by ring, Nat.mul_div_cancel_left _ hq.pos]
    apply lucas_dvd_of_div_dvd hq
    rw [hdiv1, hdiv2]
    apply lucas_dvd_of_div_mod_lt hq
    have hac_pos : 0 < a * c := Nat.mul_pos (by omega) (by omega)
    have hac_lt : a * c < q := by nlinarith only [h2b2, hb_eq, hpq]
    have hca_lt : c - a - 1 < q := by omega
    have hpr_exp : p * r = q * (q + (c - a - 1)) + (q - a * c) := by
      set t := c - a - 1
      have hc_decomp : c = t + a + 1 := by omega
      have h1 : p * r + a * c = q * (q + t) + q := by
        rw [hrc_eq, hq_eq, hc_decomp]; ring
      omega
    have hpr_div : (p * r) / q = q + (c - a - 1) := by
      rw [hpr_exp, Nat.mul_add_div hq.pos, Nat.div_eq_of_lt (by omega), add_zero]
    have hpr_d1 : ((p * r) / q) % q = c - a - 1 := by
      rw [hpr_div, Nat.add_mod_left, Nat.mod_eq_of_lt hca_lt]
    have hmr_div_lt : (m * r) / q < q := (Nat.div_lt_iff_lt_mul hq.pos).mpr hmr_lt
    have hmr_d1 : ((m * r) / q) % q = (m * r) / q := Nat.mod_eq_of_lt hmr_div_lt
    have hmr_ge : m ≤ (m * r) / q := by
      rw [Nat.le_div_iff_mul_le hq.pos]
      nlinarith only [hqr]
    omega
  · right
    have hdiv1 : (p * q * r) / r = p * q := Nat.mul_div_cancel _ hr.pos
    have hdiv2 : (m * q * r) / r = m * q := Nat.mul_div_cancel _ hr.pos
    apply lucas_dvd_of_div_dvd hr
    rw [hdiv1, hdiv2]
    apply lucas_dvd_of_mod_lt hr
    have hmc_lt_c : m < c := by omega
    have hmc_pos : 0 < m * c := Nat.mul_pos hm1 (by omega)
    have hbc_lt : b * c < r := by nlinarith only [h2b2, hb_eq, hpq, hqr]
    have hmc_lt : m * c < r := by nlinarith only [hmc_lt_c, h2b2, hb_eq, hpq, hqr]
    have hbc_le_r : b + c ≤ r := by omega
    have hpq_exp : p * q = r * (r - b - c) + b * c := by
      have hr_decomp : r = (r - b - c) + b + c := by omega
      have h1 : p * q + r * (b + c) = r * r + b * c := by
        have hp1 : p + b = r := by omega
        have hq1 : q + c = r := by omega
        nlinarith only [hp1, hq1]
      have h2 : r * r = r * (r - b - c) + r * (b + c) := by
        calc r * r = r * ((r - b - c) + b + c) := by rw [← hr_decomp]
          _ = r * (r - b - c) + r * (b + c) := by ring
      omega
    have hmq_exp : m * q = r * (m - 1) + (r - m * c) := by
      set m' := m - 1
      have hm_decomp : m = m' + 1 := by omega
      have h1 : m * q + m * c = r * m' + r := by
        calc m * q + m * c = m * (q + c) := by ring
          _ = m * r := by rw [← hrc_eq]
          _ = r * m' + r := by rw [hm_decomp]; ring
      omega
    have hpq_mod : (p * q) % r = b * c := by
      rw [hpq_exp, Nat.mul_add_mod, Nat.mod_eq_of_lt hbc_lt]
    have hmq_mod : (m * q) % r = r - m * c := by
      rw [hmq_exp, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    rw [hpq_mod, hmq_mod]
    have hsum : b * c + m * c < r := by nlinarith only [hmc_lt_c, h2b2, hb_eq, hpq, hqr]
    omega

private lemma f_sq_gt_of_good_triple {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (hgap : q - p < r - q) (hsq : 2 * (r - p) ^ 2 < p) :
    ¬ (p * q * r).Prime ∧ 1 < p * q * r ∧ (Erdos700.f (p * q * r)) ^ 2 > p * q * r := by
  have hp2 : 2 ≤ p := hp.two_le
  have hq3 : 3 ≤ q := by omega
  have hr5 : 5 ≤ r := by omega
  have hn_ge30 : 30 ≤ p * q * r := by
    have h1 : 6 ≤ p * q := Nat.mul_le_mul hp2 hq3
    exact le_trans (by decide : 30 ≤ 6 * 5) (Nat.mul_le_mul h1 hr5)
  have hn_gt1 : 1 < p * q * r := by omega
  have hn_not_prime : ¬ (p * q * r).Prime := by
    intro hnp
    have hdvd : p ∣ p * q * r := ⟨q * r, by ring⟩
    rcases hnp.eq_one_or_self_of_dvd p hdvd with h1 | hself
    · omega
    · have hqr2 : 2 ≤ q * r := by nlinarith only [hq3, hr5]
      have : p * 2 ≤ p * (q * r) := Nat.mul_le_mul_left p hqr2
      have : p * q * r = p * (q * r) := by ring
      omega
  have hne : (Erdos700.fSet (p * q * r)).Nonempty :=
    ⟨_, Erdos700.f_mem (p * q * r) 2 (by decide) (by omega)⟩
  obtain ⟨k, hk1, hk2, hkeq⟩ := Nat.sInf_mem hne
  have hfn : Erdos700.f (p * q * r) = Nat.gcd (p * q * r) ((p * q * r).choose k) := by
    rw [Erdos700.f_eq, hkeq]
  have hgcd_pos : 0 < Nat.gcd (p * q * r) ((p * q * r).choose k) :=
    Nat.gcd_pos_of_pos_left _ (by omega)
  have htwo : (p ∣ (p * q * r).choose k ∧ q ∣ (p * q * r).choose k) ∨
      (p ∣ (p * q * r).choose k ∧ r ∣ (p * q * r).choose k) ∨
      (q ∣ (p * q * r).choose k ∧ r ∣ (p * q * r).choose k) := by
    by_cases hpc : p ∣ (p * q * r).choose k
    · by_cases hqc : q ∣ (p * q * r).choose k
      · exact Or.inl ⟨hpc, hqc⟩
      · by_cases hrc : r ∣ (p * q * r).choose k
        · exact Or.inr (Or.inl ⟨hpc, hrc⟩)
        · exfalso
          have hqk : q ∣ k := Erdos700.prime_dvd_of_not_dvd_choose q (p * q * r) k hq ⟨p * r, by ring⟩ hqc
          have hrk : r ∣ k := Erdos700.prime_dvd_of_not_dvd_choose r (p * q * r) k hr ⟨p * q, by ring⟩ hrc
          have hqrk : q * r ∣ k :=
            ((Nat.coprime_primes hq hr).mpr (by omega)).mul_dvd_of_dvd_of_dvd hqk hrk
          obtain ⟨m, hm⟩ := hqrk
          have hm1 : 1 ≤ m := by
            by_contra h
            have : m = 0 := by omega
            rw [this, mul_zero] at hm
            omega
          have hmp : m ≤ p / 2 := by
            have h1 : 2 * (q * r * m) ≤ p * q * r := by omega
            have h2 : q * r * (2 * m) ≤ q * r * p := by linarith only [h1]
            have h2m : 2 * m ≤ p := Nat.le_of_mul_le_mul_left h2 (Nat.mul_pos hq.pos hr.pos)
            omega
          have hkm : k = m * q * r := by rw [hm]; ring
          rw [hkm] at hqc hrc
          rcases case_qr hq hr hpq hqr hgap hsq hm1 hmp with h1 | h2
          · exact hqc h1
          · exact hrc h2
    · by_cases hqc : q ∣ (p * q * r).choose k
      · by_cases hrc : r ∣ (p * q * r).choose k
        · exact Or.inr (Or.inr ⟨hqc, hrc⟩)
        · exfalso
          have hpk : p ∣ k := Erdos700.prime_dvd_of_not_dvd_choose p (p * q * r) k hp ⟨q * r, by ring⟩ hpc
          have hrk : r ∣ k := Erdos700.prime_dvd_of_not_dvd_choose r (p * q * r) k hr ⟨p * q, by ring⟩ hrc
          have hprk : p * r ∣ k :=
            ((Nat.coprime_primes hp hr).mpr (by omega)).mul_dvd_of_dvd_of_dvd hpk hrk
          obtain ⟨m, hm⟩ := hprk
          have hm1 : 1 ≤ m := by
            by_contra h
            have : m = 0 := by omega
            rw [this, mul_zero] at hm
            omega
          have hmq : m ≤ q / 2 := by
            have h1 : 2 * (p * r * m) ≤ p * q * r := by omega
            have h2 : p * r * (2 * m) ≤ p * r * q := by linarith only [h1]
            have h2m : 2 * m ≤ q := Nat.le_of_mul_le_mul_left h2 (Nat.mul_pos hp.pos hr.pos)
            omega
          have hkm : k = m * p * r := by rw [hm]; ring
          rw [hkm] at hpc hrc
          rcases case_pr hp hr hpq hqr hsq hm1 hmq with h1 | h2
          · exact hpc h1
          · exact hrc h2
      · exfalso
        have hpk : p ∣ k := Erdos700.prime_dvd_of_not_dvd_choose p (p * q * r) k hp ⟨q * r, by ring⟩ hpc
        have hqk : q ∣ k := Erdos700.prime_dvd_of_not_dvd_choose q (p * q * r) k hq ⟨p * r, by ring⟩ hqc
        have hpqk : p * q ∣ k :=
          ((Nat.coprime_primes hp hq).mpr (by omega)).mul_dvd_of_dvd_of_dvd hpk hqk
        obtain ⟨m, hm⟩ := hpqk
        have hm1 : 1 ≤ m := by
          by_contra h
          have : m = 0 := by omega
          rw [this, mul_zero] at hm
          omega
        have hmr : m ≤ r / 2 := by
          have h1 : 2 * (p * q * m) ≤ p * q * r := by omega
          have h2 : p * q * (2 * m) ≤ p * q * r := by linarith only [h1]
          have h2m : 2 * m ≤ r := Nat.le_of_mul_le_mul_left h2 (Nat.mul_pos hp.pos hq.pos)
          omega
        have hkm : k = m * p * q := by rw [hm]; ring
        rw [hkm] at hpc hqc
        rcases case_pq hp hq hpq hqr hgap hsq hm1 hmr with h1 | h2
        · exact hpc h1
        · exact hqc h2
  have hge_pq : p * q ≤ Nat.gcd (p * q * r) ((p * q * r).choose k) := by
    rcases htwo with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hdvd : p * q ∣ Nat.gcd (p * q * r) ((p * q * r).choose k) :=
        Nat.dvd_gcd ⟨r, by ring⟩
          (((Nat.coprime_primes hp hq).mpr (by omega)).mul_dvd_of_dvd_of_dvd h1 h2)
      exact Nat.le_of_dvd hgcd_pos hdvd
    · have hdvd : p * r ∣ Nat.gcd (p * q * r) ((p * q * r).choose k) :=
        Nat.dvd_gcd ⟨q, by ring⟩
          (((Nat.coprime_primes hp hr).mpr (by omega)).mul_dvd_of_dvd_of_dvd h1 h2)
      exact le_trans (Nat.mul_le_mul_left p (le_of_lt hqr)) (Nat.le_of_dvd hgcd_pos hdvd)
    · have hdvd : q * r ∣ Nat.gcd (p * q * r) ((p * q * r).choose k) :=
        Nat.dvd_gcd ⟨p, by ring⟩
          (((Nat.coprime_primes hq hr).mpr (by omega)).mul_dvd_of_dvd_of_dvd h1 h2)
      exact le_trans (Nat.mul_le_mul (le_of_lt hpq) (le_of_lt hqr)) (Nat.le_of_dvd hgcd_pos hdvd)
  have hr_lt_pq : r < p * q := by
    have hb_ge1 : 1 ≤ r - p := by omega
    have hb_lt_p : r - p < p := by nlinarith only [hsq, hb_ge1]
    have h2p : r < 2 * p := by omega
    nlinarith only [h2p, hp2, hq3]
  refine ⟨hn_not_prime, hn_gt1, ?_⟩
  rw [hfn]
  have hsq1 : (p * q) ^ 2 ≤ (Nat.gcd (p * q * r) ((p * q * r).choose k)) ^ 2 :=
    Nat.pow_le_pow_left hge_pq 2
  have hsq2 : p * q * r < (p * q) ^ 2 := by
    have : (p * q) ^ 2 = (p * q) * (p * q) := sq (p * q)
    rw [this]
    exact Nat.mul_lt_mul_of_pos_left hr_lt_pq (Nat.mul_pos hp.pos hq.pos)
  omega

private lemma two_pow_le_central_choose (m : ℕ) : 2 ^ m ≤ (2 * m).choose m := by
  induction m with
  | zero => simp
  | succ k ih =>
    have h1 : (2 * (k + 1)).choose (k + 1) = (2 * k + 1).choose k + (2 * k + 1).choose (k + 1) := by
      simpa [Nat.mul_add] using Nat.choose_succ_succ (2 * k + 1) k
    have hsymm : (2 * k + 1).choose (k + 1) = (2 * k + 1).choose k := by
      have := Nat.choose_symm (show k ≤ 2 * k + 1 by omega)
      have hsub : 2 * k + 1 - k = k + 1 := by omega
      rw [hsub] at this
      exact this
    have hle : (2 * k).choose k ≤ (2 * k + 1).choose k := Nat.choose_le_choose k (by omega)
    rw [h1, hsymm, pow_succ]
    omega

private lemma two_pow_le_pow_primeCount (m : ℕ) (hm : 1 ≤ m) :
    2 ^ m ≤ (2 * m) ^ (Finset.filter Nat.Prime (Finset.Icc 1 (2 * m))).card := by
  set C := (2 * m).choose m
  have hCpos : 0 < C := Nat.choose_pos (by omega)
  have hC1 : 2 ^ m ≤ C := two_pow_le_central_choose m
  have hsub : C.primeFactors ⊆ Finset.filter Nat.Prime (Finset.Icc 1 (2 * m)) := by
    intro p hp
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hfac1 : 1 ≤ C.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    have hple : p ≤ 2 * m := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ C.factorization p := Nat.pow_le_pow_right hpr.pos hfac1
        _ ≤ 2 * m := Nat.pow_factorization_choose_le (by omega)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpr.pos, hple⟩, hpr⟩
  calc 2 ^ m ≤ C := hC1
    _ = ∏ p ∈ C.primeFactors, p ^ C.factorization p :=
        (Nat.prod_factorization_pow_eq_self hCpos.ne').symm
    _ ≤ ∏ _p ∈ C.primeFactors, (2 * m) :=
        Finset.prod_le_prod' fun p _ => Nat.pow_factorization_choose_le (by omega)
    _ = (2 * m) ^ C.primeFactors.card := by simp
    _ ≤ (2 * m) ^ (Finset.filter Nat.Prime (Finset.Icc 1 (2 * m))).card :=
        Nat.pow_le_pow_right (by omega) (Finset.card_le_card hsub)

private lemma primeCount_two_pow_ge (t : ℕ) (ht : 1 ≤ t) :
    2 ^ (4 * t - 1) ≤ (4 * t) * (Finset.filter Nat.Prime (Finset.Icc 1 (2 ^ (4 * t)))).card := by
  set m := 2 ^ (4 * t - 1)
  have h2m : 2 * m = 2 ^ (4 * t) := by
    rw [show 4 * t = (4 * t - 1) + 1 by omega, pow_succ']
  have hm1 : 1 ≤ m := Nat.one_le_pow _ _ (by decide)
  have h := two_pow_le_pow_primeCount m hm1
  rw [h2m, ← pow_mul] at h
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h

private lemma four_t_poly_lt_pow (t : ℕ) (ht : 12 ≤ t) :
    4 * t * (t + 3) < 2 ^ (t - 1) := by
  induction t, ht using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hstep : 4 * (k + 1) * (k + 1 + 3) ≤ 2 * (4 * k * (k + 3)) := by nlinarith only [hk]
    have hpow : 2 ^ (k + 1 - 1) = 2 * 2 ^ (k - 1) := by
      rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ']
    omega

private lemma gap_bound_of_no_good_triple :
    ∀ (n : ℕ) (B : Finset ℕ) (hcard : B.card = n) (h2 : 2 ≤ n),
      (∀ p ∈ B, ∀ q ∈ B, ∀ r ∈ B, p < q → q < r → r - q ≤ q - p) →
      2 ^ (n - 2) ≤
        B.max' (Finset.card_pos.mp (hcard ▸ by omega)) -
        B.min' (Finset.card_pos.mp (hcard ▸ by omega)) := by
  intro n
  induction n with
  | zero => intro _ _ h; omega
  | succ k ih =>
    intro B hcard h2 hno
    have hne : B.Nonempty := Finset.card_pos.mp (hcard ▸ by omega)
    set m := B.min' hne
    set M := B.max' hne
    have hm_mem : m ∈ B := Finset.min'_mem B hne
    have hM_mem : M ∈ B := Finset.max'_mem B hne
    have hm_lt_M : m < M := by
      by_contra h
      have hmM : M ≤ m := by omega
      have hsub : B ⊆ {m} := by
        intro x hx
        have h1 : m ≤ x := Finset.min'_le B x hx
        have h2' : x ≤ M := Finset.le_max' B x hx
        exact Finset.mem_singleton.mpr (by omega)
      have := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at this
      omega
    by_cases hk1 : k = 1
    · subst hk1
      have hpow0 : 2 ^ (1 + 1 - 2) = 1 := by decide
      rw [hpow0]
      omega
    · set B' := B.erase m
      have hcard' : B'.card = k := by
        rw [Finset.card_erase_of_mem hm_mem, hcard]
        omega
      have hk2 : 2 ≤ k := by omega
      have hne' : B'.Nonempty := Finset.card_pos.mp (hcard' ▸ by omega)
      have hno' : ∀ p ∈ B', ∀ q ∈ B', ∀ r ∈ B', p < q → q < r → r - q ≤ q - p :=
        fun p hp q hq r hr => hno p (Finset.mem_of_mem_erase hp) q (Finset.mem_of_mem_erase hq)
          r (Finset.mem_of_mem_erase hr)
      have hih := ih B' hcard' hk2 hno'
      have hM_mem' : M ∈ B' := Finset.mem_erase.mpr ⟨by omega, hM_mem⟩
      have hmax' : B'.max' hne' = M := by
        apply le_antisymm
        · exact Finset.le_max' B _ (Finset.mem_of_mem_erase (Finset.max'_mem B' hne'))
        · exact Finset.le_max' B' M hM_mem'
      set m' := B'.min' hne'
      have hm'_mem' : m' ∈ B' := Finset.min'_mem B' hne'
      have hm'_mem : m' ∈ B := Finset.mem_of_mem_erase hm'_mem'
      have hm_lt_m' : m < m' := by
        have h1 : m ≤ m' := Finset.min'_le B m' hm'_mem
        have h2' : m' ≠ m := (Finset.mem_erase.mp hm'_mem').1
        omega
      have hm'_lt_M : m' < M := by
        by_contra h
        have hsub : B' ⊆ {M} := by
          intro x hx
          have h1 : m' ≤ x := Finset.min'_le B' x hx
          have h2' : x ≤ M := hmax' ▸ Finset.le_max' B' x hx
          exact Finset.mem_singleton.mpr (by omega)
        have := Finset.card_le_card hsub
        simp only [Finset.card_singleton] at this
        omega
      have hgap := hno m hm_mem m' hm'_mem M hM_mem hm_lt_m' hm'_lt_M
      rw [hmax'] at hih
      have hpow : 2 ^ (k + 1 - 2) = 2 * 2 ^ (k - 2) := by
        rw [show k + 1 - 2 = (k - 2) + 1 by omega, pow_succ']
      omega

private lemma exists_good_triple_gt (t : ℕ) (ht : 12 ≤ t) :
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧
      2 ^ (3 * t) < p ∧ p < q ∧ q < r ∧ q - p < r - q ∧ 2 * (r - p) ^ 2 < p := by
  set S_all := Finset.filter Nat.Prime (Finset.Icc 1 (2 ^ (4 * t)))
  set S_hi := S_all.filter (fun p => 2 ^ (3 * t) < p)
  have hS_lo : (S_all \ S_hi).card ≤ 2 ^ (3 * t) := by
    have hsub : S_all \ S_hi ⊆ Finset.Icc 1 (2 ^ (3 * t)) := by
      intro p hp
      simp only [Finset.mem_sdiff, S_all, S_hi, Finset.mem_filter, Finset.mem_Icc] at hp
      have hnot : ¬ (2 ^ (3 * t) < p) := fun h => hp.2 ⟨hp.1, h⟩
      exact Finset.mem_Icc.mpr ⟨hp.1.1.1, by omega⟩
    calc (S_all \ S_hi).card ≤ (Finset.Icc 1 (2 ^ (3 * t))).card := Finset.card_le_card hsub
      _ = 2 ^ (3 * t) := by simp
  have hS_split : S_all.card ≤ S_hi.card + 2 ^ (3 * t) := by
    have hsub : S_hi ⊆ S_all := Finset.filter_subset _ _
    have := Finset.card_sdiff_add_card_eq_card hsub
    omega
  have hmaps : ∀ p ∈ S_hi, p / 2 ^ t ∈ Finset.range (2 ^ (3 * t)) := by
    intro p hp
    simp only [S_hi, S_all, Finset.mem_filter, Finset.mem_Icc] at hp
    have hne : p ≠ 2 ^ (4 * t) := by
      intro heq
      have h2dvd : 2 ∣ 2 ^ (4 * t) := dvd_pow_self 2 (by omega)
      rw [← heq] at h2dvd
      have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.1.2).mp h2dvd).symm
      have hpow_ge : 2 ^ 36 ≤ 2 ^ (3 * t) := Nat.pow_le_pow_right (by decide) (by omega)
      have h36 : 2 < 2 ^ 36 := by decide
      omega
    have hplt : p < 2 ^ (4 * t) := by omega
    rw [Finset.mem_range, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos t), ← pow_add]
    simpa [show 3 * t + t = 4 * t by omega] using hplt
  have hex_block : ∃ j ∈ Finset.range (2 ^ (3 * t)),
      t + 3 ≤ (S_hi.filter (fun p => p / 2 ^ t = j)).card := by
    by_contra hall
    push Not at hall
    have hfib : S_hi.card = ∑ j ∈ Finset.range (2 ^ (3 * t)),
        (S_hi.filter (fun p => p / 2 ^ t = j)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    have hle : S_hi.card ≤ (t + 2) * 2 ^ (3 * t) := by
      rw [hfib]
      calc ∑ j ∈ Finset.range (2 ^ (3 * t)), (S_hi.filter (fun p => p / 2 ^ t = j)).card
          ≤ ∑ _j ∈ Finset.range (2 ^ (3 * t)), (t + 2) :=
            Finset.sum_le_sum fun j hj => Nat.lt_succ_iff.mp (hall j hj)
        _ = (t + 2) * 2 ^ (3 * t) := by
            simp [mul_comm]
    have hS_le : S_all.card ≤ (t + 3) * 2 ^ (3 * t) := by
      have : (t + 2) * 2 ^ (3 * t) + 2 ^ (3 * t) = (t + 3) * 2 ^ (3 * t) := by ring
      omega
    have hcheb := primeCount_two_pow_ge t (by omega)
    have hcomb : 2 ^ (4 * t - 1) ≤ (4 * t * (t + 3)) * 2 ^ (3 * t) := by
      calc 2 ^ (4 * t - 1) ≤ 4 * t * S_all.card := hcheb
        _ ≤ 4 * t * ((t + 3) * 2 ^ (3 * t)) := Nat.mul_le_mul_left _ hS_le
        _ = (4 * t * (t + 3)) * 2 ^ (3 * t) := by ring
    have hpow_split : 2 ^ (4 * t - 1) = 2 ^ (t - 1) * 2 ^ (3 * t) := by
      rw [← pow_add, show (t - 1) + 3 * t = 4 * t - 1 by omega]
    rw [hpow_split] at hcomb
    have hlt := four_t_poly_lt_pow t ht
    have hle2 : 2 ^ (t - 1) ≤ 4 * t * (t + 3) :=
      Nat.le_of_mul_le_mul_right hcomb (Nat.two_pow_pos _)
    omega
  obtain ⟨j, _, hjcard⟩ := hex_block
  set B := S_hi.filter (fun p => p / 2 ^ t = j)
  have hex_tri : ∃ p ∈ B, ∃ q ∈ B, ∃ r ∈ B, p < q ∧ q < r ∧ q - p < r - q := by
    by_contra hno
    push Not at hno
    have hgb := gap_bound_of_no_good_triple B.card B rfl (by omega) hno
    have hneB : B.Nonempty := Finset.card_pos.mp (by omega)
    have hmin_div : B.min' hneB / 2 ^ t = j := (Finset.mem_filter.mp (Finset.min'_mem B hneB)).2
    have hmax_div : B.max' hneB / 2 ^ t = j := (Finset.mem_filter.mp (Finset.max'_mem B hneB)).2
    have hdiff : B.max' hneB - B.min' hneB < 2 ^ t := by
      have h1 := Nat.div_add_mod (B.min' hneB) (2 ^ t)
      have h2 := Nat.div_add_mod (B.max' hneB) (2 ^ t)
      have h3 := Nat.mod_lt (B.max' hneB) (Nat.two_pow_pos t)
      rw [hmin_div] at h1
      rw [hmax_div] at h2
      omega
    have hpow_ge : 2 ^ t ≤ 2 ^ (B.card - 2) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  obtain ⟨p, hpB, q, hqB, r, hrB, hpq, hqr, hgap⟩ := hex_tri
  have hp_hi := (Finset.mem_filter.mp hpB).1
  have hq_hi := (Finset.mem_filter.mp hqB).1
  have hr_hi := (Finset.mem_filter.mp hrB).1
  have hp_pr : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp_hi).1).2
  have hq_pr : q.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hq_hi).1).2
  have hr_pr : r.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hr_hi).1).2
  have hp_gt : 2 ^ (3 * t) < p := (Finset.mem_filter.mp hp_hi).2
  have hdiff : r - p < 2 ^ t := by
    have h1 := Nat.div_add_mod p (2 ^ t)
    have h2 := Nat.div_add_mod r (2 ^ t)
    have h3 := Nat.mod_lt r (Nat.two_pow_pos t)
    rw [(Finset.mem_filter.mp hpB).2] at h1
    rw [(Finset.mem_filter.mp hrB).2] at h2
    omega
  have hsq : 2 * (r - p) ^ 2 < p := by
    have h1 : (r - p) ^ 2 < (2 ^ t) ^ 2 := Nat.pow_lt_pow_left hdiff (by decide)
    have h2 : 2 * (2 ^ t) ^ 2 = 2 ^ (2 * t + 1) := by
      rw [← pow_mul, mul_comm t 2, pow_succ']
    have h3 : 2 ^ (2 * t + 1) ≤ 2 ^ (3 * t) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  exact ⟨p, q, r, hp_pr, hq_pr, hr_pr, hp_gt, hpq, hqr, hgap, hsq⟩

end Erdos700Proof

theorem OMA.solution : type_of% @Erdos700.erdos_700.parts.ii := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  set t := max 12 N
  obtain ⟨p, q, r, hp, hq, hr, hp_gt, hpq, hqr, hgap, hsq⟩ :=
    Erdos700Proof.exists_good_triple_gt t (le_max_left 12 N)
  refine ⟨p * q * r, Erdos700Proof.f_sq_gt_of_good_triple hp hq hr hpq hqr hgap hsq, ?_⟩
  have ht : N ≤ t := le_max_right 12 N
  have hpow : t < 2 ^ (3 * t) := by
    have := Nat.lt_two_pow_self (n := 3 * t)
    omega
  have hp_le : p ≤ p * q * r := by
    have h1 : 1 ≤ q * r := Nat.mul_pos hq.pos hr.pos
    have h2 : p * 1 ≤ p * (q * r) := Nat.mul_le_mul_left p h1
    have h3 : p * q * r = p * (q * r) := by ring
    omega
  omega
