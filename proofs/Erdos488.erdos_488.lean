import FormalConjectures.ErdosProblems.«488»

/-!
Disproof of Erdős Problem 488: using 251-smooth numbers in dyadic bands `(2^(j-8), 2^j]`,
averaging the conjectured bound over `j ∈ [8, J)` forces exponential growth `|S_J| ≥ (5/4)^t`,
contradicting the polynomial bound `|S_J| ≤ (J + 1)^54`.
-/

namespace OMA_Erdos488

open Finset

private def PList : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
   101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
   197, 199, 211, 223, 227, 229, 233, 239, 241, 251]

private def P : Finset ℕ := PList.toFinset

private def W : ℕ := ∏ p ∈ P, p

private def Smooth (s : ℕ) : Prop :=
  0 < s ∧ ∀ p : ℕ, p.Prime → p ∣ s → p < 256

private def isPrimeSmall (n : ℕ) : Bool :=
  2 ≤ n && (List.range' 2 14).all (fun d => d == n || n % d != 0)

private lemma prime_of_isPrimeSmall {n : ℕ} (h256 : n < 256) (h : isPrimeSmall n = true) :
    n.Prime := by
  simp only [isPrimeSmall, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases h with ⟨hge2, hdiv⟩
  by_contra hnp
  have hn1 : n ≠ 1 := by omega
  let d := n.minFac
  have hd_prime : d.Prime := Nat.minFac_prime hn1
  have hd_dvd : d ∣ n := Nat.minFac_dvd n
  have hd_sq : d * d ≤ n := by
    have := Nat.minFac_sq_le_self (by omega : 0 < n) hnp
    simpa [sq] using this
  have hd_le15 : d ≤ 15 := by nlinarith
  have hd_ge2 : 2 ≤ d := hd_prime.two_le
  have hd_mem : d ∈ List.range' 2 14 := by
    rw [List.mem_range'_1]; omega
  have hd_lt : d < n := by
    have : d ≠ n := fun heq => hnp (heq ▸ hd_prime)
    have := Nat.le_of_dvd (by omega) hd_dvd
    omega
  rcases hdiv d hd_mem with heq | hmod
  · omega
  · exact hmod (Nat.mod_eq_zero_of_dvd hd_dvd)

private lemma PList_nodup : PList.Nodup := by decide +kernel

private lemma PList_len : PList.length = 54 := by decide +kernel

private lemma PList_all_prime : PList.all (fun p => p < 256 && isPrimeSmall p) = true := by
  decide +kernel

private lemma PList_complete :
    (List.range' 2 254).all (fun n =>
      PList.elem n || (List.range' 2 14).any (fun d => d < n && n % d == 0)) = true := by
  decide +kernel

private lemma mem_P_iff {p : ℕ} : p ∈ P ↔ p.Prime ∧ p < 256 := by
  rw [P, List.mem_toFinset]
  constructor
  · intro hp
    have h := List.all_eq_true.mp PList_all_prime p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨prime_of_isPrimeSmall h.1 h.2, h.1⟩
  · rintro ⟨hp, h256⟩
    have hge2 : 2 ≤ p := hp.two_le
    have hmem : p ∈ List.range' 2 254 := by rw [List.mem_range'_1]; omega
    have h := List.all_eq_true.mp PList_complete p hmem
    simp only [Bool.or_eq_true, List.elem_eq_mem, decide_eq_true_eq, List.any_eq_true,
      Bool.and_eq_true, beq_iff_eq] at h
    rcases h with hmemP | ⟨d, hd_mem, hd_lt, hd_mod⟩
    · exact hmemP
    · rw [List.mem_range'_1] at hd_mem
      have hd_dvd : d ∣ p := Nat.dvd_of_mod_eq_zero hd_mod
      rcases hp.eq_one_or_self_of_dvd d hd_dvd with rfl | rfl <;> omega

private lemma P_card : P.card = 54 := by
  rw [P, List.toFinset_card_of_nodup PList_nodup, PList_len]

private lemma totient_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Nat.totient (∏ p ∈ S, p) = ∏ p ∈ S, (p - 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p s hp_not ih =>
    have hp : p.Prime := hS p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hp_not, Finset.prod_insert hp_not]
    have hcop : p.Coprime (∏ q ∈ s, q) := by
      rw [hp.coprime_iff_not_dvd]
      intro hdvd
      rw [hp.prime.dvd_finsetProd_iff] at hdvd
      obtain ⟨q, hqs, hpq⟩ := hdvd
      have hq : q.Prime := hs q hqs
      have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
      exact hp_not (heq ▸ hqs)
    rw [Nat.totient_mul hcop, Nat.totient_prime hp, ih hs]

private lemma W_totient_eq : Nat.totient W = ∏ p ∈ P, (p - 1) :=
  totient_prod_primes P (fun _ hp => (mem_P_iff.mp hp).1)

private lemma W_totient_bound : W ≤ 10 * Nat.totient W := by
  rw [W_totient_eq, W, P, List.prod_toFinset (f := fun p => p) PList_nodup,
    List.prod_toFinset (f := fun p => p - 1) PList_nodup]
  decide +kernel

private lemma dvd_W_of_mem_P {p : ℕ} (hp : p ∈ P) : p ∣ W :=
  Finset.dvd_prod_of_mem _ hp

private lemma W_gt_two : 2 < W := by
  have hpos : 0 < W := Finset.prod_pos fun _ hp => (mem_P_iff.mp hp).1.pos
  have h3dvd : 3 ∣ W := dvd_W_of_mem_P (mem_P_iff.mpr ⟨Nat.prime_three, by omega⟩)
  have h3 := Nat.le_of_dvd hpos h3dvd
  omega

private lemma smooth_mul {a b : ℕ} (ha : Smooth a) (hb : Smooth b) : Smooth (a * b) := by
  refine ⟨Nat.mul_pos ha.1 hb.1, fun p hp hdvd => ?_⟩
  rcases hp.dvd_mul.mp hdvd with h | h
  · exact ha.2 p hp h
  · exact hb.2 p hp h

private lemma smooth_of_dvd {a b : ℕ} (hb : Smooth b) (ha0 : 0 < a) (hab : a ∣ b) : Smooth a :=
  ⟨ha0, fun p hp hpa => hb.2 p hp (dvd_trans hpa hab)⟩

private lemma smooth_of_lt_256 {q : ℕ} (hq0 : 0 < q) (hq : q < 256) : Smooth q :=
  ⟨hq0, fun _ _ hpq => lt_of_le_of_lt (Nat.le_of_dvd hq0 hpq) hq⟩

private lemma smooth_pow_two (k : ℕ) : Smooth (2 ^ k) := by
  refine ⟨pow_pos (by norm_num) k, fun p hp hdvd => ?_⟩
  have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hdvd
  have := Nat.le_of_dvd (by norm_num) hp2
  omega

private lemma smooth_coprime_of_coprime_M {M s r : ℕ} (hM_dvd : ∀ p ∈ P, p ∣ M)
    (hs : Smooth s) (hr : r.Coprime M) : s.Coprime r := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  let p := (Nat.gcd s r).minFac
  have hp : p.Prime := Nat.minFac_prime hne
  have hps : p ∣ s := dvd_trans (Nat.minFac_dvd _) (Nat.gcd_dvd_left s r)
  have hpr : p ∣ r := dvd_trans (Nat.minFac_dvd _) (Nat.gcd_dvd_right s r)
  have hpP : p ∈ P := mem_P_iff.mpr ⟨hp, hs.2 p hp hps⟩
  have hpM : p ∣ M := hM_dvd p hpP
  have hp_gcd : p ∣ Nat.gcd r M := Nat.dvd_gcd hpr hpM
  rw [hr.gcd_eq_one] at hp_gcd
  have := Nat.le_of_dvd one_pos hp_gcd
  have := hp.two_le
  omega

private lemma smooth_factorization_le {s M : ℕ} (hs : Smooth s) (hsM : s ≤ 2 ^ M) (p : ℕ) :
    s.factorization p ≤ M := by
  by_cases hp : p.Prime
  · have h1 : p ^ (s.factorization p) ≤ s := Nat.le_of_dvd hs.1 (Nat.ordProj_dvd s p)
    have h2 : 2 ^ (s.factorization p) ≤ p ^ (s.factorization p) :=
      Nat.pow_le_pow_left hp.two_le _
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (le_trans (le_trans h2 h1) hsM)
  · simp [Nat.factorization_eq_zero_of_not_prime s hp]

private lemma smooth_dvd_M_pow {M s J : ℕ} (hM_pos : 0 < M) (hM_dvd : ∀ p ∈ P, p ∣ M)
    (hs : Smooth s) (hsJ : s ≤ 2 ^ J) : s ∣ M ^ J := by
  rw [← Nat.factorization_le_iff_dvd hs.1.ne' (pow_ne_zero J hM_pos.ne')]
  intro p
  by_cases hpdvd : p.Prime ∧ p ∣ s
  · rcases hpdvd with ⟨hp, hps⟩
    have hpP : p ∈ P := mem_P_iff.mpr ⟨hp, hs.2 p hp hps⟩
    have hpM : p ∣ M := hM_dvd p hpP
    have hM1 : 1 ≤ M.factorization p := Nat.Prime.factorization_pos_of_dvd hp hM_pos.ne' hpM
    have hsle : s.factorization p ≤ J := smooth_factorization_le hs hsJ p
    rw [Nat.factorization_pow]
    simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    nlinarith
  · have hz : s.factorization p = 0 := by
      by_cases hp : p.Prime
      · exact Nat.factorization_eq_zero_of_not_dvd (fun h => hpdvd ⟨hp, h⟩)
      · exact Nat.factorization_eq_zero_of_not_prime s hp
    simp [hz]

private lemma smooth_descent {j s : ℕ} (hj : 8 ≤ j) (hs : Smooth s) (hlo : 2 ^ (j - 8) < s) :
    ∃ a : ℕ, Smooth a ∧ 2 ^ (j - 8) < a ∧ a ≤ 2 ^ j ∧ a ∣ s := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    by_cases hle : s ≤ 2 ^ j
    · exact ⟨s, hs, hlo, hle, dvd_rfl⟩
    · have hsgt : 2 ^ j < s := by omega
      have h256 : 256 ≤ 2 ^ j := by
        have : 2 ^ 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
        simpa using this
      have hs1 : s ≠ 1 := by omega
      let p := s.minFac
      have hp : p.Prime := Nat.minFac_prime hs1
      have hps : p ∣ s := Nat.minFac_dvd s
      have hp256 : p < 256 := hs.2 p hp hps
      let s' := s / p
      have hs'_mul : p * s' = s := Nat.mul_div_cancel' hps
      have hs'_pos : 0 < s' := by
        by_contra h0
        have hzero : s' = 0 := Nat.eq_zero_of_not_pos h0
        rw [hzero, mul_zero] at hs'_mul
        omega
      have hs'_lt : s' < s := by
        have := hp.two_le
        nlinarith
      have hs'_smooth : Smooth s' := smooth_of_dvd hs hs'_pos ⟨p, by linarith⟩
      have h2pow : 2 ^ j = 256 * 2 ^ (j - 8) := by
        have : j = 8 + (j - 8) := by omega
        conv_lhs => rw [this, pow_add]
        norm_num
      have hs'_lo : 2 ^ (j - 8) < s' := by nlinarith
      obtain ⟨a, ha_sm, ha_lo, ha_hi, ha_dvd⟩ := ih s' hs'_lt hs'_smooth hs'_lo
      exact ⟨a, ha_sm, ha_lo, ha_hi, dvd_trans ha_dvd ⟨p, by linarith⟩⟩

private lemma card_Icc_coprime_mul {M : ℕ} (hM : 2 < M) (t : ℕ) :
    ((Finset.Icc 1 (M * t)).filter (fun r => r.Coprime M)).card = t * Nat.totient M := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hsplit : Finset.Icc 1 (M * (t + 1)) =
        Finset.Icc 1 (M * t) ∪ Finset.Ioc (M * t) (M * t + M) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      have : M * (t + 1) = M * t + M := by ring
      omega
    have hdisj : Disjoint (Finset.Icc 1 (M * t)) (Finset.Ioc (M * t) (M * t + M)) := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2
      omega
    rw [hsplit, Finset.filter_union,
      Finset.card_union_of_disjoint (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
      ih]
    have hblock : ((Finset.Ioc (M * t) (M * t + M)).filter (fun r => r.Coprime M)).card =
        Nat.totient M := by
      rw [Nat.totient_eq_card_coprime]
      apply Finset.card_bij (fun r _ => r - M * t)
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hr ⊢
        rcases hr with ⟨⟨hlo, hhi⟩, hcop⟩
        have hreq : r = M * t + (r - M * t) := by omega
        have hcop' : (r - M * t).Coprime M := by
          rw [hreq, Nat.coprime_comm] at hcop
          simpa [Nat.coprime_comm, Nat.coprime_mul_left_add_right] using hcop
        have hlt : r - M * t < M := by
          by_contra hge
          have heq : r - M * t = M := by omega
          rw [heq] at hcop'
          have h1 := hcop'.gcd_eq_one
          rw [Nat.gcd_self] at h1
          omega
        exact ⟨hlt, hcop'.symm⟩
      · intro r1 hr1 r2 hr2 h
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hr1 hr2
        omega
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_range] at hx
        rcases hx with ⟨hlt, hcop⟩
        have hxpos : 0 < x := by
          by_contra h0
          have hx0 : x = 0 := by omega
          rw [hx0, Nat.coprime_zero_right] at hcop
          omega
        refine ⟨M * t + x, ?_, by omega⟩
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        rw [Nat.coprime_comm]
        simpa [Nat.coprime_mul_left_add_right] using hcop
    rw [hblock]
    ring

private noncomputable def S (K : ℕ) : Finset ℕ :=
  @Finset.filter ℕ Smooth (Classical.decPred Smooth) (Finset.Icc 1 (2 ^ K))

private lemma mem_S {K s : ℕ} : s ∈ S K ↔ 1 ≤ s ∧ s ≤ 2 ^ K ∧ Smooth s := by
  simp [S, and_assoc]

private lemma card_S_le (K : ℕ) : (S K).card ≤ (K + 1) ^ 54 := by
  let f : ℕ → (P → Fin (K + 1)) := fun s p =>
    ⟨min (s.factorization p.1) K, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  have hinj : Set.InjOn f (S K) := by
    intro s1 hs1 s2 hs2 hfeq
    rw [Finset.mem_coe, mem_S] at hs1 hs2
    have hfac : s1.factorization = s2.factorization := by
      ext p
      by_cases hpP : p ∈ P
      · have hval := congr_arg Fin.val (congr_fun hfeq ⟨p, hpP⟩)
        dsimp only [f] at hval
        rw [Nat.min_eq_left (smooth_factorization_le hs1.2.2 hs1.2.1 p),
          Nat.min_eq_left (smooth_factorization_le hs2.2.2 hs2.2.1 p)] at hval
        exact hval
      · have h1 : s1.factorization p = 0 := by
          by_cases hp : p.Prime
          · apply Nat.factorization_eq_zero_of_not_dvd
            intro hdvd
            exact hpP (mem_P_iff.mpr ⟨hp, hs1.2.2.2 p hp hdvd⟩)
          · exact Nat.factorization_eq_zero_of_not_prime s1 hp
        have h2 : s2.factorization p = 0 := by
          by_cases hp : p.Prime
          · apply Nat.factorization_eq_zero_of_not_dvd
            intro hdvd
            exact hpP (mem_P_iff.mpr ⟨hp, hs2.2.2.2 p hp hdvd⟩)
          · exact Nat.factorization_eq_zero_of_not_prime s2 hp
        rw [h1, h2]
    exact Nat.factorization_inj hs1.2.2.1.ne' hs2.2.2.1.ne' hfac
  have hle : (S K).card ≤ (Finset.univ : Finset (P → Fin (K + 1))).card :=
    Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj
  simpa [Fintype.card_pi, Fintype.card_fin, P_card] using hle

private lemma card_S_ge_pow_two (K : ℕ) : K + 1 ≤ (S K).card := by
  have hsub : (Finset.range (K + 1)).image (fun k => 2 ^ k) ⊆ S K := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    simp only [Finset.mem_range] at hk
    rw [mem_S]
    exact ⟨Nat.one_le_two_pow, Nat.pow_le_pow_right (by norm_num) (by omega), smooth_pow_two k⟩
  have hcard : ((Finset.range (K + 1)).image (fun k => 2 ^ k)).card = K + 1 := by
    rw [Finset.card_image_of_injective _ (Nat.pow_right_injective (by norm_num)),
      Finset.card_range]
  rw [← hcard]
  exact Finset.card_le_card hsub

private lemma card_S_16_le : (S 16).card ≤ 2 ^ 16 := by
  calc (S 16).card ≤ (Finset.Icc 1 (2 ^ 16)).card :=
        Finset.card_le_card (fun s hs => Finset.mem_Icc.mpr ⟨(mem_S.mp hs).1, (mem_S.mp hs).2.1⟩)
    _ = 2 ^ 16 := by simp

private lemma growth_step
    {M : ℕ} (hM2 : 2 < M) (hM_dvd : ∀ p ∈ P, p ∣ M) (hM_tot : M ≤ 10 * Nat.totient M)
    (h488 : ∀ (A : Finset ℕ), A.Nonempty → 0 ∉ A → 1 ∉ A →
      ∀ (n : ℕ) (m : ℕ), m > n → A.max ≤ n →
        ((Finset.Icc 1 m).filter (· ∈ {x ≥ 1 | ∃ a ∈ A, a ∣ x})).card / (m : ℚ) <
          2 * ((Finset.Icc 1 n).filter (· ∈ {x ≥ 1 | ∃ a ∈ A, a ∣ x})).card / n)
    {J : ℕ} (hJ : 24 ≤ J) :
    51 * (S (J - 8)).card ≤ 32 * (S J).card + 51 * (S 16).card := by
  have hM_pos : 0 < M := by omega
  let Q : ℕ := M ^ (J + 1)
  have hQ_pos : 0 < Q := pow_pos hM_pos _
  have hQ_gt : ∀ j < J, 2 ^ j < Q := by
    intro j hj
    have h1 : 2 ^ j < 2 ^ (J + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (J + 1) ≤ M ^ (J + 1) := Nat.pow_le_pow_left hM2.le _
    exact lt_of_lt_of_le h1 h2
  have hband : ∀ j ∈ Finset.Ico 8 J,
      ((Nat.totient M : ℚ) / (M : ℚ)) *
        ∑ s ∈ (S J).filter (fun s => 2 ^ (j - 8) < s), (2 ^ j : ℚ) / (s : ℚ) <
      2 * (((S J).filter (fun s => 2 ^ (j - 8) < s ∧ s ≤ 2 ^ j)).card : ℚ) := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    let A : Finset ℕ := (S J).filter (fun s => 2 ^ (j - 8) < s ∧ s ≤ 2 ^ j)
    have hA_ne : A.Nonempty := by
      refine ⟨2 ^ j, ?_⟩
      simp only [A, Finset.mem_filter, mem_S]
      exact ⟨⟨Nat.one_le_two_pow, Nat.pow_le_pow_right (by norm_num) (by omega),
        smooth_pow_two j⟩,
        Nat.pow_lt_pow_right (by norm_num) (by omega), le_rfl⟩
    have h0A : 0 ∉ A := by
      intro h0
      simp only [A, Finset.mem_filter, mem_S] at h0
      omega
    have h1A : 1 ∉ A := by
      intro h1
      simp only [A, Finset.mem_filter, mem_S] at h1
      have : 1 ≤ 2 ^ (j - 8) := Nat.one_le_two_pow
      omega
    have hAmax : A.max ≤ (2 ^ j : ℕ) := by
      rw [Finset.max_le_iff]
      intro a ha
      simp only [A, Finset.mem_filter] at ha
      exact WithBot.coe_le_coe.mpr ha.2.2
    let B : Set ℕ := {x ≥ 1 | ∃ a ∈ A, a ∣ x}
    have hspec := h488 A hA_ne h0A h1A (2 ^ j) Q (hQ_gt j hj.2) hAmax
    have hBn_eq : (Finset.Icc 1 (2 ^ j)).filter (· ∈ B) = A := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_Icc, B, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨hu1, hule⟩, -, a, haA, hau⟩
        simp only [A, Finset.mem_filter, mem_S] at haA ⊢
        rcases hau with ⟨q, rfl⟩
        have hq_pos : 0 < q := by
          by_contra hq0
          have hzero : q = 0 := Nat.eq_zero_of_not_pos hq0
          rw [hzero, mul_zero] at hu1
          omega
        have h2pow : 2 ^ j = 256 * 2 ^ (j - 8) := by
          have : j = 8 + (j - 8) := by omega
          conv_lhs => rw [this, pow_add]
          norm_num
        have hq_lt : q < 256 := by nlinarith [haA.2.1]
        refine ⟨⟨hu1, le_trans hule (Nat.pow_le_pow_right (by norm_num) (by omega)),
          smooth_mul haA.1.2.2 (smooth_of_lt_256 hq_pos hq_lt)⟩, ?_, hule⟩
        nlinarith [haA.2.1]
      · intro huA
        have huA' := huA
        simp only [A, Finset.mem_filter, mem_S] at huA'
        exact ⟨⟨huA'.1.1, huA'.2.2⟩, huA'.1.1, u, huA, dvd_rfl⟩
    let T : Finset ℕ := (S J).filter (fun s => 2 ^ (j - 8) < s)
    let C : ℕ → Finset ℕ := fun s =>
      ((Finset.Icc 1 (Q / s)).filter (fun r => r.Coprime M)).image (fun r => s * r)
    have hdisj : Set.PairwiseDisjoint (T : Set ℕ) C := by
      intro s1 hs1 s2 hs2 hne
      simp only [Finset.mem_coe, T, Finset.mem_filter, mem_S] at hs1 hs2
      change Disjoint (C s1) (C s2)
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      rcases Finset.mem_image.mp hu1 with ⟨r1, hr1, rfl⟩
      rcases Finset.mem_image.mp hu2 with ⟨r2, hr2, heq⟩
      simp only [Finset.mem_filter] at hr1 hr2
      have hcop1 : s1.Coprime r2 := smooth_coprime_of_coprime_M hM_dvd hs1.1.2.2 hr2.2
      have hcop2 : s2.Coprime r1 := smooth_coprime_of_coprime_M hM_dvd hs2.1.2.2 hr1.2
      have hd1 : s1 ∣ s2 := hcop1.dvd_of_dvd_mul_right ⟨r1, heq⟩
      have hd2 : s2 ∣ s1 := hcop2.dvd_of_dvd_mul_right ⟨r2, heq.symm⟩
      exact hne (Nat.dvd_antisymm hd1 hd2)
    have hsub : T.biUnion C ⊆ (Finset.Icc 1 Q).filter (· ∈ B) := by
      intro u hu
      rcases Finset.mem_biUnion.mp hu with ⟨s, hsT, huC⟩
      simp only [T, Finset.mem_filter, mem_S] at hsT
      rcases Finset.mem_image.mp huC with ⟨r, hr, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_Icc] at hr
      have hsr_pos : 1 ≤ s * r := Nat.mul_pos hsT.1.2.2.1 hr.1.1
      have hsr_le : s * r ≤ Q := le_trans (Nat.mul_le_mul_left s hr.1.2) (Nat.mul_div_le Q s)
      obtain ⟨a, ha_sm, ha_lo, ha_hi, ha_dvd⟩ := smooth_descent hj.1 hsT.1.2.2 hsT.2
      have haA : a ∈ A := by
        simp only [A, Finset.mem_filter, mem_S]
        exact ⟨⟨ha_sm.1, le_trans ha_hi (Nat.pow_le_pow_right (by norm_num) (by omega)), ha_sm⟩,
          ha_lo, ha_hi⟩
      simp only [Finset.mem_filter, Finset.mem_Icc, B, Set.mem_ofPred_eq]
      exact ⟨⟨hsr_pos, hsr_le⟩, hsr_pos, a, haA, dvd_trans ha_dvd (dvd_mul_right s r)⟩
    have hcard_C : ∀ s ∈ T, ((C s).card : ℚ) = (Q : ℚ) * ((Nat.totient M : ℚ) / (M : ℚ)) / (s : ℚ) := by
      intro s hsT
      simp only [T, Finset.mem_filter, mem_S] at hsT
      have hs_dvd : s ∣ M ^ J := smooth_dvd_M_pow hM_pos hM_dvd hsT.1.2.2 hsT.1.2.1
      obtain ⟨t, ht⟩ := hs_dvd
      have hQ_eq : Q = s * (M * t) := by
        dsimp only [Q]
        rw [pow_succ, ht]
        ring
      have hdiv_eq : Q / s = M * t := by
        rw [hQ_eq, Nat.mul_div_right _ hsT.1.2.2.1]
      have hcard_nat : (C s).card = t * Nat.totient M := by
        dsimp only [C]
        rw [Finset.card_image_of_injective _ (mul_right_injective₀ hsT.1.2.2.1.ne'), hdiv_eq,
          card_Icc_coprime_mul hM2]
      rw [hcard_nat]
      have hsQ : (s : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hsT.1.2.2.1.ne'
      have hMQ : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hM_pos.ne'
      have hQ_cast : (Q : ℚ) = (s : ℚ) * ((M : ℚ) * (t : ℚ)) := by exact_mod_cast hQ_eq
      push_cast
      rw [hQ_cast]
      field_simp [hsQ, hMQ]
    have hcard_lb : ∑ s ∈ T, ((C s).card : ℚ) ≤ (((Finset.Icc 1 Q).filter (· ∈ B)).card : ℚ) := by
      have hnat : ∑ s ∈ T, (C s).card ≤ ((Finset.Icc 1 Q).filter (· ∈ B)).card := by
        rw [← Finset.card_biUnion hdisj]
        exact Finset.card_le_card hsub
      exact_mod_cast hnat
    have hsum_eq : ∑ s ∈ T, ((C s).card : ℚ) =
        (Q : ℚ) * ((Nat.totient M : ℚ) / (M : ℚ)) * ∑ s ∈ T, (1 : ℚ) / (s : ℚ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [hcard_C s hs]
      ring
    rw [hsum_eq] at hcard_lb
    have hQ_posQ : (0 : ℚ) < (Q : ℚ) := Nat.cast_pos.mpr hQ_pos
    have h2j_posQ : (0 : ℚ) < (2 ^ j : ℚ) := by positivity
    have hdiv_lb : ((Nat.totient M : ℚ) / (M : ℚ)) * ∑ s ∈ T, (1 : ℚ) / (s : ℚ) ≤
        (((Finset.Icc 1 Q).filter (· ∈ B)).card : ℚ) / (Q : ℚ) := by
      rw [le_div_iff₀ hQ_posQ]
      linarith
    have hlt : ((Nat.totient M : ℚ) / (M : ℚ)) * ∑ s ∈ T, (1 : ℚ) / (s : ℚ) <
        2 * (A.card : ℚ) / (2 ^ j : ℚ) := by
      rw [hBn_eq] at hspec
      have hspec' : (((Finset.Icc 1 Q).filter (· ∈ B)).card : ℚ) / (Q : ℚ) <
          2 * (A.card : ℚ) / (2 ^ j : ℚ) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hspec
      exact lt_of_le_of_lt hdiv_lb hspec'
    have hmul := mul_lt_mul_of_pos_right hlt h2j_posQ
    have hrhs : 2 * (A.card : ℚ) / (2 ^ j : ℚ) * (2 ^ j : ℚ) = 2 * (A.card : ℚ) := by
      field_simp [h2j_posQ.ne']
    have hlhs : ((Nat.totient M : ℚ) / (M : ℚ)) * (∑ s ∈ T, (1 : ℚ) / (s : ℚ)) * (2 ^ j : ℚ) =
        ((Nat.totient M : ℚ) / (M : ℚ)) * ∑ s ∈ T, (2 ^ j : ℚ) / (s : ℚ) := by
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [hlhs, hrhs] at hmul
    exact hmul
  have hsum_lt :
      ((Nat.totient M : ℚ) / (M : ℚ)) *
        ∑ j ∈ Finset.Ico 8 J, ∑ s ∈ (S J).filter (fun s => 2 ^ (j - 8) < s), (2 ^ j : ℚ) / (s : ℚ) <
      2 * ∑ j ∈ Finset.Ico 8 J, (((S J).filter (fun s => 2 ^ (j - 8) < s ∧ s ≤ 2 ^ j)).card : ℚ) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_lt_sum_of_nonempty (Finset.nonempty_Ico.mpr (by omega)) hband
  have hrhs_le :
      ∑ j ∈ Finset.Ico 8 J, (((S J).filter (fun s => 2 ^ (j - 8) < s ∧ s ≤ 2 ^ j)).card : ℚ) ≤
      8 * ((S J).card : ℚ) := by
    have hrew : ∀ j, (((S J).filter (fun s => 2 ^ (j - 8) < s ∧ s ≤ 2 ^ j)).card : ℚ) =
        ∑ s ∈ S J, if 2 ^ (j - 8) < s ∧ s ≤ 2 ^ j then (1 : ℚ) else 0 := by
      intro j
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    simp_rw [hrew]
    rw [Finset.sum_comm]
    calc ∑ s ∈ S J, ∑ j ∈ Finset.Ico 8 J, (if 2 ^ (j - 8) < s ∧ s ≤ 2 ^ j then (1 : ℚ) else 0)
        ≤ ∑ s ∈ S J, (8 : ℚ) := by
          apply Finset.sum_le_sum
          intro s _
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            mul_one]
          have hsub : (Finset.Ico 8 J).filter (fun j => 2 ^ (j - 8) < s ∧ s ≤ 2 ^ j) ⊆
              Finset.Ico (Nat.clog 2 s) (Nat.clog 2 s + 8) := by
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_Ico] at hj ⊢
            have h1 : Nat.clog 2 s ≤ j := (Nat.clog_le_iff_le_pow (by norm_num)).mpr hj.2.2
            have h2 : j < Nat.clog 2 s + 8 := by
              by_contra hge
              have hle : Nat.clog 2 s ≤ j - 8 := by omega
              have := (Nat.clog_le_iff_le_pow (by norm_num)).mp hle
              omega
            exact ⟨h1, h2⟩
          have hcard : ((Finset.Ico 8 J).filter (fun j => 2 ^ (j - 8) < s ∧ s ≤ 2 ^ j)).card ≤ 8 := by
            calc _ ≤ (Finset.Ico (Nat.clog 2 s) (Nat.clog 2 s + 8)).card := Finset.card_le_card hsub
              _ = 8 := by simp
          exact_mod_cast hcard
      _ = 8 * ((S J).card : ℚ) := by simp [mul_comm]
  let S' : Finset ℕ := (S (J - 8)).filter (fun s => 2 ^ 16 < s)
  have hS'_sub : S' ⊆ S J := by
    intro s hs
    simp only [S', Finset.mem_filter, mem_S] at hs ⊢
    exact ⟨hs.1.1, le_trans hs.1.2.1 (Nat.pow_le_pow_right (by norm_num) (by omega)), hs.1.2.2⟩
  have hlhs_ge :
      255 * (S'.card : ℚ) ≤
      ∑ j ∈ Finset.Ico 8 J, ∑ s ∈ (S J).filter (fun s => 2 ^ (j - 8) < s), (2 ^ j : ℚ) / (s : ℚ) := by
    have hrew : ∀ j, ∑ s ∈ (S J).filter (fun s => 2 ^ (j - 8) < s), (2 ^ j : ℚ) / (s : ℚ) =
        ∑ s ∈ S J, if 2 ^ (j - 8) < s then (2 ^ j : ℚ) / (s : ℚ) else 0 := by
      intro j; rw [Finset.sum_filter]
    simp_rw [hrew]
    rw [Finset.sum_comm]
    calc 255 * (S'.card : ℚ)
        = ∑ _s ∈ S', (255 : ℚ) := by simp [mul_comm]
      _ ≤ ∑ s ∈ S', ∑ j ∈ Finset.Ico 8 J, if 2 ^ (j - 8) < s then (2 ^ j : ℚ) / (s : ℚ) else 0 := by
          apply Finset.sum_le_sum
          intro s hs
          simp only [S', Finset.mem_filter, mem_S] at hs
          let c := Nat.clog 2 s
          have hc_lo : 17 ≤ c := by
            by_contra hlt
            have hle : c ≤ 16 := by omega
            have := (Nat.clog_le_iff_le_pow (by norm_num)).mp hle
            omega
          have hc_hi : c ≤ J - 8 := (Nat.clog_le_iff_le_pow (by norm_num)).mpr hs.1.2.1
          have hs_gt_prev : 2 ^ (c - 1) < s := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
          have hs_le_pow : s ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) s
          have hsub : Finset.Ico 8 (c + 8) ⊆ Finset.Ico 8 J :=
            Finset.Ico_subset_Ico_right (by omega)
          have hterm : ∀ j ∈ Finset.Ico 8 (c + 8), 2 ^ (j - 8) < s := by
            intro j hj
            simp only [Finset.mem_Ico] at hj
            exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega)) hs_gt_prev
          have hge1 : ∑ j ∈ Finset.Ico 8 (c + 8), (2 ^ j : ℚ) / (s : ℚ) ≤
              ∑ j ∈ Finset.Ico 8 J, if 2 ^ (j - 8) < s then (2 ^ j : ℚ) / (s : ℚ) else 0 := by
            calc ∑ j ∈ Finset.Ico 8 (c + 8), (2 ^ j : ℚ) / (s : ℚ)
                = ∑ j ∈ Finset.Ico 8 (c + 8),
                    if 2 ^ (j - 8) < s then (2 ^ j : ℚ) / (s : ℚ) else 0 := by
                  apply Finset.sum_congr rfl
                  intro j hj; rw [if_pos (hterm j hj)]
              _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by
                  split_ifs <;> positivity)
          have hgeom : ∑ j ∈ Finset.Ico 8 (c + 8), (2 ^ j : ℚ) = (2 ^ (c + 8) : ℚ) - (2 ^ 8 : ℚ) := by
            have hshift : ∑ j ∈ Finset.Ico 8 (c + 8), (2 ^ j : ℚ) =
                ∑ k ∈ Finset.range c, (2 ^ (k + 8) : ℚ) := by
              apply Finset.sum_bij (fun j _ => j - 8)
              · intro j hj; simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢; omega
              · intro j1 hj1 j2 hj2 h; simp only [Finset.mem_Ico] at hj1 hj2; omega
              · intro k hk; simp only [Finset.mem_range] at hk
                exact ⟨k + 8, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
              · intro j hj; simp only [Finset.mem_Ico] at hj; congr 1; omega
            rw [hshift]
            have hfact : ∑ k ∈ Finset.range c, (2 ^ (k + 8) : ℚ) =
                (2 ^ 8 : ℚ) * ∑ k ∈ Finset.range c, (2 ^ k : ℚ) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              rw [pow_add]; ring
            rw [hfact]
            have hsum2 : ∑ k ∈ Finset.range c, (2 ^ k : ℚ) = (2 ^ c : ℚ) - 1 := by
              have := geom_sum_eq (by norm_num : (2 : ℚ) ≠ 1) c
              linarith
            rw [hsum2, pow_add]
            ring
          have hsum_div : ∑ j ∈ Finset.Ico 8 (c + 8), (2 ^ j : ℚ) / (s : ℚ) =
              ((2 ^ (c + 8) : ℚ) - (2 ^ 8 : ℚ)) / (s : ℚ) := by
            rw [← Finset.sum_div, hgeom]
          refine le_trans ?_ hge1
          rw [hsum_div]
          have hs_posQ : (0 : ℚ) < (s : ℚ) := Nat.cast_pos.mpr hs.1.2.2.1
          rw [le_div_iff₀ hs_posQ]
          have hs_leQ : (s : ℚ) ≤ (2 ^ c : ℚ) := by exact_mod_cast hs_le_pow
          have hs_gt256 : (2 ^ 8 : ℚ) ≤ (s : ℚ) := by
            have : 2 ^ 8 ≤ s := le_trans (by norm_num) hs.2.le
            exact_mod_cast this
          have hpow8 : (2 ^ (c + 8) : ℚ) = 256 * (2 ^ c : ℚ) := by
            rw [pow_add, show (2 : ℚ) ^ 8 = 256 by norm_num]; ring
          rw [hpow8]
          linarith
      _ ≤ ∑ s ∈ S J, ∑ j ∈ Finset.Ico 8 J, if 2 ^ (j - 8) < s then (2 ^ j : ℚ) / (s : ℚ) else 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg hS'_sub (fun s _ _ =>
            Finset.sum_nonneg fun j _ => by split_ifs <;> positivity)
  have halpha : (1 : ℚ) / 10 ≤ (Nat.totient M : ℚ) / (M : ℚ) := by
    have hMQ : (0 : ℚ) < (M : ℚ) := Nat.cast_pos.mpr hM_pos
    rw [div_le_div_iff₀ (by norm_num) hMQ]
    have hMbound : (M : ℚ) ≤ 10 * (Nat.totient M : ℚ) := by exact_mod_cast hM_tot
    linarith
  have hcomb : (1 : ℚ) / 10 * (255 * (S'.card : ℚ)) < 2 * (8 * ((S J).card : ℚ)) := by
    have h1 : (1 : ℚ) / 10 * (255 * (S'.card : ℚ)) ≤
        ((Nat.totient M : ℚ) / (M : ℚ)) *
          ∑ j ∈ Finset.Ico 8 J, ∑ s ∈ (S J).filter (fun s => 2 ^ (j - 8) < s), (2 ^ j : ℚ) / (s : ℚ) := by
      exact mul_le_mul halpha hlhs_ge (by positivity) (by positivity)
    linarith
  have hS'_card : (S (J - 8)).card ≤ S'.card + (S 16).card := by
    have hsub : S (J - 8) ⊆ S' ∪ S 16 := by
      intro s hs
      by_cases h16 : 2 ^ 16 < s
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs, h16⟩)
      · refine Finset.mem_union_right _ ?_
        rw [mem_S] at hs ⊢
        exact ⟨hs.1, by omega, hs.2.2⟩
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hS'_cardQ : ((S (J - 8)).card : ℚ) ≤ (S'.card : ℚ) + ((S 16).card : ℚ) := by
    exact_mod_cast hS'_card
  have hfinalQ : (51 : ℚ) * ((S (J - 8)).card : ℚ) ≤ 32 * ((S J).card : ℚ) + 51 * ((S 16).card : ℚ) := by
    linarith
  exact_mod_cast hfinalQ

end OMA_Erdos488

theorem OMA.disproof : ¬ (type_of% @Erdos488.erdos_488) := by
  intro h488
  let J0 : ℕ := 5 * 2 ^ 16 + 8
  have hstep : ∀ k : ℕ, 5 * (OMA_Erdos488.S (J0 + 8 * k)).card ≤
      4 * (OMA_Erdos488.S (J0 + 8 * (k + 1))).card := by
    intro k
    have hg := OMA_Erdos488.growth_step OMA_Erdos488.W_gt_two
      (fun _ hp => OMA_Erdos488.dvd_W_of_mem_P hp) OMA_Erdos488.W_totient_bound
      h488 (J := J0 + 8 * (k + 1)) (by omega)
    have hsub : J0 + 8 * (k + 1) - 8 = J0 + 8 * k := by omega
    rw [hsub] at hg
    have hge : 5 * 2 ^ 16 ≤ (OMA_Erdos488.S (J0 + 8 * k)).card := by
      have := OMA_Erdos488.card_S_ge_pow_two (J0 + 8 * k)
      omega
    have h16 := OMA_Erdos488.card_S_16_le
    omega
  have hiter : ∀ k : ℕ, 5 ^ k * (OMA_Erdos488.S J0).card ≤
      4 ^ k * (OMA_Erdos488.S (J0 + 8 * k)).card := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk := hstep k
      calc 5 ^ (k + 1) * (OMA_Erdos488.S J0).card
          = 5 * (5 ^ k * (OMA_Erdos488.S J0).card) := by ring
        _ ≤ 5 * (4 ^ k * (OMA_Erdos488.S (J0 + 8 * k)).card) := Nat.mul_le_mul_left 5 ih
        _ = 4 ^ k * (5 * (OMA_Erdos488.S (J0 + 8 * k)).card) := by ring
        _ ≤ 4 ^ k * (4 * (OMA_Erdos488.S (J0 + 8 * (k + 1))).card) := Nat.mul_le_mul_left _ hk
        _ = 4 ^ (k + 1) * (OMA_Erdos488.S (J0 + 8 * (k + 1))).card := by ring
  have hbase : 1 ≤ (OMA_Erdos488.S J0).card := by
    have := OMA_Erdos488.card_S_ge_pow_two J0
    omega
  have h8000 := hiter 8000
  have hlb : 5 ^ 8000 ≤ 4 ^ 8000 * (OMA_Erdos488.S (J0 + 8 * 8000)).card := by
    calc 5 ^ 8000 = 5 ^ 8000 * 1 := (mul_one _).symm
      _ ≤ 5 ^ 8000 * (OMA_Erdos488.S J0).card := Nat.mul_le_mul_left _ hbase
      _ ≤ 4 ^ 8000 * (OMA_Erdos488.S (J0 + 8 * 8000)).card := h8000
  have hub1 : (OMA_Erdos488.S (J0 + 8 * 8000)).card ≤ 2 ^ 1026 := by
    have h1 := OMA_Erdos488.card_S_le (J0 + 8 * 8000)
    have h2 : J0 + 8 * 8000 + 1 ≤ 2 ^ 19 := by norm_num [J0]
    calc (OMA_Erdos488.S (J0 + 8 * 8000)).card
        ≤ (J0 + 8 * 8000 + 1) ^ 54 := h1
      _ ≤ (2 ^ 19) ^ 54 := Nat.pow_le_pow_left h2 54
      _ = 2 ^ 1026 := by rw [← pow_mul]
  have hcontra : 4 ^ 8000 * 2 ^ 1026 < 5 ^ 8000 := by
    have h1 : 4 ^ 8000 * 2 ^ 1026 < 4 ^ 8000 * 2 ^ 2000 :=
      Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega : 1026 < 2000))
        (pow_pos (by omega : 0 < 4) 8000)
    have h2 : 4 ^ 8000 * 2 ^ 2000 = 512 ^ 2000 := by
      calc 4 ^ 8000 * 2 ^ 2000 = (4 ^ 4) ^ 2000 * 2 ^ 2000 := by rw [← pow_mul]
        _ = (4 ^ 4 * 2) ^ 2000 := by rw [← mul_pow]
        _ = 512 ^ 2000 := by rw [show 4 ^ 4 * 2 = 512 by norm_num]
    have h3 : 512 ^ 2000 < 625 ^ 2000 :=
      Nat.pow_lt_pow_left (by norm_num) (by norm_num)
    have h4 : 625 ^ 2000 = 5 ^ 8000 := by
      calc 625 ^ 2000 = (5 ^ 4) ^ 2000 := by rw [show 5 ^ 4 = 625 by norm_num]
        _ = 5 ^ 8000 := by rw [← pow_mul]
    calc 4 ^ 8000 * 2 ^ 1026 < 4 ^ 8000 * 2 ^ 2000 := h1
      _ = 512 ^ 2000 := h2
      _ < 625 ^ 2000 := h3
      _ = 5 ^ 8000 := h4
  have hub2 : 4 ^ 8000 * (OMA_Erdos488.S (J0 + 8 * 8000)).card ≤ 4 ^ 8000 * 2 ^ 1026 :=
    Nat.mul_le_mul_left (4 ^ 8000) hub1
  exact Nat.not_lt.mpr (le_trans hlb hub2) hcontra
