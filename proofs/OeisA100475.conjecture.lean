import FormalConjectures.OEIS.«100475»

/-!
Disproof of `OeisA100475.conjecture`: no positive starting value enters an ultimately periodic
cycle under $k \mapsto \operatorname{reverseDigits}(p_k)$.

Proof structure:
1. Since $p_k > k$ and $10 \nmid p_k$, reversing the decimal digits of $p_k$ preserves digit count,
   so the decimal digit count $D(aStartAt\ x\ n)$ is nondecreasing.
2. Any periodic tail has constant digit count $D \ge 1$, forcing $10^{D-1} \le \pi(10^D)$.
3. We prove $\pi(10^D) < 10^{D-1}$ for all $D \ge 5$: exact Legendre sieve for $D = 5, 6$,
   dyadic Chebyshev primorial bounds for $D = 7, 8$, and Erdős's primorial bound
   $\prod_{p \le n} p \le 4^n$ for $D \ge 9$.
4. Thus any cycle stays in $[1, 1229]$ (since $p_{1230} = 10007 > 10^4$), which is ruled out by
   checking that every start in $[1, 1229]$ reaches $\ge 1230$ within $10$ steps.
-/

namespace OeisA100475Disproof

private def piCount (N : ℕ) : ℕ := (Finset.filter Nat.Prime (Finset.Icc 1 N)).card

/- ### Part 0: Fast primality tester for $n \le 10007$ -/

private def primes25 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

private def isPrime10007 (n : ℕ) : Bool :=
  n ≥ 2 &&
  (4 > n || n % 2 != 0) && (9 > n || n % 3 != 0) && (25 > n || n % 5 != 0) &&
  (49 > n || n % 7 != 0) && (121 > n || n % 11 != 0) && (169 > n || n % 13 != 0) &&
  (289 > n || n % 17 != 0) && (361 > n || n % 19 != 0) && (529 > n || n % 23 != 0) &&
  (841 > n || n % 29 != 0) && (961 > n || n % 31 != 0) && (1369 > n || n % 37 != 0) &&
  (1681 > n || n % 41 != 0) && (1849 > n || n % 43 != 0) && (2209 > n || n % 47 != 0) &&
  (2809 > n || n % 53 != 0) && (3481 > n || n % 59 != 0) && (3721 > n || n % 61 != 0) &&
  (4489 > n || n % 67 != 0) && (5041 > n || n % 71 != 0) && (5329 > n || n % 73 != 0) &&
  (6241 > n || n % 79 != 0) && (6889 > n || n % 83 != 0) && (7921 > n || n % 89 != 0) &&
  (9409 > n || n % 97 != 0)

private lemma isPrime10007_eq_all (n : ℕ) :
    isPrime10007 n = (decide (2 ≤ n) && primes25.all (fun p => decide (p * p > n) || n % p != 0)) := by
  simp only [isPrime10007, primes25, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc]

private lemma primes25_prime : ∀ p ∈ primes25, p.Prime := by
  intro p hp
  simp only [primes25, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> norm_num

private def checkNonPrime100 : ℕ → Bool
  | 0 => true
  | k + 1 =>
    (k < 2 || primes25.elem k || (k > 2 && k % 2 == 0) || (k > 3 && k % 3 == 0) ||
      (k > 5 && k % 5 == 0) || (k > 7 && k % 7 == 0)) && checkNonPrime100 k

private lemma checkNonPrime100_sound :
    ∀ n : ℕ, checkNonPrime100 n = true → ∀ p : ℕ, p < n → p.Prime → p ∈ primes25
  | 0, _, p, hp, _ => by omega
  | k + 1, h, p, hp, hpr => by
    simp only [checkNonPrime100, Bool.and_eq_true] at h
    by_cases hpk : p = k
    · subst hpk
      have h1 := h.1
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.elem_eq_mem,
        beq_iff_eq] at h1
      have hp2 : 2 ≤ p := hpr.two_le
      rcases h1 with ((((hsmall | hmem) | ⟨hgt, hmod⟩) | ⟨hgt, hmod⟩) | ⟨hgt, hmod⟩) | ⟨hgt, hmod⟩
      · omega
      · exact hmem
      · exfalso
        have hdvd : 2 ∣ p := Nat.dvd_of_mod_eq_zero hmod
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpr).mp hdvd
        omega
      · exfalso
        have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hmod
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).mp hdvd
        omega
      · exfalso
        have hdvd : 5 ∣ p := Nat.dvd_of_mod_eq_zero hmod
        have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) hpr).mp hdvd
        omega
      · exfalso
        have hdvd : 7 ∣ p := Nat.dvd_of_mod_eq_zero hmod
        have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 7) hpr).mp hdvd
        omega
    · exact checkNonPrime100_sound k h.2 p (by omega) hpr

private lemma prime_mem_primes25 {p : ℕ} (hp : p.Prime) (hle : p ≤ 100) : p ∈ primes25 := by
  have h : checkNonPrime100 101 = true := by decide +kernel
  exact checkNonPrime100_sound 101 h p (by omega) hp

private lemma isPrime10007_iff {n : ℕ} (hn : n ≤ 10007) : isPrime10007 n = true ↔ n.Prime := by
  rw [isPrime10007_eq_all]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, bne_iff_ne]
  constructor
  · rintro ⟨hn2, hall⟩
    by_contra hnotp
    set p := n.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpdvd : p ∣ n := Nat.minFac_dvd n
    have hpsq : p * p ≤ n := by
      have := Nat.minFac_sq_le_self (by omega) hnotp
      simpa [sq] using this
    have hple : p ≤ 100 := by nlinarith only [hpsq, hn]
    have hmem : p ∈ primes25 := prime_mem_primes25 hp hple
    rcases hall p hmem with hgt | hne
    · omega
    · exact hne (Nat.mod_eq_zero_of_dvd hpdvd)
  · intro hpr
    refine ⟨hpr.two_le, fun p hp => ?_⟩
    by_cases hgt : p * p > n
    · exact Or.inl hgt
    · right
      intro h0
      have hdvd : p ∣ n := Nat.dvd_of_mod_eq_zero h0
      have hpeq : p = n := (Nat.prime_dvd_prime_iff_eq (primes25_prime p hp) hpr).mp hdvd
      have hp2 : 2 ≤ p := (primes25_prime p hp).two_le
      nlinarith only [hgt, hpeq, hp2]

/- ### Part 1: Legendre sieve for $D = 5, 6$ and wheel-210 bound -/

private def phiSpec (P : List ℕ) (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun n => ∀ p ∈ P, ¬ p ∣ n)).card

private lemma phiSpec_nil (x : ℕ) : phiSpec [] x = x := by
  simp [phiSpec]

private lemma phiSpec_cons {q : ℕ} {P : List ℕ} (hq : 0 < q)
    (hcop : ∀ p ∈ P, Nat.Coprime p q) (x : ℕ) :
    phiSpec (q :: P) x + phiSpec P (x / q) = phiSpec P x := by
  unfold phiSpec
  set S := (Finset.Icc 1 x).filter (fun n => ∀ p ∈ P, ¬ p ∣ n)
  set Snd := S.filter (fun n => ¬ q ∣ n)
  set Sd := S.filter (fun n => q ∣ n)
  have hSnd : (Finset.Icc 1 x).filter (fun n => ∀ p ∈ q :: P, ¬ p ∣ n) = Snd := by
    ext n
    simp only [Finset.mem_filter, List.mem_cons, forall_eq_or_imp, Snd, S]
    tauto
  have hpart : Snd.card + Sd.card = S.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext n
      simp only [Finset.mem_union, Finset.mem_filter, Snd, Sd]
      tauto
    · rw [Finset.disjoint_left]
      intro n h1 h2
      simp only [Finset.mem_filter, Snd, Sd] at h1 h2
      exact h1.2 h2.2
  have hbij : Sd.card = ((Finset.Icc 1 (x / q)).filter (fun m => ∀ p ∈ P, ¬ p ∣ m)).card := by
    refine Finset.card_bij (fun n _ => n / q) ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc, Sd, S] at hn ⊢
      obtain ⟨⟨⟨hn1, hnx⟩, hP⟩, hqn⟩ := hn
      refine ⟨⟨?_, Nat.div_le_div_right hnx⟩, ?_⟩
      · have hle : q ≤ n := Nat.le_of_dvd (by omega) hqn
        exact (Nat.le_div_iff_mul_le hq).mpr (by omega)
      · intro p hp hdvd
        exact hP p hp (dvd_trans hdvd (Nat.div_dvd_of_dvd hqn))
    · intro a ha b hb hab
      simp only [Finset.mem_filter, Sd] at ha hb
      rw [← Nat.mul_div_cancel' ha.2, ← Nat.mul_div_cancel' hb.2, hab]
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_Icc, Sd, S] at hm ⊢
      obtain ⟨⟨hm1, hmx⟩, hP⟩ := hm
      refine ⟨q * m, ⟨⟨⟨?_, ?_⟩, ?_⟩, dvd_mul_right q m⟩, Nat.mul_div_cancel_left m hq⟩
      · exact Nat.mul_pos hq hm1
      · exact (Nat.le_div_iff_mul_le hq).mp hmx |> fun h => by linarith only [h]
      · intro p hp hdvd
        have hpm : p ∣ m := (hcop p hp).dvd_of_dvd_mul_left hdvd
        exact hP p hp hpm
  rw [hSnd, ← hbij, hpart]

private def phi210 (x : ℕ) : ℕ :=
  (x + x / 6 + x / 10 + x / 14 + x / 15 + x / 21 + x / 35 + x / 210)
    - (x / 2 + x / 3 + x / 5 + x / 7 + x / 30 + x / 42 + x / 70 + x / 105)

private lemma phi210_eq_phiSpec (x : ℕ) : phi210 x = phiSpec [7, 5, 3, 2] x := by
  have h2 : ∀ y : ℕ, phiSpec [2] y + y / 2 = y := fun y => by
    have := phiSpec_cons (q := 2) (P := []) (by decide) (by simp) y
    simp only [phiSpec_nil] at this
    exact this
  have h3 : ∀ y : ℕ, phiSpec [3, 2] y + phiSpec [2] (y / 3) = phiSpec [2] y := fun y =>
    phiSpec_cons (q := 3) (P := [2]) (by decide) (by decide) y
  have h5 : ∀ y : ℕ, phiSpec [5, 3, 2] y + phiSpec [3, 2] (y / 5) = phiSpec [3, 2] y := fun y =>
    phiSpec_cons (q := 5) (P := [3, 2]) (by decide) (by decide) y
  have h7 : phiSpec [7, 5, 3, 2] x + phiSpec [5, 3, 2] (x / 7) = phiSpec [5, 3, 2] x :=
    phiSpec_cons (q := 7) (P := [5, 3, 2]) (by decide) (by decide) x
  have e1 := h5 x
  have e2 := h5 (x / 7)
  have e3 := h3 x
  have e4 := h3 (x / 5)
  have e5 := h3 (x / 7)
  have e6 := h3 (x / 35)
  have e7 := h2 x
  have e8 := h2 (x / 3)
  have e9 := h2 (x / 5)
  have e10 := h2 (x / 15)
  have e11 := h2 (x / 7)
  have e12 := h2 (x / 21)
  have e13 := h2 (x / 35)
  have e14 := h2 (x / 105)
  rw [Nat.div_div_eq_div_mul] at e2 e4 e5 e6 e8 e9 e10 e11 e12 e13 e14
  norm_num only at e2 e4 e5 e6 e8 e9 e10 e11 e12 e13 e14
  unfold phi210
  have hsum : phiSpec [7, 5, 3, 2] x +
      (x / 2 + x / 3 + x / 5 + x / 7 + x / 30 + x / 42 + x / 70 + x / 105) =
      x + x / 6 + x / 10 + x / 14 + x / 15 + x / 21 + x / 35 + x / 210 := by
    linarith only [h7, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14]
  exact (Nat.eq_sub_of_add_eq hsum).symm

private def phiRec : List ℕ → ℕ → ℕ
  | [], x => phi210 x
  | p :: rest, x => if x < p then phi210 x else phiRec rest x - phiRec rest (x / p)

private lemma phiSpec_drop_large {P Q : List ℕ} {x : ℕ} (h : ∀ p ∈ P, x < p) :
    phiSpec (P ++ Q) x = phiSpec Q x := by
  unfold phiSpec
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, List.mem_append]
  constructor
  · rintro ⟨hn, hall⟩
    exact ⟨hn, fun p hp => hall p (Or.inr hp)⟩
  · rintro ⟨hn, hall⟩
    refine ⟨hn, fun p hp => ?_⟩
    rcases hp with hpP | hpQ
    · intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      have := h p hpP
      omega
    · exact hall p hpQ

private lemma phiRec_eq_phiSpec :
    ∀ (ps : List ℕ),
      (∀ p ∈ ps, 11 ≤ p) →
      ps.Pairwise (· < ·) →
      (ps ++ [7, 5, 3, 2]).Pairwise Nat.Coprime →
      ∀ x : ℕ, phiRec ps x = phiSpec (ps ++ [7, 5, 3, 2]) x
  | [], _, _, _, x => by
    simp [phiRec, phi210_eq_phiSpec]
  | p :: rest, hge, hlt, hpair, x => by
    unfold phiRec
    have hlt_cons : (∀ q ∈ rest, p < q) ∧ rest.Pairwise (· < ·) := List.pairwise_cons.mp hlt
    split_ifs with hxp
    · rw [phi210_eq_phiSpec]
      refine (phiSpec_drop_large (P := p :: rest) (Q := [7, 5, 3, 2]) fun q hq => ?_).symm
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hxp
      · exact lt_trans hxp (hlt_cons.1 q hq)
    · have hge_rest : ∀ q ∈ rest, 11 ≤ q := fun q hq => hge q (List.mem_cons_of_mem p hq)
      have hpair_cons : (∀ q ∈ rest ++ [7, 5, 3, 2], Nat.Coprime p q) ∧
          (rest ++ [7, 5, 3, 2]).Pairwise Nat.Coprime :=
        List.pairwise_cons.mp hpair
      have ih := phiRec_eq_phiSpec rest hge_rest hlt_cons.2 hpair_cons.2
      rw [ih x, ih (x / p)]
      have hp_pos : 0 < p := by have := hge p (List.mem_cons_self ..); omega
      have hcop_sym : ∀ q ∈ rest ++ [7, 5, 3, 2], Nat.Coprime q p :=
        fun q hq => (hpair_cons.1 q hq).symm
      have hstep := phiSpec_cons hp_pos hcop_sym x
      change phiSpec (rest ++ [7, 5, 3, 2]) x - phiSpec (rest ++ [7, 5, 3, 2]) (x / p) =
        phiSpec (p :: (rest ++ [7, 5, 3, 2])) x
      omega

private lemma piCount_add_one_le_phiSpec {P : List ℕ} (hP : ∀ p ∈ P, p.Prime)
    {N : ℕ} (hN : 1 ≤ N) :
    piCount N + 1 ≤ P.length + phiSpec P N := by
  unfold piCount phiSpec
  set A := (Finset.Icc 1 N).filter Nat.Prime
  set B := (Finset.Icc 1 N).filter (fun n => ∀ p ∈ P, ¬ p ∣ n)
  have h1B : 1 ∈ B := by
    simp only [Finset.mem_filter, Finset.mem_Icc, B]
    refine ⟨⟨le_rfl, hN⟩, fun p hp hdvd => ?_⟩
    have := (hP p hp).two_le
    have := Nat.le_of_dvd one_pos hdvd
    omega
  have h1A : 1 ∉ A := by
    simp only [Finset.mem_filter, A]
    intro h
    exact Nat.not_prime_one h.2
  have hsub : insert 1 A ⊆ P.toFinset ∪ B := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset] at hx ⊢
    rcases hx with rfl | hxA
    · exact Or.inr h1B
    · by_cases hxP : x ∈ P
      · exact Or.inl hxP
      · right
        simp only [Finset.mem_filter, A, B] at hxA ⊢
        refine ⟨hxA.1, fun p hp hdvd => ?_⟩
        have hpx : p = x := (Nat.prime_dvd_prime_iff_eq (hP p hp) hxA.2).mp hdvd
        exact hxP (hpx ▸ hp)
  have hcard1 : (insert 1 A).card = A.card + 1 := Finset.card_insert_of_notMem h1A
  have hcard2 : (P.toFinset ∪ B).card ≤ P.toFinset.card + B.card := Finset.card_union_le _ _
  have hcard3 : P.toFinset.card ≤ P.length := List.toFinset_card_le P
  have hle := Finset.card_le_card hsub
  omega

private def ps48 : List ℕ :=
  [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103,
   107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199,
   211, 223, 227, 229, 233, 239]

private lemma ps48_all_ge11 : ∀ p ∈ ps48, 11 ≤ p := by decide +kernel

private lemma ps48_sorted : ps48.Pairwise (· < ·) := by decide +kernel

private lemma ps48_full_prime : ∀ p ∈ ps48 ++ [7, 5, 3, 2], p.Prime := by
  have hall : (ps48 ++ [7, 5, 3, 2]).all (fun p => decide (p ≤ 10007) && isPrime10007 p) = true := by
    decide +kernel
  rw [List.all_eq_true] at hall
  intro p hp
  have h1 := hall p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  exact (isPrime10007_iff h1.1).mp h1.2

private lemma ps48_full_pairwise : (ps48 ++ [7, 5, 3, 2]).Pairwise Nat.Coprime := by
  have hnodup : (ps48 ++ [7, 5, 3, 2]).Nodup := by decide +kernel
  exact hnodup.imp_of_mem fun {a b} ha hb hne =>
    (Nat.coprime_primes (ps48_full_prime a ha) (ps48_full_prime b hb)).mpr hne

private lemma piCount_10e5 : piCount (10 ^ 5) < 10 ^ 4 := by
  have h1 := piCount_add_one_le_phiSpec ps48_full_prime (N := 100000) (by decide)
  have h2 := phiRec_eq_phiSpec ps48 ps48_all_ge11 ps48_sorted ps48_full_pairwise 100000
  have hlen : (ps48 ++ [7, 5, 3, 2]).length = 52 := by decide
  have hchk : phiRec ps48 100000 + 51 < 10000 := by decide +kernel
  rw [hlen, ← h2] at h1
  change piCount 100000 < 10000
  omega

private lemma piCount_10e6 : piCount (10 ^ 6) < 10 ^ 5 := by
  have h1 := piCount_add_one_le_phiSpec ps48_full_prime (N := 1000000) (by decide)
  have h2 := phiRec_eq_phiSpec ps48 ps48_all_ge11 ps48_sorted ps48_full_pairwise 1000000
  have hlen : (ps48 ++ [7, 5, 3, 2]).length = 52 := by decide
  have hchk : phiRec ps48 1000000 + 51 < 100000 := by decide +kernel
  rw [hlen, ← h2] at h1
  change piCount 1000000 < 100000
  omega

private lemma piCount_le_phi210 {N : ℕ} (hN : 1 ≤ N) : piCount N ≤ phi210 N + 3 := by
  have hP : ∀ p ∈ ([7, 5, 3, 2] : List ℕ), p.Prime := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  have h1 := piCount_add_one_le_phiSpec hP hN
  rw [← phi210_eq_phiSpec] at h1
  simp only [List.length_cons, List.length_nil] at h1
  omega

/- ### Part 2: Elementary Chebyshev / Erdős primorial bounds for $D \ge 7$ -/

private lemma prod_primes_dvd_of_dvd {S : Finset ℕ} {M : ℕ}
    (hpr : ∀ p ∈ S, p.Prime) (hdvd : ∀ p ∈ S, p ∣ M) : (∏ p ∈ S, p) ∣ M := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha_pr : a.Prime := hpr a (Finset.mem_insert_self a s)
    have hs_pr : ∀ p ∈ s, p.Prime := fun p hp => hpr p (Finset.mem_insert_of_mem hp)
    have ha_dvd : a ∣ M := hdvd a (Finset.mem_insert_self a s)
    have hs_dvd : (∏ p ∈ s, p) ∣ M := ih hs_pr (fun p hp => hdvd p (Finset.mem_insert_of_mem hp))
    have hcop : Nat.Coprime a (∏ p ∈ s, p) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes ha_pr (hs_pr p hp)).mpr fun heq => ha (heq ▸ hp)
    exact hcop.mul_dvd_of_dvd_of_dvd ha_dvd hs_dvd

private lemma prod_primes_Ioc_le_four_pow (m : ℕ) :
    ∏ p ∈ (Finset.Ioc m (2 * m)).filter Nat.Prime, p ≤ 4 ^ m := by
  have hdvd : (∏ p ∈ (Finset.Ioc m (2 * m)).filter Nat.Prime, p) ∣ (2 * m).choose m := by
    apply prod_primes_dvd_of_dvd (fun p hp => (Finset.mem_filter.mp hp).2)
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hmp, hp2m⟩, hpr⟩ := hp
    have hfac := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
    rw [show 2 * m - m = m by omega] at hfac
    have hp_dvd_top : p ∣ (2 * m).factorial := hpr.dvd_factorial.mpr hp2m
    rw [← hfac] at hp_dvd_top
    have hp_ndvd_m : ¬ p ∣ m.factorial := by
      rw [hpr.dvd_factorial]; omega
    rcases hpr.dvd_mul.mp hp_dvd_top with h1 | h2
    · rcases hpr.dvd_mul.mp h1 with h3 | h4
      · exact h3
      · exact absurd h4 hp_ndvd_m
    · exact absurd h2 hp_ndvd_m
  have hle1 : (∏ p ∈ (Finset.Ioc m (2 * m)).filter Nat.Prime, p) ≤ (2 * m).choose m :=
    Nat.le_of_dvd (Nat.choose_pos (by omega)) hdvd
  have hle2 : (2 * m).choose m ≤ 4 ^ m := by
    calc (2 * m).choose m ≤ ∑ k ∈ Finset.range (2 * m + 1), (2 * m).choose k :=
          Finset.single_le_sum (f := fun k => (2 * m).choose k) (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.mpr (by omega))
      _ = 2 ^ (2 * m) := Nat.sum_range_choose (2 * m)
      _ = 4 ^ m := by rw [pow_mul]; norm_num
  exact le_trans hle1 hle2

private lemma piCount_Ioc_eq_sub {a b : ℕ} (hab : a ≤ b) :
    ((Finset.Ioc a b).filter Nat.Prime).card = piCount b - piCount a := by
  unfold piCount
  have hunion : (Finset.Icc 1 b).filter Nat.Prime =
      (Finset.Icc 1 a).filter Nat.Prime ∪ (Finset.Ioc a b).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, hb⟩, hpr⟩
      by_cases hpa : p ≤ a
      · exact Or.inl ⟨⟨h1, hpa⟩, hpr⟩
      · exact Or.inr ⟨⟨by omega, hb⟩, hpr⟩
    · rintro (⟨⟨h1, ha⟩, hpr⟩ | ⟨⟨ha, hb⟩, hpr⟩)
      · exact ⟨⟨h1, le_trans ha hab⟩, hpr⟩
      · exact ⟨⟨by omega, hb⟩, hpr⟩
  have hdisj : Disjoint ((Finset.Icc 1 a).filter Nat.Prime) ((Finset.Ioc a b).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at h1 h2
    omega
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  omega

private lemma piCount_double_sub_le {m a b : ℕ} (hm : 2 ≤ m) (hb : 0 < b) (hpow : 4 ^ b < m ^ a) :
    piCount (2 * m) - piCount m ≤ (a * m - 1) / b := by
  set S := (Finset.Ioc m (2 * m)).filter Nat.Prime
  have hcard : S.card = piCount (2 * m) - piCount m := piCount_Ioc_eq_sub (by omega)
  have hm_pow : m ^ S.card ≤ 4 ^ m := by
    calc m ^ S.card = ∏ _p ∈ S, m := by simp
      _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod' fun p hp =>
            le_of_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
      _ ≤ 4 ^ m := prod_primes_Ioc_le_four_pow m
  have hpow_b : m ^ (b * S.card) < m ^ (a * m) := by
    calc m ^ (b * S.card) = (m ^ S.card) ^ b := by rw [mul_comm, pow_mul]
      _ ≤ (4 ^ m) ^ b := Nat.pow_le_pow_left hm_pow b
      _ = (4 ^ b) ^ m := by rw [← pow_mul, mul_comm m b, pow_mul]
      _ < (m ^ a) ^ m := Nat.pow_lt_pow_left hpow (by omega)
      _ = m ^ (a * m) := by rw [← pow_mul]
  have hlt : b * S.card < a * m := (Nat.pow_lt_pow_iff_right (by omega : 1 < m)).mp hpow_b
  rw [← hcard]
  exact (Nat.le_div_iff_mul_le hb).mpr (by rw [mul_comm]; omega)

private lemma piCount_10e7 : piCount (10 ^ 7) < 10 ^ 6 := by
  have h1 := piCount_double_sub_le (m := 5000000) (a := 1) (b := 11) (by decide) (by decide) (by norm_num)
  have h2 := piCount_double_sub_le (m := 2500000) (a := 2) (b := 21) (by decide) (by decide) (by norm_num)
  have h3 := piCount_double_sub_le (m := 1250000) (a := 1) (b := 10) (by decide) (by decide) (by norm_num)
  have h4 := piCount_double_sub_le (m := 625000) (a := 2) (b := 19) (by decide) (by decide) (by norm_num)
  have h5 := piCount_double_sub_le (m := 312500) (a := 1) (b := 9) (by decide) (by decide) (by norm_num)
  have hrem := piCount_le_phi210 (N := 312500) (by decide)
  have hphi : phi210 312500 = 71429 := by decide
  norm_num at h1 h2 h3 h4 h5 hrem ⊢
  omega

private lemma piCount_10e8 : piCount (10 ^ 8) < 10 ^ 7 := by
  have h1 := piCount_double_sub_le (m := 50000000) (a := 4) (b := 51) (by decide) (by decide) (by norm_num)
  have h2 := piCount_double_sub_le (m := 25000000) (a := 4) (b := 49) (by decide) (by decide) (by norm_num)
  have h3 := piCount_double_sub_le (m := 12500000) (a := 4) (b := 47) (by decide) (by decide) (by norm_num)
  have h4 := piCount_double_sub_le (m := 6250000) (a := 4) (b := 45) (by decide) (by decide) (by norm_num)
  have hrem := piCount_le_phi210 (N := 6250000) (by decide)
  have hphi : phi210 6250000 = 1428571 := by decide
  norm_num at h1 h2 h3 h4 hrem ⊢
  omega

private lemma prod_primes_le_four_pow (n : ℕ) :
    ∏ p ∈ (Finset.Icc 1 n).filter Nat.Prime, p ≤ 4 ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h2 : n ≤ 2
    · interval_cases n <;> decide
    · by_cases hpar : n % 2 = 0
      · have hnotp : ¬ n.Prime := by
          intro hpr
          have h2dvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero hpar
          have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpr).mp h2dvd
          omega
        have heq : (Finset.Icc 1 n).filter Nat.Prime = (Finset.Icc 1 (n - 1)).filter Nat.Prime := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_Icc]
          constructor
          · rintro ⟨⟨h1, hle⟩, hpr⟩
            have hne : p ≠ n := fun h => hnotp (h ▸ hpr)
            exact ⟨⟨h1, by omega⟩, hpr⟩
          · rintro ⟨⟨h1, hle⟩, hpr⟩
            exact ⟨⟨h1, by omega⟩, hpr⟩
        rw [heq]
        calc ∏ p ∈ (Finset.Icc 1 (n - 1)).filter Nat.Prime, p ≤ 4 ^ (n - 1) := ih (n - 1) (by omega)
          _ ≤ 4 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      · set m := n / 2
        have hn_eq : n = 2 * m + 1 := by omega
        have hm1 : 1 ≤ m := by omega
        have hunion : (Finset.Icc 1 n).filter Nat.Prime =
            (Finset.Icc 1 (m + 1)).filter Nat.Prime ∪ (Finset.Ioc (m + 1) n).filter Nat.Prime := by
          ext p
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
          constructor
          · rintro ⟨⟨h1, hle⟩, hpr⟩
            by_cases hpm : p ≤ m + 1
            · exact Or.inl ⟨⟨h1, hpm⟩, hpr⟩
            · exact Or.inr ⟨⟨by omega, hle⟩, hpr⟩
          · rintro (⟨⟨h1, hle⟩, hpr⟩ | ⟨⟨hgt, hle⟩, hpr⟩)
            · exact ⟨⟨h1, by omega⟩, hpr⟩
            · exact ⟨⟨by omega, hle⟩, hpr⟩
        have hdisj : Disjoint ((Finset.Icc 1 (m + 1)).filter Nat.Prime)
            ((Finset.Ioc (m + 1) n).filter Nat.Prime) := by
          rw [Finset.disjoint_left]
          intro p h1 h2
          simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at h1 h2
          omega
        have hhi_dvd : (∏ p ∈ (Finset.Ioc (m + 1) n).filter Nat.Prime, p) ∣ n.choose m := by
          apply prod_primes_dvd_of_dvd (fun p hp => (Finset.mem_filter.mp hp).2)
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
          obtain ⟨⟨hgt, hle⟩, hpr⟩ := hp
          have hfac := Nat.choose_mul_factorial_mul_factorial (show m ≤ n by omega)
          have hsub : n - m = m + 1 := by omega
          rw [hsub] at hfac
          have hp_top : p ∣ n.factorial := hpr.dvd_factorial.mpr hle
          rw [← hfac] at hp_top
          have hnd1 : ¬ p ∣ m.factorial := by rw [hpr.dvd_factorial]; omega
          have hnd2 : ¬ p ∣ (m + 1).factorial := by rw [hpr.dvd_factorial]; omega
          rcases hpr.dvd_mul.mp hp_top with h1 | h2
          · rcases hpr.dvd_mul.mp h1 with h3 | h4
            · exact h3
            · exact absurd h4 hnd1
          · exact absurd h2 hnd2
        have hhi_le : (∏ p ∈ (Finset.Ioc (m + 1) n).filter Nat.Prime, p) ≤ 4 ^ m := by
          have h1 : (∏ p ∈ (Finset.Ioc (m + 1) n).filter Nat.Prime, p) ≤ n.choose m :=
            Nat.le_of_dvd (Nat.choose_pos (by omega)) hhi_dvd
          have hsymm : n.choose (m + 1) = n.choose m := by
            have := Nat.choose_symm (show m ≤ n by omega)
            rw [show n - m = m + 1 by omega] at this
            exact this
          have h2 : n.choose m + n.choose (m + 1) ≤ 2 ^ n := by
            have hsub : ({m, m + 1} : Finset ℕ) ⊆ Finset.range (n + 1) := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range] at hx ⊢
              omega
            calc n.choose m + n.choose (m + 1)
                = ∑ k ∈ ({m, m + 1} : Finset ℕ), n.choose k := by
                    rw [Finset.sum_pair (by omega)]
              _ ≤ ∑ k ∈ Finset.range (n + 1), n.choose k :=
                    Finset.sum_le_sum_of_subset hsub
              _ = 2 ^ n := Nat.sum_range_choose n
          have h2n : 2 ^ n = 2 * 4 ^ m := by
            rw [hn_eq, pow_succ', pow_mul]; norm_num
          omega
        rw [hunion, Finset.prod_union hdisj]
        calc (∏ p ∈ (Finset.Icc 1 (m + 1)).filter Nat.Prime, p) *
              (∏ p ∈ (Finset.Ioc (m + 1) n).filter Nat.Prime, p)
            ≤ 4 ^ (m + 1) * 4 ^ m := Nat.mul_le_mul (ih (m + 1) (by omega)) hhi_le
          _ = 4 ^ n := by rw [← pow_add, show m + 1 + m = n by omega]

private lemma piCount_ge9 {D : ℕ} (hD : 9 ≤ D) : piCount (10 ^ D) < 10 ^ (D - 1) := by
  by_contra hge
  push Not at hge
  set y := 10 ^ (D - 2)
  have hy_le : y ≤ 10 ^ D := Nat.pow_le_pow_right (by decide) (by omega)
  have hpi_y : piCount y ≤ y := by
    unfold piCount
    calc ((Finset.Icc 1 y).filter Nat.Prime).card ≤ (Finset.Icc 1 y).card :=
          Finset.card_filter_le _ _
      _ = y := by simp
  have h10y : 10 ^ (D - 1) = 10 * y := by
    rw [show D - 1 = (D - 2) + 1 by omega, pow_succ']
  have h100y : 10 ^ D = 100 * y := by
    rw [show D = (D - 2) + 2 by omega, pow_add]; ring
  set S := (Finset.Ioc y (10 ^ D)).filter Nat.Prime
  have hScard : S.card = piCount (10 ^ D) - piCount y := piCount_Ioc_eq_sub hy_le
  have h9y : 9 * y ≤ S.card := by omega
  have hsub : S ⊆ (Finset.Icc 1 (10 ^ D)).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc, S] at hp ⊢
    exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
  have hprod : y ^ (9 * y) ≤ 4 ^ (100 * y) := by
    calc y ^ (9 * y) ≤ y ^ S.card := Nat.pow_le_pow_right (Nat.pow_pos (by decide)) h9y
      _ = ∏ _p ∈ S, y := by simp
      _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod' fun p hp =>
            le_of_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
      _ ≤ ∏ p ∈ (Finset.Icc 1 (10 ^ D)).filter Nat.Prime, p :=
            Finset.prod_le_prod_of_subset_of_one_le' hsub fun p hp _ =>
              (Finset.mem_filter.mp hp).2.pos
      _ ≤ 4 ^ (10 ^ D) := prod_primes_le_four_pow (10 ^ D)
      _ = 4 ^ (100 * y) := by rw [h100y]
  have hrew1 : y ^ (9 * y) = (y ^ 9) ^ y := by rw [pow_mul]
  have hrew2 : 4 ^ (100 * y) = (4 ^ 100) ^ y := by rw [pow_mul]
  rw [hrew1, hrew2] at hprod
  have hbase : y ^ 9 ≤ 4 ^ 100 := by
    by_contra hgt
    push Not at hgt
    have hy_pos : 0 < y := Nat.pow_pos (by decide : 0 < 10)
    have := Nat.pow_lt_pow_left (n := y) hgt hy_pos.ne'
    omega
  have hy9 : 10 ^ 63 ≤ y ^ 9 := by
    change 10 ^ 63 ≤ (10 ^ (D - 2)) ^ 9
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide : 0 < 10) (by omega)
  have hcontra : 4 ^ 100 < 10 ^ 63 := by norm_num
  omega

private lemma piCount_lt_ten_pow {D : ℕ} (hD : 5 ≤ D) : piCount (10 ^ D) < 10 ^ (D - 1) := by
  by_cases h9 : 9 ≤ D
  · exact piCount_ge9 h9
  · interval_cases D
    · exact piCount_10e5
    · exact piCount_10e6
    · exact piCount_10e7
    · exact piCount_10e8

/- ### Part 3: Finite check for $D \le 4$ ($1 \le x \le 1229$) -/

private def collectDown : ℕ → List ℕ → List ℕ
  | 0, acc => acc
  | n + 1, acc => collectDown n (if isPrime10007 n then n :: acc else acc)

private lemma collectDown_eq :
    ∀ (k : ℕ) (acc : List ℕ),
      collectDown k acc = (List.range k).filter isPrime10007 ++ acc
  | 0, acc => by simp [collectDown]
  | k + 1, acc => by
    rw [collectDown, collectDown_eq k, List.range_succ, List.filter_append, List.filter_cons,
      List.filter_nil]
    split_ifs <;> simp [List.append_assoc]

private def primesList : List ℕ := collectDown 10008 []

private lemma primesList_eq : primesList = (List.range 10008).filter isPrime10007 := by
  rw [primesList, collectDown_eq, List.append_nil]

private lemma primesList_sorted : primesList.Pairwise (· < ·) := by
  rw [primesList_eq]
  exact List.Pairwise.filter _ List.pairwise_lt_range

private lemma mem_primesList_iff (x : ℕ) : x ∈ primesList ↔ x < 10008 ∧ x.Prime := by
  rw [primesList_eq, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hx, hp⟩
    exact ⟨hx, (isPrime10007_iff (by omega)).mp hp⟩
  · rintro ⟨hx, hp⟩
    exact ⟨hx, (isPrime10007_iff (by omega)).mpr hp⟩

private lemma list_getElem_eq_nth {L : List ℕ} (hsorted : L.Pairwise (· < ·))
    (hmem : ∀ x, x ∈ L ↔ x < 10008 ∧ x.Prime) (i : ℕ) (hi : i < L.length) :
    L[i] = Nat.nth Nat.Prime i := by
  set p := L[i]
  have hp_mem : p ∈ L := List.getElem_mem hi
  have hp_lt : p < 10008 := ((hmem p).mp hp_mem).1
  have hp_pr : p.Prime := ((hmem p).mp hp_mem).2
  have hmono : ∀ a b : ℕ, (ha : a < L.length) → (hb : b < L.length) →
      a < b → L[a] < L[b] := fun a b ha hb hab =>
    List.pairwise_iff_getElem.mp hsorted a b ha hb hab
  have hcount : Nat.count Nat.Prime p = i := by
    rw [Nat.count_eq_card_filter_range]
    have hbij : (Finset.range i).card = ((Finset.range p).filter Nat.Prime).card := by
      refine Finset.card_bij (fun j hj => L[j]'(lt_trans (Finset.mem_range.mp hj) hi))
        ?_ ?_ ?_
      · intro j hj
        have hji : j < i := Finset.mem_range.mp hj
        have hjlen : j < L.length := lt_trans hji hi
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (hmono j i hjlen hi hji),
            ((hmem _).mp (List.getElem_mem hjlen)).2⟩
      · intro a ha b hb hab
        have halen : a < L.length := lt_trans (Finset.mem_range.mp ha) hi
        have hblen : b < L.length := lt_trans (Finset.mem_range.mp hb) hi
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact absurd hab (ne_of_lt (hmono a b halen hblen hlt))
        · exact absurd hab.symm (ne_of_lt (hmono b a hblen halen hgt))
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_range] at hq
        have hqmem : q ∈ L := (hmem q).mpr ⟨by omega, hq.2⟩
        obtain ⟨j, hjlen, hjeq⟩ := List.getElem_of_mem hqmem
        have hji : j < i := by
          by_contra hge
          rcases eq_or_lt_of_le (not_lt.mp hge) with rfl | hlt
          · omega
          · have := hmono i j hi hjlen hlt
            omega
        exact ⟨j, Finset.mem_range.mpr hji, hjeq⟩
    rw [← hbij, Finset.card_range]
  rw [← hcount]
  exact (Nat.nth_count hp_pr).symm

private lemma primesList_getElem_eq_nth (i : ℕ) (hi : i < primesList.length) :
    primesList[i] = Nat.nth Nat.Prime i :=
  list_getElem_eq_nth primesList_sorted mem_primesList_iff i hi

private inductive NatTree
  | leaf : NatTree
  | node : ℕ → NatTree → NatTree → NatTree

private def buildTreeAux : ℕ → ℕ → List ℕ → NatTree × List ℕ
  | 0, _, xs => (.leaf, xs)
  | _, 0, xs => (.leaf, xs)
  | fuel + 1, n + 1, xs =>
    let leftSize := n / 2
    let rightSize := n - leftSize
    let (l, xs1) := buildTreeAux fuel leftSize xs
    match xs1 with
    | [] => (.leaf, [])
    | v :: xs2 =>
      let (r, xs3) := buildTreeAux fuel rightSize xs2
      (.node v l r, xs3)

private def treeGet : NatTree → ℕ → ℕ → ℕ
  | .leaf, _, _ => 0
  | .node v l r, sz, i =>
    match sz with
    | 0 => 0
    | n + 1 =>
      let leftSize := n / 2
      if i < leftSize then treeGet l leftSize i
      else if i == leftSize then v
      else treeGet r (n - leftSize) (i - leftSize - 1)

private lemma buildTreeAux_spec :
    ∀ (fuel sz : ℕ) (xs : List ℕ) (_ : sz ≤ fuel) (hsl : sz ≤ xs.length),
      (buildTreeAux fuel sz xs).2 = xs.drop sz ∧
      ∀ i : ℕ, (hi : i < sz) → treeGet (buildTreeAux fuel sz xs).1 sz i = xs[i]'(lt_of_lt_of_le hi hsl)
  | 0, sz, xs, hsf, _ => by
    have hsz : sz = 0 := by omega
    subst hsz
    exact ⟨by simp [buildTreeAux], fun i hi => by omega⟩
  | fuel + 1, 0, xs, _, _ => ⟨by simp [buildTreeAux], fun i hi => by omega⟩
  | fuel + 1, n + 1, xs, hsf, hsl => by
    set leftSize := n / 2
    set rightSize := n - leftSize
    have hl_le : leftSize ≤ fuel := by omega
    have hr_le : rightSize ≤ fuel := by omega
    have hl_len : leftSize ≤ xs.length := by omega
    have ihL := buildTreeAux_spec fuel leftSize xs hl_le hl_len
    set resL := buildTreeAux fuel leftSize xs
    have hdropL : resL.2 = xs.drop leftSize := ihL.1
    have hdropL_ne : resL.2 ≠ [] := by
      rw [hdropL]
      intro hnil
      have := congrArg List.length hnil
      simp only [List.length_drop, List.length_nil] at this
      omega
    obtain ⟨v, xs2, hxs1⟩ : ∃ v xs2, resL.2 = v :: xs2 := List.exists_cons_of_ne_nil hdropL_ne
    have hv_eq : v = xs[leftSize]'(by omega) := by
      have h1 : (v :: xs2)[0] = (xs.drop leftSize)[0]'(by simp; omega) := by
        simp only [← hxs1, hdropL]
      simpa using h1
    have hxs2_eq : xs2 = xs.drop (leftSize + 1) := by
      have := congrArg List.tail hxs1
      simp only [List.tail_cons] at this
      rw [← this, hdropL, List.tail_drop]
    have hr_len : rightSize ≤ xs2.length := by
      rw [hxs2_eq, List.length_drop]
      omega
    have ihR := buildTreeAux_spec fuel rightSize xs2 hr_le hr_len
    have hunfold : buildTreeAux (fuel + 1) (n + 1) xs =
        (.node v resL.1 (buildTreeAux fuel rightSize xs2).1,
          (buildTreeAux fuel rightSize xs2).2) := by
      conv_lhs => unfold buildTreeAux
      dsimp only
      change (match resL.2 with
        | [] => (NatTree.leaf, [])
        | v :: xs2 =>
          let x := buildTreeAux fuel rightSize xs2
          (NatTree.node v resL.1 x.1, x.2)) = _
      rw [hxs1]
    rw [hunfold]
    constructor
    · dsimp only
      rw [ihR.1, hxs2_eq, List.drop_drop, show leftSize + 1 + rightSize = n + 1 by omega]
    · intro i hi
      dsimp only [treeGet]
      split_ifs with hlt heq
      · exact ihL.2 i hlt
      · have hieq : i = leftSize := beq_iff_eq.mp heq
        subst hieq
        exact hv_eq
      · have hgt : leftSize < i := by
          have hne : i ≠ leftSize := fun h => heq (beq_iff_eq.mpr h)
          omega
        have hiR : i - leftSize - 1 < rightSize := by omega
        rw [ihR.2 (i - leftSize - 1) hiR]
        simp only [hxs2_eq, List.getElem_drop]
        congr 1
        omega

private def primesTree : NatTree := (buildTreeAux 1230 1230 primesList).1

private lemma primesTree_eq : primesTree = (buildTreeAux 1230 1230 primesList).1 := rfl

private def revFastAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | fuel + 1, k, acc => if k = 0 then acc else revFastAux fuel (k / 10) (acc * 10 + k % 10)

private def revFast (k : ℕ) : ℕ := revFastAux 5 k 0

private lemma revFastAux_eq :
    ∀ (fuel k acc : ℕ), k < 10 ^ fuel →
      revFastAux fuel k acc =
        acc * 10 ^ (Nat.digits 10 k).length + Nat.ofDigits 10 (Nat.digits 10 k).reverse
  | 0, k, acc, hk => by
    have hk0 : k = 0 := by omega
    subst hk0
    simp [revFastAux]
  | fuel + 1, k, acc, hk => by
    unfold revFastAux
    split_ifs with hk0
    · subst hk0; simp
    · have hkdiv : k / 10 < 10 ^ fuel := by
        rw [Nat.div_lt_iff_lt_mul (by decide), ← pow_succ]
        exact hk
      rw [revFastAux_eq fuel (k / 10) (acc * 10 + k % 10) hkdiv]
      rw [Nat.digits_def' (by decide) (Nat.pos_of_ne_zero hk0)]
      simp only [List.length_cons, List.reverse_cons, Nat.ofDigits_append,
        Nat.ofDigits_singleton, List.length_reverse]
      rw [pow_succ]
      ring

private lemma revFast_eq {k : ℕ} (hk : k < 10000) :
    revFast k = OeisA100475.reverseDigits k := by
  unfold revFast OeisA100475.reverseDigits
  rw [revFastAux_eq 5 k 0 (by omega)]
  simp

private def stepFast (t : NatTree) (k : ℕ) : ℕ :=
  revFast (treeGet t 1230 (k - 1))

private def escapesIn (t : NatTree) : ℕ → ℕ → Bool
  | 0, k => decide (1230 ≤ k)
  | fuel + 1, k => decide (1230 ≤ k) || escapesIn t fuel (stepFast t k)

private def allEscape (t : NatTree) : ℕ → Bool
  | 0 => true
  | k + 1 => escapesIn t 10 (k + 1) && allEscape t k

private def checkAllFor (L : List ℕ) : Bool :=
  let t := (buildTreeAux 1230 1230 L).1
  (L.length == 1230) &&
  (treeGet t 1230 1228 == 9973) &&
  (treeGet t 1230 1229 == 10007) &&
  allEscape t 1229

private lemma checkAllFor_sound (L : List ℕ) (h : checkAllFor L = true) :
    L.length = 1230 ∧
    treeGet (buildTreeAux 1230 1230 L).1 1230 1228 = 9973 ∧
    treeGet (buildTreeAux 1230 1230 L).1 1230 1229 = 10007 ∧
    allEscape (buildTreeAux 1230 1230 L).1 1229 = true := by
  simp only [checkAllFor, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

private lemma checkAllFor_primesList : checkAllFor primesList = true := by decide +kernel

private lemma primesList_len : primesList.length = 1230 :=
  (checkAllFor_sound primesList checkAllFor_primesList).1

private lemma treeGet_primesTree (i : ℕ) (hi : i < 1230) :
    treeGet primesTree 1230 i = Nat.nth Nat.Prime i := by
  have hspec := buildTreeAux_spec 1230 1230 primesList le_rfl (by rw [primesList_len])
  have h1 := hspec.2 i hi
  rw [primesTree_eq, h1]
  exact primesList_getElem_eq_nth i (by rw [primesList_len]; exact hi)

private lemma nth_prime_1228 : Nat.nth Nat.Prime 1228 = 9973 := by
  rw [← treeGet_primesTree 1228 (by decide), primesTree_eq]
  exact (checkAllFor_sound primesList checkAllFor_primesList).2.1

private lemma nth_prime_1229 : Nat.nth Nat.Prime 1229 = 10007 := by
  rw [← treeGet_primesTree 1229 (by decide), primesTree_eq]
  exact (checkAllFor_sound primesList checkAllFor_primesList).2.2.1

private lemma allEscape_1229 : allEscape primesTree 1229 = true := by
  rw [primesTree_eq]
  exact (checkAllFor_sound primesList checkAllFor_primesList).2.2.2

private lemma allEscape_sound :
    ∀ (n : ℕ), allEscape primesTree n = true → ∀ x : ℕ, 1 ≤ x → x ≤ n →
      escapesIn primesTree 10 x = true
  | 0, _, x, h1, h2 => by omega
  | k + 1, h, x, h1, h2 => by
    simp only [allEscape, Bool.and_eq_true] at h
    by_cases hxk : x = k + 1
    · subst hxk; exact h.1
    · exact allEscape_sound k h.2 x h1 (by omega)

private lemma aStartAt_add (x m n : ℕ) :
    OeisA100475.aStartAt x (m + n) = OeisA100475.aStartAt (OeisA100475.aStartAt x m) n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc]
    simp only [OeisA100475.aStartAt, ih]

private lemma prime_lt_10000_of_lt_1229 {i : ℕ} (hi : i < 1229) :
    Nat.nth Nat.Prime i < 10000 := by
  have h1228 : Nat.nth Nat.Prime 1228 = 9973 := nth_prime_1228
  have hle : Nat.nth Nat.Prime i ≤ Nat.nth Nat.Prime 1228 :=
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (by omega)
  omega

private lemma reverseDigits_prime_digits {p : ℕ} (hp : p.Prime) :
    Nat.digits 10 (OeisA100475.reverseDigits p) = (Nat.digits 10 p).reverse := by
  have h10 : p % 10 ≠ 0 := by
    intro hmod
    have hdvd : 10 ∣ p := Nat.dvd_of_mod_eq_zero hmod
    have h2dvd : 2 ∣ p := dvd_trans (by decide : 2 ∣ 10) hdvd
    have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2dvd).symm
    omega
  unfold OeisA100475.reverseDigits
  apply Nat.digits_ofDigits 10 (by decide)
  · intro d hd
    rw [List.mem_reverse] at hd
    exact Nat.digits_lt_base (by decide) hd
  · intro _
    rw [List.getLast_reverse]
    have hdef := Nat.digits_def' (by decide : 1 < 10) hp.pos
    simp only [hdef, List.head_cons]
    exact h10

private lemma aStartAt_pos {x : ℕ} (hx : 0 < x) : ∀ n : ℕ, 0 < OeisA100475.aStartAt x n := by
  intro n
  induction n with
  | zero => exact hx
  | succ k ih =>
    unfold OeisA100475.aStartAt
    have hk0 : OeisA100475.aStartAt x k ≠ 0 := ih.ne'
    simp only [hk0, ↓reduceIte]
    set p := Nat.nth Nat.Prime (OeisA100475.aStartAt x k - 1)
    have hp : p.Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
    have hdig := reverseDigits_prime_digits hp
    by_contra h0
    have hrev0 : OeisA100475.reverseDigits p = 0 := by omega
    rw [hrev0, Nat.digits_zero] at hdig
    have hnil : Nat.digits 10 p = [] := List.reverse_eq_nil_iff.mp hdig.symm
    exact Nat.digits_ne_nil_iff_ne_zero.mpr hp.ne_zero hnil

private lemma escapesIn_sound :
    ∀ (fuel x : ℕ), 1 ≤ x → escapesIn primesTree fuel x = true →
      ∃ s : ℕ, 1230 ≤ OeisA100475.aStartAt x s
  | 0, x, _, h => by
    simp only [escapesIn, decide_eq_true_eq] at h
    exact ⟨0, h⟩
  | fuel + 1, x, hx1, h => by
    simp only [escapesIn, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with hge | hrec
    · exact ⟨0, hge⟩
    · by_cases hge : 1230 ≤ x
      · exact ⟨0, hge⟩
      · have hxlt : x - 1 < 1229 := by omega
        have hstep : stepFast primesTree x = OeisA100475.aStartAt x 1 := by
          have hx0 : x ≠ 0 := by omega
          simp only [stepFast, OeisA100475.aStartAt, hx0, ↓reduceIte]
          rw [treeGet_primesTree (x - 1) (by omega),
            revFast_eq (prime_lt_10000_of_lt_1229 hxlt)]
        have hpos1 : 1 ≤ stepFast primesTree x := by
          rw [hstep]
          exact aStartAt_pos hx1 1
        obtain ⟨s, hs⟩ := escapesIn_sound fuel (stepFast primesTree x) hpos1 hrec
        rw [hstep, ← aStartAt_add] at hs
        exact ⟨1 + s, hs⟩

/- ### Part 4: Digit-count monotonicity and main disproof -/

private lemma nth_prime_ge_add_two (n : ℕ) : n + 2 ≤ Nat.nth Nat.Prime n := by
  induction n with
  | zero => rw [Nat.nth_prime_zero_eq_two]
  | succ k ih =>
    have hlt : Nat.nth Nat.Prime k < Nat.nth Nat.Prime (k + 1) :=
      Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self k)
    omega

private lemma digits_len_mono {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    (Nat.digits 10 a).length ≤ (Nat.digits 10 b).length := by
  rw [Nat.length_digits 10 a (by decide) ha.ne', Nat.length_digits 10 b (by decide) (by omega)]
  exact Nat.add_le_add_right (Nat.log_mono_right hab) 1

private lemma aStartAt_digits_mono {x : ℕ} (hx : 0 < x) :
    Monotone (fun n => (Nat.digits 10 (OeisA100475.aStartAt x n)).length) := by
  apply monotone_nat_of_le_succ
  intro n
  have hpos := aStartAt_pos hx n
  have hstep : OeisA100475.aStartAt x (n + 1) =
      OeisA100475.reverseDigits (Nat.nth Nat.Prime (OeisA100475.aStartAt x n - 1)) := by
    simp only [OeisA100475.aStartAt, hpos.ne', ↓reduceIte]
  rw [hstep]
  set p := Nat.nth Nat.Prime (OeisA100475.aStartAt x n - 1)
  have hp : p.Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
  rw [reverseDigits_prime_digits hp, List.length_reverse]
  have hle : OeisA100475.aStartAt x n ≤ p := by
    have := nth_prime_ge_add_two (OeisA100475.aStartAt x n - 1)
    omega
  exact digits_len_mono hpos hle

private lemma le_piCount_of_nth_prime_le {y N : ℕ} (hy : 1 ≤ y)
    (hle : Nat.nth Nat.Prime (y - 1) ≤ N) : y ≤ piCount N := by
  unfold piCount
  have hcard : (Finset.range y).card ≤ ((Finset.Icc 1 N).filter Nat.Prime).card := by
    refine Finset.card_le_card_of_injOn (Nat.nth Nat.Prime) ?_ ?_
    · intro i hi
      simp only [Finset.coe_range, Set.mem_Iio] at hi
      have hpr : (Nat.nth Nat.Prime i).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i
      have hmono : Nat.nth Nat.Prime i ≤ Nat.nth Nat.Prime (y - 1) :=
        (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (by omega)
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Icc]
      exact ⟨⟨hpr.pos, le_trans hmono hle⟩, hpr⟩
    · intro a _ b _ hab
      exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hab
  simpa using hcard

end OeisA100475Disproof

theorem OMA.disproof : ¬ (type_of% @OeisA100475.conjecture) := by
  rintro ⟨x, hx0, _, N, P, hP, hper⟩
  have hper_mul : ∀ k : ℕ, OeisA100475.aStartAt x (N + k * P) = OeisA100475.aStartAt x N := by
    intro k
    induction k with
    | zero => simp
    | succ m ih =>
      rw [show N + (m + 1) * P = (N + m * P) + P by ring, hper _ (by omega), ih]
  set D := (Nat.digits 10 (OeisA100475.aStartAt x N)).length
  have hconstD : ∀ n : ℕ, N ≤ n → (Nat.digits 10 (OeisA100475.aStartAt x n)).length = D := by
    intro n hn
    have hle1 : D ≤ (Nat.digits 10 (OeisA100475.aStartAt x n)).length :=
      OeisA100475Disproof.aStartAt_digits_mono hx0 hn
    have hnk : n ≤ N + (n - N + 1) * P := by
      have : n - N + 1 ≤ (n - N + 1) * P := Nat.le_mul_of_pos_right _ hP
      omega
    have hle2 : (Nat.digits 10 (OeisA100475.aStartAt x n)).length ≤
        (Nat.digits 10 (OeisA100475.aStartAt x (N + (n - N + 1) * P))).length :=
      OeisA100475Disproof.aStartAt_digits_mono hx0 hnk
    rw [hper_mul] at hle2
    omega
  have hD_pos : 1 ≤ D := by
    have hpos := OeisA100475Disproof.aStartAt_pos hx0 N
    have hne : Nat.digits 10 (OeisA100475.aStartAt x N) ≠ [] :=
      Nat.digits_ne_nil_iff_ne_zero.mpr hpos.ne'
    exact List.length_pos_of_ne_nil hne
  by_cases hD5 : 5 ≤ D
  · set y := OeisA100475.aStartAt x N
    have hy_pos : 0 < y := OeisA100475Disproof.aStartAt_pos hx0 N
    have hy_ge : 10 ^ (D - 1) ≤ y := by
      have hlen : D = Nat.log 10 y + 1 := Nat.length_digits 10 y (by decide) hy_pos.ne'
      rw [show D - 1 = Nat.log 10 y by omega]
      exact Nat.pow_log_le_self 10 hy_pos.ne'
    have hstep_D : (Nat.digits 10 (Nat.nth Nat.Prime (y - 1))).length = D := by
      have hnext := hconstD (N + 1) (by omega)
      have hstep : OeisA100475.aStartAt x (N + 1) =
          OeisA100475.reverseDigits (Nat.nth Nat.Prime (y - 1)) := by
        unfold OeisA100475.aStartAt
        simp [hy_pos.ne', y]
      rw [hstep] at hnext
      have hp : (Nat.nth Nat.Prime (y - 1)).Prime :=
        Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
      rw [OeisA100475Disproof.reverseDigits_prime_digits hp, List.length_reverse] at hnext
      exact hnext
    have hp_lt : Nat.nth Nat.Prime (y - 1) < 10 ^ D := by
      rw [← hstep_D]
      exact Nat.lt_base_pow_length_digits (by decide)
    have hy_le : y ≤ OeisA100475Disproof.piCount (10 ^ D) :=
      OeisA100475Disproof.le_piCount_of_nth_prime_le hy_pos (le_of_lt hp_lt)
    have hpi_lt : OeisA100475Disproof.piCount (10 ^ D) < 10 ^ (D - 1) :=
      OeisA100475Disproof.piCount_lt_ten_pow hD5
    omega
  · have hbound : ∀ n : ℕ, N ≤ n → OeisA100475.aStartAt x n ≤ 1229 := by
      intro n hn
      set y := OeisA100475.aStartAt x n
      have hy_pos : 0 < y := OeisA100475Disproof.aStartAt_pos hx0 n
      have hstep_D : (Nat.digits 10 (Nat.nth Nat.Prime (y - 1))).length = D := by
        have hnext := hconstD (n + 1) (by omega)
        have hstep : OeisA100475.aStartAt x (n + 1) =
            OeisA100475.reverseDigits (Nat.nth Nat.Prime (y - 1)) := by
          unfold OeisA100475.aStartAt
          simp [hy_pos.ne', y]
        rw [hstep] at hnext
        have hp : (Nat.nth Nat.Prime (y - 1)).Prime :=
          Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
        rw [OeisA100475Disproof.reverseDigits_prime_digits hp, List.length_reverse] at hnext
        exact hnext
      have hp_lt : Nat.nth Nat.Prime (y - 1) < 10 ^ 4 := by
        calc Nat.nth Nat.Prime (y - 1) < 10 ^ D := by
              rw [← hstep_D]; exact Nat.lt_base_pow_length_digits (by decide)
          _ ≤ 10 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega)
      have hp_lt_1229 : Nat.nth Nat.Prime (y - 1) < Nat.nth Nat.Prime 1229 := by
        rw [OeisA100475Disproof.nth_prime_1229]
        omega
      have hy_lt : y - 1 < 1229 := by
        by_contra hge
        have hle : Nat.nth Nat.Prime 1229 ≤ Nat.nth Nat.Prime (y - 1) :=
          (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (not_lt.mp hge)
        omega
      omega
    set y0 := OeisA100475.aStartAt x N
    have hy0_pos : 1 ≤ y0 := OeisA100475Disproof.aStartAt_pos hx0 N
    have hy0_le : y0 ≤ 1229 := hbound N le_rfl
    have hesc := OeisA100475Disproof.allEscape_sound 1229 OeisA100475Disproof.allEscape_1229
      y0 hy0_pos hy0_le
    obtain ⟨s, hs⟩ := OeisA100475Disproof.escapesIn_sound 10 y0 hy0_pos hesc
    rw [← OeisA100475Disproof.aStartAt_add] at hs
    have hle := hbound (N + s) (by omega)
    omega
