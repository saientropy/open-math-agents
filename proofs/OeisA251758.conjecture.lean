import FormalConjectures.OEIS.«251758»

/-!
Proof that `Nat.kthPrimorial 12 / Nat.kthPrimorial (Nat.primeCounting' 8) = 35336848261`
is the least `x ≥ 2` satisfying `OeisA251758.a x = 8`.

Strategy:
1. Evaluate the target `X0 = 11 * 13 * 17 * 19 * 23 * 29 * 31 * 37 = 35336848261`.
2. Express `a n` via the divisor-reversal identity `(consecProdSum (divList n) : ℚ) = n^2 * R (divList n)`,
   so `a n = 8` implies `1 / 9 < R (divList n) ≤ 1 / 8`.
3. Prove pointwise and sublist monotonicity of `R` on strictly increasing positive lists.
4. Any prime factor `p ≤ 7` gives `R (divList n) ≥ 1 / p ≥ 1 / 7 > 1 / 8`.
5. Any `2 ≤ n < X0` with all prime factors `≥ 11` has at most 7 distinct prime factors;
   mapping them to `Q7 = [11, 13, 17, 19, 23, 29, 31]` reduces `R (divList n)` to `R U`
   for a `Q7`-smooth list `U`. Splitting `U` at cutoff `150` and bounding the tail by the
   finite `Q7`-smooth Euler product gives `R U < 1 / 9`.
6. Compute `divList X0` as the sorted 256-element subset-product list of `Q8` and verify `a X0 = 8`.
-/

namespace OMAO251758

open Nat List Finset

/-- Target integer `11 * 13 * 17 * 19 * 23 * 29 * 31 * 37`. -/
def X0 : ℕ := 35336848261

/-- The seven smallest primes `≥ 11`. -/
def Q7 : List ℕ := [11, 13, 17, 19, 23, 29, 31]

/-- The eight smallest primes `≥ 11`. -/
def Q8 : List ℕ := [11, 13, 17, 19, 23, 29, 31, 37]

/-- All `Q7`-smooth positive integers `≤ 150`, in strictly increasing order. -/
def P150 : List ℕ := [1, 11, 13, 17, 19, 23, 29, 31, 121, 143]

/-- Sorted list of divisors of `n` as used in `OeisA251758.a`. -/
def divList (n : ℕ) : List ℕ := (List.range (n + 1)).filter (· ∣ n)

/-- Recursive sum of products of consecutive elements of a list. -/
def consecProdSum : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: t => a * b + consecProdSum (b :: t)

/-- Sum of reciprocals of consecutive products in `ℚ`. -/
def R : List ℕ → ℚ
  | [] => 0
  | [_] => 0
  | a :: b :: t => (1 : ℚ) / ((a : ℚ) * (b : ℚ)) + R (b :: t)

/-- Boolean check for strict increasing order on consecutive pairs. -/
def isChainLt : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => decide (a < b) && isChainLt (b :: t)

/-- Subset-product generator for squarefree divisor lists. -/
def genDivs : List ℕ → List ℕ
  | [] => [1]
  | p :: ps =>
    let r := genDivs ps
    r ++ r.map (p * ·)

/-- Explicit sorted list of all 256 divisors of `X0`. -/
def X0Divs : List ℕ := [
  1, 11, 13, 17, 19, 23, 29, 31,
  37, 143, 187, 209, 221, 247, 253, 299,
  319, 323, 341, 377, 391, 403, 407, 437,
  481, 493, 527, 551, 589, 629, 667, 703,
  713, 851, 899, 1073, 1147, 2431, 2717, 3289,
  3553, 4147, 4199, 4301, 4433, 4807, 5083, 5291,
  5423, 5681, 5797, 6061, 6409, 6479, 6851, 6919,
  7163, 7337, 7429, 7657, 7733, 7843, 8177, 8671,
  9139, 9269, 9361, 9367, 9889, 10013, 11063, 11339,
  11687, 11803, 11951, 12121, 12617, 12673, 13547, 13949,
  14467, 14911, 15283, 16169, 17081, 18241, 19499, 20387,
  20677, 21793, 24679, 26381, 33263, 46189, 55913, 62491,
  70499, 75361, 78793, 81719, 84227, 89947, 95381, 96577,
  100529, 101959, 103037, 110143, 121693, 121771, 124729, 128557,
  130169, 131461, 133331, 139403, 147407, 149017, 153439, 155363,
  157573, 159137, 164021, 164749, 168113, 176111, 177859, 187891,
  188071, 198679, 200651, 210197, 214489, 215441, 222053, 224257,
  227447, 230299, 237133, 239723, 253487, 265031, 268801, 271469,
  274873, 283309, 290191, 290377, 320827, 342953, 346579, 351509,
  365893, 370481, 392863, 419543, 432419, 448477, 468901, 501239,
  565471, 631997, 765049, 1062347, 1339481, 1431859, 1621477, 1708993,
  1733303, 1812239, 1937221, 2068781, 2185469, 2312167, 2369851, 2442583,
  2533289, 2608463, 2788357, 2800733, 2915341, 2956811, 2993887, 3023603,
  3116399, 3194147, 3529097, 3573349, 3772483, 3774901, 3812369, 3866599,
  4075291, 4321493, 4505527, 4569617, 4614973, 4756609, 4816253, 4933247,
  5107219, 5157911, 5454059, 5513629, 5830201, 6095713, 6220181, 6516107,
  6678671, 6951967, 7351123, 7971317, 8215961, 8415539, 8521063, 9945637,
  10743949, 13005833, 14535931, 30808063, 32932757, 39306839, 41523911, 49560797,
  50265787, 52978783, 56179409, 59994649, 64132211, 67052843, 71677177, 73465381,
  80862353, 86822723, 87684487, 90375571, 93731693, 103627121, 109402007, 110773819,
  118183439, 139671337, 143064163, 159895241, 169075829, 188967103, 247110827, 955049953,
  1139898331, 1218512009, 1536384707, 1859834119, 2078638133, 2718219097, 3212440751, 35336848261
]

/- ### Part 1: Target primorial ratio equals `X0` -/

lemma primeCounting'_8 : Nat.primeCounting' 8 = 4 := by
  simp only [Nat.primeCounting', Nat.count_succ, Nat.count_zero]
  decide

lemma target_eq_X0 :
    Nat.kthPrimorial 12 / Nat.kthPrimorial (Nat.primeCounting' 8) = X0 := by
  rw [primeCounting'_8]
  have h12 : Nat.kthPrimorial 12 = 210 * X0 := by
    simp only [Nat.kthPrimorial_succ,
      Nat.nth_prime_four_eq_eleven, Nat.nth_prime_five_eq_thirteen,
      Nat.nth_prime_six_eq_seventeen, Nat.nth_prime_seven_eq_nineteen,
      Nat.nth_prime_eight_eq_twentyThree, Nat.nth_prime_nine_eq_twentyNine,
      Nat.nth_prime_ten_eq_thirtyOne, Nat.nth_prime_eleven_eq_thirtySeven, X0]
    norm_num
  rw [h12, Nat.kthPrimorial_four]
  exact Nat.mul_div_right X0 (by decide)

/- ### Part 2: `consecProdSum`, strictly increasing lists, and `a X0 = 8` -/

lemma zip_tail_sum_eq_consecProdSum : ∀ L : List ℕ,
    ((L.zip L.tail).map (fun p : ℕ × ℕ => p.fst * p.snd)).sum = consecProdSum L
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
    simp only [List.tail_cons, List.zip_cons_cons, List.map_cons, List.sum_cons, consecProdSum]
    congr 1
    exact zip_tail_sum_eq_consecProdSum (b :: t)

lemma a_eq (n : ℕ) :
    OeisA251758.a n =
      if consecProdSum (divList n) = 0 then 0 else n ^ 2 / consecProdSum (divList n) := by
  unfold OeisA251758.a
  dsimp only
  rw [← divList, zip_tail_sum_eq_consecProdSum]

lemma pairwise_lt_of_isChainLt : ∀ {L : List ℕ}, isChainLt L = true → L.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: t, h => by
    simp only [isChainLt, Bool.and_eq_true, decide_eq_true_eq] at h
    have hbt := pairwise_lt_of_isChainLt h.2
    refine List.Pairwise.cons ?_ hbt
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hxt
    · exact h.1
    · exact lt_trans h.1 ((List.pairwise_cons.mp hbt).1 x hxt)

lemma eq_of_pairwise_lt : ∀ {L1 L2 : List ℕ},
    L1.Pairwise (· < ·) → L2.Pairwise (· < ·) → (∀ x, x ∈ L1 ↔ x ∈ L2) → L1 = L2
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, hmem => absurd ((hmem b).mpr List.mem_cons_self) List.not_mem_nil
  | a :: _, [], _, _, hmem => absurd ((hmem a).mp List.mem_cons_self) List.not_mem_nil
  | a :: t1, b :: t2, h1, h2, hmem => by
    rw [List.pairwise_cons] at h1 h2
    have hab : a = b := by
      have ha2 : a ∈ b :: t2 := (hmem a).mp List.mem_cons_self
      have hb1 : b ∈ a :: t1 := (hmem b).mpr List.mem_cons_self
      simp only [List.mem_cons] at ha2 hb1
      have hba : b ≤ a := ha2.elim (fun h => le_of_eq h.symm) (fun h => le_of_lt (h2.1 a h))
      have hab' : a ≤ b := hb1.elim (fun h => le_of_eq h.symm) (fun h => le_of_lt (h1.1 b h))
      omega
    subst hab
    congr 1
    apply eq_of_pairwise_lt h1.2 h2.2
    intro x
    have hx_ne1 : x ∈ t1 → x ≠ a := fun hx h => Nat.lt_irrefl a (h ▸ h1.1 x hx)
    have hx_ne2 : x ∈ t2 → x ≠ a := fun hx h => Nat.lt_irrefl a (h ▸ h2.1 x hx)
    constructor
    · intro hx
      have := (hmem x).mp (List.mem_cons_of_mem a hx)
      exact (List.mem_cons.mp this).resolve_left (hx_ne1 hx)
    · intro hx
      have := (hmem x).mpr (List.mem_cons_of_mem a hx)
      exact (List.mem_cons.mp this).resolve_left (hx_ne2 hx)

lemma divList_pairwise_lt (n : ℕ) : (divList n).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

lemma mem_divList {n d : ℕ} (hn : 0 < n) : d ∈ divList n ↔ d ∣ n := by
  simp only [divList, List.mem_filter, List.mem_range, decide_eq_true_eq, and_iff_right_iff_imp]
  intro hd
  exact Nat.lt_succ_of_le (Nat.le_of_dvd hn hd)

lemma coprime_list_prod {p : ℕ} : ∀ {L : List ℕ},
    (∀ q ∈ L, Nat.Coprime p q) → Nat.Coprime p L.prod
  | [], _ => Nat.coprime_one_right p
  | q :: t, h => by
    rw [List.prod_cons]
    exact (h q List.mem_cons_self).mul_right
      (coprime_list_prod fun r hr => h r (List.mem_cons_of_mem q hr))

lemma mem_genDivs_iff : ∀ {ps : List ℕ},
    (∀ p ∈ ps, p.Prime) → ps.Nodup → ∀ d, d ∈ genDivs ps ↔ d ∣ ps.prod
  | [], _, _, d => by
    simp only [genDivs, List.mem_singleton, List.prod_nil, Nat.dvd_one]
  | p :: ps, hprime, hnodup, d => by
    rw [List.nodup_cons] at hnodup
    have hp : p.Prime := hprime p List.mem_cons_self
    have hps_prime : ∀ q ∈ ps, q.Prime := fun q hq => hprime q (List.mem_cons_of_mem p hq)
    have ih := mem_genDivs_iff hps_prime hnodup.2
    have hcop : Nat.Coprime p ps.prod := by
      refine coprime_list_prod fun q hq => ?_
      have hqp : q.Prime := hps_prime q hq
      have hne : p ≠ q := fun h => hnodup.1 (h ▸ hq)
      exact (Nat.coprime_primes hp hqp).mpr hne
    simp only [genDivs, List.mem_append, List.mem_map, List.prod_cons]
    constructor
    · rintro (hd | ⟨d', hd', rfl⟩)
      · exact dvd_mul_of_dvd_right ((ih d).mp hd) p
      · exact Nat.mul_dvd_mul_left p ((ih d').mp hd')
    · intro hd
      by_cases hpd : p ∣ d
      · right
        rcases hpd with ⟨d', rfl⟩
        exact ⟨d', (ih d').mpr ((Nat.mul_dvd_mul_iff_left hp.pos).mp hd), rfl⟩
      · left
        have hcp : Nat.Coprime d p := (hp.coprime_iff_not_dvd.mpr hpd).symm
        exact (ih d).mpr (hcp.dvd_of_dvd_mul_left hd)

lemma length_genDivs : ∀ ps : List ℕ, (genDivs ps).length = 2 ^ ps.length
  | [] => rfl
  | _ :: ps => by
    simp only [genDivs, List.length_append, List.length_map, List.length_cons, pow_succ, mul_two]
    rw [length_genDivs ps]

set_option maxRecDepth 4096 in
lemma X0Divs_eq_divList : divList X0 = X0Divs := by
  have hQ8_prime : ∀ p ∈ Q8, p.Prime := by decide +kernel
  have hQ8_nodup : Q8.Nodup := by decide +kernel
  have hQ8_prod : Q8.prod = X0 := by decide +kernel
  have hchain : isChainLt X0Divs = true := by decide +kernel
  have hX0pw : X0Divs.Pairwise (· < ·) := pairwise_lt_of_isChainLt hchain
  have hdvd_all : X0Divs.all (fun d => X0 % d == 0) = true := by decide +kernel
  have hsub : X0Divs.toFinset ⊆ (genDivs Q8).toFinset := by
    intro d hd
    rw [List.mem_toFinset] at hd ⊢
    have hdX0 : d ∣ X0 := by
      have hmod := (List.all_eq_true.mp hdvd_all) d hd
      exact Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp hmod)
    exact (mem_genDivs_iff hQ8_prime hQ8_nodup d).mpr (hQ8_prod.symm ▸ hdX0)
  have hcard_ge : (genDivs Q8).toFinset.card ≤ X0Divs.toFinset.card := by
    rw [List.toFinset_card_of_nodup hX0pw.nodup]
    have h1 : (genDivs Q8).toFinset.card ≤ (genDivs Q8).length := List.toFinset_card_le _
    have h2 : (genDivs Q8).length = 256 := by rw [length_genDivs]; decide +kernel
    have h3 : X0Divs.length = 256 := by decide +kernel
    omega
  have hfeq : X0Divs.toFinset = (genDivs Q8).toFinset :=
    Finset.eq_of_subset_of_card_le hsub hcard_ge
  apply eq_of_pairwise_lt (divList_pairwise_lt X0) hX0pw
  intro d
  rw [mem_divList (by decide : 0 < X0), ← hQ8_prod, ← mem_genDivs_iff hQ8_prime hQ8_nodup]
  have := Finset.ext_iff.mp hfeq d
  simpa [List.mem_toFinset] using this.symm

set_option maxRecDepth 4096 in
lemma a_X0_eq_8 : OeisA251758.a X0 = 8 := by
  rw [a_eq, X0Divs_eq_divList]
  have hs : consecProdSum X0Divs = 139494930817713648343 := by decide +kernel
  rw [hs]
  decide +kernel

/- ### Part 3: Divisor-reversal identity `consecProdSum (divList n) = n^2 * R (divList n)` -/

lemma consecProdSum_append_cons (L : List ℕ) (a b : ℕ) (t : List ℕ) :
    consecProdSum ((L ++ [a]) ++ (b :: t)) =
      consecProdSum (L ++ [a]) + a * b + consecProdSum (b :: t) := by
  induction L with
  | nil => simp [consecProdSum]
  | cons x xs ih =>
    cases xs with
    | nil => simp [consecProdSum, add_assoc]
    | cons y ys =>
      simp only [List.cons_append, consecProdSum]
      have h := ih
      simp only [List.cons_append] at h
      omega

lemma consecProdSum_append_singleton (L : List ℕ) (a b : ℕ) :
    consecProdSum (L ++ [a, b]) = consecProdSum (L ++ [a]) + a * b := by
  have h := consecProdSum_append_cons L a b []
  simp only [List.append_assoc, List.singleton_append, consecProdSum, add_zero] at h
  exact h

lemma consecProdSum_reverse : ∀ L : List ℕ, consecProdSum L.reverse = consecProdSum L
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
    have ih := consecProdSum_reverse (b :: t)
    simp only [List.reverse_cons, consecProdSum]
    rw [List.append_assoc]
    change consecProdSum (t.reverse ++ [b, a]) = a * b + consecProdSum (b :: t)
    rw [consecProdSum_append_singleton, ← List.reverse_cons, ih, mul_comm, add_comm]

lemma consecProdSum_map_div (n : ℕ) : ∀ L : List ℕ,
    (∀ d ∈ L, d ∣ n ∧ 0 < d) →
    (consecProdSum (L.map (n / ·)) : ℚ) = (n : ℚ) ^ 2 * R L
  | [], _ => by simp [consecProdSum, R]
  | [_], _ => by simp [consecProdSum, R]
  | a :: b :: t, h => by
    have ha := h a List.mem_cons_self
    have hb := h b (List.mem_cons_of_mem a List.mem_cons_self)
    have ht : ∀ d ∈ b :: t, d ∣ n ∧ 0 < d := fun d hd => h d (List.mem_cons_of_mem a hd)
    have ih := consecProdSum_map_div n (b :: t) ht
    simp only [List.map_cons] at ih
    simp only [List.map_cons, consecProdSum, R, Nat.cast_add, Nat.cast_mul, mul_add]
    rw [ih]
    congr 1
    have ha0 : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt ha.2)
    have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hb.2)
    rw [Nat.cast_div ha.1 ha0, Nat.cast_div hb.1 hb0]
    field_simp

lemma divList_reverse_map_div {n : ℕ} (hn : 0 < n) :
    (divList n).reverse.map (n / ·) = divList n := by
  have h1 : ((divList n).reverse.map (n / ·)).Pairwise (· < ·) := by
    rw [List.pairwise_map, List.pairwise_reverse]
    refine (divList_pairwise_lt n).imp_of_mem ?_
    intro a b ha hb hab
    have had : a ∣ n := (mem_divList hn).mp ha
    have hbd : b ∣ n := (mem_divList hn).mp hb
    have ha0 : 0 < a := Nat.pos_of_dvd_of_pos had hn
    have hb0 : 0 < b := Nat.pos_of_dvd_of_pos hbd hn
    rcases had with ⟨ka, hka⟩
    rcases hbd with ⟨kb, hkb⟩
    have hda : n / a = ka := by rw [hka, Nat.mul_div_cancel_left _ ha0]
    have hdb : n / b = kb := by rw [hkb, Nat.mul_div_cancel_left _ hb0]
    rw [hda, hdb]
    have hmul : a * ka = b * kb := hka.symm.trans hkb
    have hkb0 : 0 < kb := Nat.pos_of_mul_pos_left (hkb ▸ hn)
    nlinarith
  apply eq_of_pairwise_lt h1 (divList_pairwise_lt n)
  intro d
  rw [List.mem_map, mem_divList hn]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [List.mem_reverse, mem_divList hn] at hx
    exact Nat.div_dvd_of_dvd hx
  · intro hd
    refine ⟨n / d, ?_, Nat.div_div_self hd (Nat.ne_of_gt hn)⟩
    rw [List.mem_reverse, mem_divList hn]
    exact Nat.div_dvd_of_dvd hd

lemma consecProdSum_divList_eq_R {n : ℕ} (hn : 0 < n) :
    (consecProdSum (divList n) : ℚ) = (n : ℚ) ^ 2 * R (divList n) := by
  have hmem : ∀ d ∈ divList n, d ∣ n ∧ 0 < d := fun d hd => by
    have h := (mem_divList hn).mp hd
    exact ⟨h, Nat.pos_of_dvd_of_pos h hn⟩
  have hrev := divList_reverse_map_div hn
  have h1 : consecProdSum (divList n) = consecProdSum ((divList n).map (n / ·)) := by
    conv_lhs => rw [← hrev]
    rw [List.map_reverse, consecProdSum_reverse]
  rw [h1]
  exact consecProdSum_map_div n (divList n) hmem

lemma R_bounds_of_a_eq_8 {n : ℕ} (hn : 2 ≤ n) (ha : OeisA251758.a n = 8) :
    (1 : ℚ) / 9 < R (divList n) ∧ R (divList n) ≤ (1 : ℚ) / 8 := by
  rw [a_eq] at ha
  have hs0 : consecProdSum (divList n) ≠ 0 := by
    intro h0; rw [if_pos h0] at ha; omega
  rw [if_neg hs0] at ha
  have hs_pos : 0 < consecProdSum (divList n) := Nat.pos_of_ne_zero hs0
  have hlo : 8 * consecProdSum (divList n) ≤ n ^ 2 := by
    have := Nat.div_mul_le_self (n ^ 2) (consecProdSum (divList n))
    rw [ha] at this; exact this
  have hhi : n ^ 2 < 9 * consecProdSum (divList n) := by
    have := Nat.lt_mul_div_succ (n ^ 2) hs_pos
    rw [ha] at this; linarith
  have hloQ : (8 : ℚ) * (consecProdSum (divList n) : ℚ) ≤ (n : ℚ) ^ 2 := by exact_mod_cast hlo
  have hhiQ : (n : ℚ) ^ 2 < (9 : ℚ) * (consecProdSum (divList n) : ℚ) := by exact_mod_cast hhi
  rw [consecProdSum_divList_eq_R (by omega)] at hloQ hhiQ
  have hn2 : (0 : ℚ) < (n : ℚ) ^ 2 := by positivity
  constructor <;> nlinarith

/- ### Part 4: Pointwise and sublist monotonicity of `R` -/

lemma R_nonneg : ∀ L : List ℕ, 0 ≤ R L
  | [] => le_refl 0
  | [_] => le_refl 0
  | a :: b :: t => by
    simp only [R]
    exact add_nonneg (by positivity) (R_nonneg (b :: t))

lemma R_le_cons (a : ℕ) : ∀ L : List ℕ, R L ≤ R (a :: L)
  | [] => le_refl 0
  | b :: t => by
    simp only [R]
    have : (0 : ℚ) ≤ 1 / ((a : ℚ) * (b : ℚ)) := by positivity
    linarith

lemma R_pointwise_le : ∀ {L1 L2 : List ℕ},
    L1.length = L2.length →
    (∀ i (h1 : i < L1.length), 0 < L1[i]) →
    (∀ i (h1 : i < L1.length) (h2 : i < L2.length), L1[i] ≤ L2[i]) →
    R L2 ≤ R L1
  | [], [], _, _, _ => le_refl 0
  | [_], [_], _, _, _ => le_refl 0
  | a1 :: b1 :: t1, a2 :: b2 :: t2, hlen, hpos, hle => by
    simp only [R]
    have ha1 : (0 : ℚ) < a1 := by exact_mod_cast hpos 0 (by simp)
    have hb1 : (0 : ℚ) < b1 := by exact_mod_cast hpos 1 (by simp)
    have ha : (a1 : ℚ) ≤ a2 := by exact_mod_cast hle 0 (by simp) (by simp)
    have hb : (b1 : ℚ) ≤ b2 := by exact_mod_cast hle 1 (by simp) (by simp)
    have hterm : (1 : ℚ) / ((a2 : ℚ) * (b2 : ℚ)) ≤ 1 / ((a1 : ℚ) * (b1 : ℚ)) :=
      one_div_le_one_div_of_le (mul_pos ha1 hb1) (mul_le_mul ha hb (le_of_lt hb1) (by linarith))
    have htail : R (b2 :: t2) ≤ R (b1 :: t1) := by
      apply R_pointwise_le (by simp at hlen; simpa using hlen)
      · intro i hi
        exact hpos (i + 1) (by simpa using Nat.succ_lt_succ hi)
      · intro i h1 h2
        exact hle (i + 1) (by simpa using Nat.succ_lt_succ h1) (by simpa using Nat.succ_lt_succ h2)
    linarith

lemma inv_pair_insert {a b c : ℕ} (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    (1 : ℚ) / ((a : ℚ) * (c : ℚ)) ≤
      1 / ((a : ℚ) * (b : ℚ)) + 1 / ((b : ℚ) * (c : ℚ)) := by
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hbQ : (0 : ℚ) < b := by exact_mod_cast lt_trans ha hab
  have hcQ : (0 : ℚ) < c := by exact_mod_cast lt_trans (lt_trans ha hab) hbc
  have hbcQ : (b : ℚ) < c := by exact_mod_cast hbc
  rw [div_add_div _ _ (ne_of_gt (mul_pos haQ hbQ)) (ne_of_gt (mul_pos hbQ hcQ)),
    div_le_div_iff₀ (mul_pos haQ hcQ) (mul_pos (mul_pos haQ hbQ) (mul_pos hbQ hcQ))]
  have h1 : (a : ℚ) * b * b * c ≤ a * b * c * c := by
    have hprod : (0 : ℚ) < (a : ℚ) * b * c := mul_pos (mul_pos haQ hbQ) hcQ
    nlinarith
  have h2 : (0 : ℚ) ≤ (a : ℚ) * a * b * c := by positivity
  linarith

lemma R_insert_le : ∀ (p q : List ℕ) (b : ℕ),
    (p ++ b :: q).Pairwise (· < ·) →
    (∀ x ∈ p ++ b :: q, 0 < x) →
    R (p ++ q) ≤ R (p ++ b :: q)
  | [], q, b, _, _ => R_le_cons b q
  | [a], [], b, _, _ => by
    simp only [List.singleton_append, R]
    positivity
  | [a], c :: q, b, hpw, hpos => by
    simp only [List.singleton_append, R] at hpw ⊢
    rw [List.pairwise_cons] at hpw
    have hab : a < b := hpw.1 b List.mem_cons_self
    have hbc : b < c := (List.pairwise_cons.mp hpw.2).1 c List.mem_cons_self
    have ha : 0 < a := hpos a (by simp)
    linarith [inv_pair_insert ha hab hbc]
  | a1 :: a2 :: p, q, b, hpw, hpos => by
    simp only [List.cons_append, R]
    have ih := R_insert_le (a2 :: p) q b
      (List.pairwise_cons.mp hpw).2
      (fun x hx => hpos x (List.mem_cons_of_mem a1 hx))
    simp only [List.cons_append] at ih
    linarith

lemma sublist_of_pairwise_lt_subset : ∀ {L1 L2 : List ℕ},
    L1.Pairwise (· < ·) → L2.Pairwise (· < ·) → (∀ x ∈ L1, x ∈ L2) → L1 <+ L2
  | [], L2, _, _, _ => List.nil_sublist L2
  | a :: t1, [], _, _, hsub => absurd (hsub a List.mem_cons_self) List.not_mem_nil
  | a :: t1, b :: t2, h1, h2, hsub => by
    rw [List.pairwise_cons] at h1 h2
    have ha2 : a ∈ b :: t2 := hsub a List.mem_cons_self
    simp only [List.mem_cons] at ha2
    rcases ha2 with rfl | hat2
    · refine List.Sublist.cons_cons a (sublist_of_pairwise_lt_subset h1.2 h2.2 fun x hx => ?_)
      have hxb := hsub x (List.mem_cons_of_mem a hx)
      have hne : x ≠ a := fun h => Nat.lt_irrefl a (h ▸ h1.1 x hx)
      exact (List.mem_cons.mp hxb).resolve_left hne
    · have hba : b < a := h2.1 a hat2
      refine List.Sublist.cons b (sublist_of_pairwise_lt_subset (List.pairwise_cons.mpr h1) h2.2 fun x hx => ?_)
      have hxb := hsub x hx
      have hne : x ≠ b := by
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hxt1
        · exact Nat.ne_of_gt hba
        · exact Nat.ne_of_gt (lt_trans hba (h1.1 x hxt1))
      exact (List.mem_cons.mp hxb).resolve_left hne

lemma R_sublist_le : ∀ {L1 L2 : List ℕ},
    L1 <+ L2 → L2.Pairwise (· < ·) → (∀ x ∈ L2, 0 < x) → R L1 ≤ R L2 := by
  have haux : ∀ k (A B : List ℕ), B.length - A.length = k → A <+ B →
      B.Pairwise (· < ·) → (∀ x ∈ B, 0 < x) → R A ≤ R B := by
    intro k
    induction k with
    | zero =>
      intro A B hk hAB _ _
      have hlen : A.length = B.length := by
        have := hAB.length_le; omega
      have heq : A = B := hAB.eq_of_length hlen
      rw [heq]
    | succ k ihk =>
      intro A B hk hAB hpwB hposB
      have hlt : A.length < B.length := by
        have := hAB.length_le; omega
      have hex : ∃ p b q, B = p ++ b :: q ∧ A <+ p ++ q := by
        clear ihk hk hpwB hposB
        induction hAB with
        | slnil => simp at hlt
        | @cons X Y b hXY _ =>
          exact ⟨[], b, Y, rfl, hXY⟩
        | @cons_cons X Y x hXY ihXY =>
          have hlt' : X.length < Y.length := by simpa using hlt
          obtain ⟨p, b, q, rfl, hXq⟩ := ihXY hlt'
          exact ⟨x :: p, b, q, rfl, List.Sublist.cons_cons x hXq⟩
      obtain ⟨p, b, q, rfl, hApq⟩ := hex
      have hlen_pq : (p ++ q).length - A.length = k := by
        simp only [List.length_append, List.length_cons] at hk ⊢
        omega
      have hpw_pq : (p ++ q).Pairwise (· < ·) :=
        hpwB.sublist (List.Sublist.append_left (List.sublist_cons_self b q) p)
      have hpos_pq : ∀ x ∈ p ++ q, 0 < x := fun x hx =>
        hposB x ((List.Sublist.append_left (List.sublist_cons_self b q) p).subset hx)
      exact (ihk A (p ++ q) hlen_pq hApq hpw_pq hpos_pq).trans (R_insert_le p q b hpwB hposB)
  intro L1 L2 hsub hpw hpos
  exact haux (L2.length - L1.length) L1 L2 rfl hsub hpw hpos

lemma R_subset_le {L1 L2 : List ℕ}
    (h1 : L1.Pairwise (· < ·)) (h2 : L2.Pairwise (· < ·))
    (hpos : ∀ x ∈ L2, 0 < x) (hsub : ∀ x ∈ L1, x ∈ L2) :
    R L1 ≤ R L2 :=
  R_sublist_le (sublist_of_pairwise_lt_subset h1 h2 hsub) h2 hpos

/- ### Part 5: Exclude prime factors `≤ 7` -/

lemma no_small_prime_of_a_eq_8 {n p : ℕ} (hn : 2 ≤ n) (ha : OeisA251758.a n = 8)
    (hp : p.Prime) (hpn : p ∣ n) : 11 ≤ p := by
  by_contra hlt
  have hp7 : p ≤ 7 := by
    have : p < 11 := by omega
    interval_cases p <;> first | omega | norm_num at hp
  have h1p_pw : ([1, p] : List ℕ).Pairwise (· < ·) := by
    simp [hp.one_lt]
  have h1p_sub : ∀ x ∈ ([1, p] : List ℕ), x ∈ divList n := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [mem_divList (by omega)]
    rcases hx with rfl | rfl
    · exact one_dvd n
    · exact hpn
  have hpos : ∀ x ∈ divList n, 0 < x := fun x hx =>
    Nat.pos_of_dvd_of_pos ((mem_divList (by omega)).mp hx) (by omega)
  have hR_ge : R [1, p] ≤ R (divList n) :=
    R_subset_le h1p_pw (divList_pairwise_lt n) hpos h1p_sub
  have hR_le := (R_bounds_of_a_eq_8 hn ha).2
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.pos
  have hp7Q : (p : ℚ) ≤ 7 := by exact_mod_cast hp7
  have hR1p : R [1, p] = 1 / (p : ℚ) := by simp [R]
  rw [hR1p] at hR_ge
  have h17 : (1 : ℚ) / 7 ≤ 1 / (p : ℚ) := one_div_le_one_div_of_le hpQ hp7Q
  linarith

/- ### Part 6: `Q7`-smoothness, Euler product bound, and cutoff `150` -/

/-- A positive integer is `ps`-smooth if all its prime factors belong to `ps`. -/
def IsSmooth (ps : List ℕ) (d : ℕ) : Prop :=
  0 < d ∧ ∀ p : ℕ, p.Prime → p ∣ d → p ∈ ps

/-- Finite Euler product `∏_{p ∈ ps} p^2 / (p^2 - 1)` in `ℚ`. -/
def eulerProd : List ℕ → ℚ
  | [] => 1
  | p :: ps => ((p : ℚ) ^ 2 / ((p : ℚ) ^ 2 - 1)) * eulerProd ps

lemma geom_sum_le_inv (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, r ^ k ≤ 1 / (1 - r) := by
  have h1r : 0 < 1 - r := by linarith
  rw [le_div_iff₀ h1r]
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, add_mul]
    have hpow : 0 ≤ r ^ k := pow_nonneg hr0 k
    have hgeom : (∑ i ∈ Finset.range k, r ^ i) * (1 - r) = 1 - r ^ k := by
      clear ih hpow
      induction k with
      | zero => simp
      | succ m ihm =>
        rw [Finset.sum_range_succ, add_mul, ihm]
        ring
    rw [hgeom]
    nlinarith

lemma sum_inv_sq_smooth_le : ∀ {ps : List ℕ},
    (∀ p ∈ ps, p.Prime) → ps.Nodup →
    ∀ S : Finset ℕ, (∀ d ∈ S, IsSmooth ps d) →
      ∑ d ∈ S, (1 : ℚ) / ((d : ℚ) ^ 2) ≤ eulerProd ps
  | [], _, _, S, hS => by
    have hsub : S ⊆ {1} := by
      intro d hd
      rw [Finset.mem_singleton]
      obtain ⟨hdpos, hdprime⟩ := hS d hd
      by_contra hne1
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne1
      exact List.not_mem_nil (hdprime p hp hpd)
    calc ∑ d ∈ S, (1 : ℚ) / ((d : ℚ) ^ 2)
        ≤ ∑ d ∈ ({1} : Finset ℕ), (1 : ℚ) / ((d : ℚ) ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = 1 := by simp
      _ = eulerProd [] := rfl
  | p :: ps, hprime, hnodup, S, hS => by
    rw [List.nodup_cons] at hnodup
    have hp : p.Prime := hprime p List.mem_cons_self
    have hps_prime : ∀ q ∈ ps, q.Prime := fun q hq => hprime q (List.mem_cons_of_mem p hq)
    let E : ℕ := S.sup id + 1
    have hfact_lt : ∀ d ∈ S, d.factorization p < E := by
      intro d hd
      have h1 : d.factorization p ≤ d := by
        have hle : p ^ d.factorization p ≤ d :=
          Nat.le_of_dvd (hS d hd).1 (Nat.ordProj_dvd d p)
        have hlt : d.factorization p < p ^ d.factorization p :=
          Nat.lt_pow_self hp.one_lt
        omega
      have h2 : d ≤ S.sup id := Finset.le_sup (f := id) hd
      omega
    have hpart : S = (Finset.range E).biUnion (fun k => S.filter (fun d => d.factorization p = k)) := by
      ext d
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
      exact ⟨fun hd => ⟨d.factorization p, hfact_lt d hd, hd, rfl⟩, fun ⟨_, _, hd, _⟩ => hd⟩
    have hdisj : Set.PairwiseDisjoint (↑(Finset.range E) : Set ℕ)
        (fun k => S.filter (fun d => d.factorization p = k)) := by
      intro k1 _ k2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_filter]
      intro d _ h1 h2
      exact hne (h1.symm.trans h2)
    have hsum_split : ∑ d ∈ S, (1 : ℚ) / ((d : ℚ) ^ 2) =
        ∑ k ∈ Finset.range E, ∑ d ∈ S.filter (fun d => d.factorization p = k),
          (1 : ℚ) / ((d : ℚ) ^ 2) := by
      conv_lhs => rw [hpart]
      exact Finset.sum_biUnion hdisj
    have hslice : ∀ k ∈ Finset.range E,
        ∑ d ∈ S.filter (fun d => d.factorization p = k), (1 : ℚ) / ((d : ℚ) ^ 2) ≤
          ((1 : ℚ) / ((p : ℚ) ^ 2)) ^ k * eulerProd ps := by
      intro k _
      let Sk := S.filter (fun d => d.factorization p = k)
      let Mk := Sk.image (fun d => d / p ^ k)
      have hpk_dvd : ∀ d ∈ Sk, p ^ k ∣ d := by
        intro d hd
        rw [Finset.mem_filter] at hd
        rw [← hd.2]
        exact Nat.ordProj_dvd d p
      have hMk_smooth : ∀ m ∈ Mk, IsSmooth ps m := by
        intro m hm
        rw [Finset.mem_image] at hm
        rcases hm with ⟨d, hd, rfl⟩
        have hdS := (Finset.mem_filter.mp hd).1
        have hdk := (Finset.mem_filter.mp hd).2
        have hdvd := hpk_dvd d hd
        have hmpos : 0 < d / p ^ k := Nat.div_pos (Nat.le_of_dvd (hS d hdS).1 hdvd) (pow_pos hp.pos k)
        refine ⟨hmpos, fun q hq hqm => ?_⟩
        have hqd : q ∣ d := dvd_trans hqm (Nat.div_dvd_of_dvd hdvd)
        have hq_in := (hS d hdS).2 q hq hqd
        simp only [List.mem_cons] at hq_in
        rcases hq_in with hqp | hqps
        · exfalso
          subst hqp
          have hpk1 : q ^ (k + 1) ∣ d := by
            rw [pow_succ, ← Nat.mul_div_cancel' hdvd]
            exact Nat.mul_dvd_mul_left (q ^ k) hqm
          have hge : k + 1 ≤ d.factorization q :=
            (hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt (hS d hdS).1)).mp hpk1
          omega
        · exact hqps
      have hinj : Set.InjOn (fun d => d / p ^ k) (Sk : Set ℕ) := by
        intro d1 hd1 d2 hd2 heq
        dsimp only at heq
        have h1 := Nat.mul_div_cancel' (hpk_dvd d1 hd1)
        have h2 := Nat.mul_div_cancel' (hpk_dvd d2 hd2)
        rw [← h1, ← h2, heq]
      have hrew : ∑ d ∈ Sk, (1 : ℚ) / ((d : ℚ) ^ 2) =
          ((1 : ℚ) / ((p : ℚ) ^ 2)) ^ k * ∑ m ∈ Mk, (1 : ℚ) / ((m : ℚ) ^ 2) := by
        rw [Finset.mul_sum, Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun d hd => ?_
        have hdvd := hpk_dvd d hd
        have hmul : (p ^ k : ℕ) * (d / p ^ k) = d := Nat.mul_div_cancel' hdvd
        have hmulQ : ((p : ℚ) ^ k) * ((d / p ^ k : ℕ) : ℚ) = (d : ℚ) := by
          exact_mod_cast hmul
        rw [← hmulQ, mul_pow, one_div_pow, ← pow_mul, ← pow_mul, mul_comm 2 k]
        simp only [one_div, mul_inv]
      rw [hrew]
      exact mul_le_mul_of_nonneg_left (sum_inv_sq_smooth_le hps_prime hnodup.2 Mk hMk_smooth) (by positivity)
    rw [hsum_split]
    calc ∑ k ∈ Finset.range E, ∑ d ∈ S.filter (fun d => d.factorization p = k),
            (1 : ℚ) / ((d : ℚ) ^ 2)
        ≤ ∑ k ∈ Finset.range E, ((1 : ℚ) / ((p : ℚ) ^ 2)) ^ k * eulerProd ps :=
          Finset.sum_le_sum hslice
      _ = (∑ k ∈ Finset.range E, ((1 : ℚ) / ((p : ℚ) ^ 2)) ^ k) * eulerProd ps :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (1 / (1 - (1 : ℚ) / ((p : ℚ) ^ 2))) * eulerProd ps := by
          have hr0 : (0 : ℚ) ≤ 1 / ((p : ℚ) ^ 2) := by positivity
          have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
          have hr1 : (1 : ℚ) / ((p : ℚ) ^ 2) < 1 := by
            rw [div_lt_one (by positivity)]; nlinarith
          have heul0 : 0 ≤ eulerProd ps := by
            have := sum_inv_sq_smooth_le hps_prime hnodup.2 ∅ (by simp)
            simpa using this
          exact mul_le_mul_of_nonneg_right (geom_sum_le_inv _ hr0 hr1 E) heul0
      _ = eulerProd (p :: ps) := by
          simp only [eulerProd]
          congr 1
          have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
          have hne : (p : ℚ) ^ 2 - 1 ≠ 0 := by nlinarith
          have hpne : (p : ℚ) ^ 2 ≠ 0 := by positivity
          field_simp

/-- Fast decidable smoothness test for `n ≤ 150`. -/
def stripFactor (p : ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => if p ∣ n then stripFactor p k (n / p) else n

def isQ7SmoothB (n : ℕ) : Bool :=
  (Q7.foldl (fun m p => stripFactor p 3 m) n) == 1

lemma stripFactor_dvd (p k n : ℕ) : stripFactor p k n ∣ n := by
  induction k generalizing n with
  | zero => exact dvd_refl n
  | succ k ih =>
    simp only [stripFactor]
    split_ifs with h
    · exact dvd_trans (ih (n / p)) (Nat.div_dvd_of_dvd h)
    · exact dvd_refl n

lemma stripFactor_pos (p k n : ℕ) (hn : 0 < n) : 0 < stripFactor p k n :=
  Nat.pos_of_dvd_of_pos (stripFactor_dvd p k n) hn

lemma not_dvd_stripFactor (p k n : ℕ) (hp : 2 ≤ p) (hn : 0 < n) (hlt : n < p ^ k) :
    ¬ p ∣ stripFactor p k n := by
  induction k generalizing n with
  | zero => simp at hlt; omega
  | succ k ih =>
    simp only [stripFactor]
    split_ifs with h
    · apply ih (n / p) (Nat.div_pos (Nat.le_of_dvd hn h) (by omega))
      rw [Nat.div_lt_iff_lt_mul (by omega), ← pow_succ]
      exact hlt
    · exact h

lemma Q7_smooth_le_150_mem_P150 {d : ℕ} (hd : IsSmooth Q7 d) (hle : d ≤ 150) :
    d ∈ P150 := by
  have hfilt : (List.range 151).filter isQ7SmoothB = P150 := by decide
  rw [← hfilt, List.mem_filter, List.mem_range]
  refine ⟨by omega, ?_⟩
  simp only [isQ7SmoothB, beq_iff_eq]
  -- Strip each of the 7 primes in Q7; after stripping all 7, no prime in Q7 divides the result,
  -- yet every prime factor of the result lies in Q7, so the result must equal 1!
  have hstep : ∀ (ps : List ℕ) (m : ℕ),
      (∀ p ∈ ps, 11 ≤ p) → 0 < m → m ≤ 150 →
      (ps.foldl (fun x p => stripFactor p 3 x) m ∣ m) ∧
      (∀ p ∈ ps, ¬ p ∣ ps.foldl (fun x p => stripFactor p 3 x) m) := by
    intro ps
    induction ps with
    | nil => intro m _ _ _; exact ⟨dvd_refl m, by simp⟩
    | cons p ps ih =>
      intro m h11 hmpos hmle
      have hp11 : 11 ≤ p := h11 p List.mem_cons_self
      have hps11 : ∀ q ∈ ps, 11 ≤ q := fun q hq => h11 q (List.mem_cons_of_mem p hq)
      let m1 := stripFactor p 3 m
      have hm1_dvd : m1 ∣ m := stripFactor_dvd p 3 m
      have hm1_pos : 0 < m1 := stripFactor_pos p 3 m hmpos
      have hm1_le : m1 ≤ 150 := (Nat.le_of_dvd hmpos hm1_dvd).trans hmle
      have hnotp : ¬ p ∣ m1 := by
        apply not_dvd_stripFactor p 3 m (by omega) hmpos
        have : 11 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp11 3
        omega
      obtain ⟨hdvd2, hnot2⟩ := ih m1 hps11 hm1_pos hm1_le
      refine ⟨dvd_trans hdvd2 hm1_dvd, fun q hq => ?_⟩
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hqps
      · exact fun h => hnotp (dvd_trans h hdvd2)
      · exact hnot2 q hqps
  obtain ⟨hres_dvd, hres_not⟩ := hstep Q7 d (by decide) hd.1 hle
  have hres_pos : 0 < Q7.foldl (fun m p => stripFactor p 3 m) d :=
    Nat.pos_of_dvd_of_pos hres_dvd hd.1
  by_contra hne1
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne1
  have hq_in : q ∈ Q7 := hd.2 q hq_prime (dvd_trans hq_dvd hres_dvd)
  exact hres_not q hq_in hq_dvd

lemma R_le_sum_inv_sq : ∀ {L : List ℕ},
    L.Pairwise (· < ·) → (∀ x ∈ L, 0 < x) →
    R L ≤ (L.map (fun d : ℕ => (1 : ℚ) / ((d : ℚ) ^ 2))).sum
  | [], _, _ => le_refl 0
  | [a], _, _ => by simp only [R, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]; positivity
  | a :: b :: t, hpw, hpos => by
    simp only [R, List.map_cons, List.sum_cons]
    have hab : a < b := (List.pairwise_cons.mp hpw).1 b List.mem_cons_self
    have ha : (0 : ℚ) < a := by exact_mod_cast hpos a List.mem_cons_self
    have habQ : (a : ℚ) ≤ b := by exact_mod_cast le_of_lt hab
    have hterm : (1 : ℚ) / ((a : ℚ) * (b : ℚ)) ≤ 1 / ((a : ℚ) ^ 2) := by
      rw [sq]
      exact one_div_le_one_div_of_le (mul_pos ha ha) (mul_le_mul_of_nonneg_left habQ (le_of_lt ha))
    have ih := R_le_sum_inv_sq (List.pairwise_cons.mp hpw).2
      (fun x hx => hpos x (List.mem_cons_of_mem a hx))
    simp only [List.map_cons, List.sum_cons] at ih
    linarith

lemma R_append_split : ∀ (P : List ℕ) (lastP : ℕ) (T : List ℕ) (hne : P ≠ []),
    P.getLast hne = lastP →
    R (P ++ T) = R P + (match T with | [] => 0 | t0 :: _ => (1 : ℚ) / ((lastP : ℚ) * (t0 : ℚ))) + R T
  | [], _, _, hne, _ => absurd rfl hne
  | [a], lastP, T, _, hlast => by
    simp only [List.getLast_singleton] at hlast
    subst hlast
    cases T with
    | nil => simp [R]
    | cons t0 t' => simp [R]
  | a :: b :: P', lastP, T, _, hlast => by
    have ih := R_append_split (b :: P') lastP T (List.cons_ne_nil _ _) (by simpa using hlast)
    simp only [List.cons_append, R] at ih ⊢
    linarith

lemma R_Q7_smooth_lt_one_ninth {U : List ℕ}
    (hUpw : U.Pairwise (· < ·)) (hUsmooth : ∀ d ∈ U, IsSmooth Q7 d) :
    R U < (1 : ℚ) / 9 := by
  let T := U.filter (fun d => decide (150 < d))
  have hTpw : T.Pairwise (· < ·) := hUpw.filter _
  have hTgt : ∀ d ∈ T, 150 < d := fun d hd => by
    have := (List.mem_filter.mp hd).2
    simpa using this
  have hP150_pw : P150.Pairwise (· < ·) := pairwise_lt_of_isChainLt (by decide : isChainLt P150 = true)
  have hP150_le : ∀ d ∈ P150, d ≤ 143 := by decide
  have hP150_pos : ∀ d ∈ P150, 0 < d := by decide
  have hP150_smooth : ∀ d ∈ P150, IsSmooth Q7 d := by
    intro d hd
    have hcases : d = 1 ∨ d = 11 ∨ d = 13 ∨ d = 17 ∨ d = 19 ∨
        d = 23 ∨ d = 29 ∨ d = 31 ∨ d = 121 ∨ d = 143 := by
      simpa [P150] using hd
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, fun p hp h => absurd (Nat.le_of_dvd (by decide) h) (by have := hp.two_le; omega)⟩
    · exact ⟨by decide, fun p hp h => by
        have := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h; subst this; decide⟩
    · exact ⟨by decide, fun p hp h => by
        have := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h; subst this; decide⟩
    · exact ⟨by decide, fun p hp h => by
        have := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h; subst this; decide⟩
    · exact ⟨by decide, fun p hp h => by
        have := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h; subst this; decide⟩
    · exact ⟨by decide, fun p hp h => by
        have := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h; subst this; decide⟩
    · exact ⟨by decide, fun p hp h => by
        have := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h; subst this; decide⟩
    · exact ⟨by decide, fun p hp h => by
        have := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h; subst this; decide⟩
    · exact ⟨by decide, fun p hp h => by
        have h11 : p ∣ 11 ^ 2 := by simpa using h
        have := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow h11)
        subst this; decide⟩
    · exact ⟨by decide, fun p hp h => by
        have h143 : p ∣ 11 * 13 := by simpa using h
        rcases hp.dvd_mul.mp h143 with h1 | h2
        · have := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h1; subst this; decide
        · have := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h2; subst this; decide⟩
  let V := P150 ++ T
  have hVpw : V.Pairwise (· < ·) := by
    rw [List.pairwise_append]
    exact ⟨hP150_pw, hTpw, fun a ha b hb => lt_of_le_of_lt (hP150_le a ha) (lt_trans (by decide : 143 < 150) (hTgt b hb))⟩
  have hVpos : ∀ d ∈ V, 0 < d := by
    intro d hd
    rcases List.mem_append.mp hd with h | h
    · exact hP150_pos d h
    · exact lt_trans (by decide : 0 < 150) (hTgt d h)
  have hU_sub_V : ∀ d ∈ U, d ∈ V := by
    intro d hd
    rw [List.mem_append]
    by_cases hle : d ≤ 150
    · exact Or.inl (Q7_smooth_le_150_mem_P150 (hUsmooth d hd) hle)
    · exact Or.inr (List.mem_filter.mpr ⟨hd, by simpa using Nat.lt_of_not_ge hle⟩)
  have hRU_le_RV : R U ≤ R V := R_subset_le hUpw hVpw hVpos hU_sub_V
  have hRV_split : R V ≤ R P150 + (1 : ℚ) / (143 * 151) +
      (T.map (fun d : ℕ => (1 : ℚ) / ((d : ℚ) ^ 2))).sum := by
    have hsp := R_append_split P150 143 T (by decide) (by decide)
    rw [hsp]
    have hRT := R_le_sum_inv_sq hTpw (fun d hd => lt_trans (by decide) (hTgt d hd))
    have hbridge : (match T with | [] => (0 : ℚ) | t0 :: _ => 1 / ((143 : ℚ) * (t0 : ℚ))) ≤
        1 / (143 * 151) := by
      cases hT : T with
      | nil => positivity
      | cons t0 t' =>
        have ht0 : 151 ≤ t0 := hTgt t0 (by rw [hT]; exact List.mem_cons_self)
        have ht0Q : (151 : ℚ) ≤ t0 := by exact_mod_cast ht0
        exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  -- Bound the tail sum using `sum_inv_sq_smooth_le` on `V.toFinset`
  have hVnodup : V.Nodup := hVpw.nodup
  have hVsmooth : ∀ d ∈ V.toFinset, IsSmooth Q7 d := by
    intro d hd
    rw [List.mem_toFinset, List.mem_append] at hd
    rcases hd with h | h
    · exact hP150_smooth d h
    · exact hUsmooth d (List.mem_filter.mp h).1
  have hEuler := sum_inv_sq_smooth_le (by decide : ∀ p ∈ Q7, p.Prime)
    (by decide : Q7.Nodup) V.toFinset hVsmooth
  have hVsum : ∑ d ∈ V.toFinset, (1 : ℚ) / ((d : ℚ) ^ 2) =
      (P150.map (fun d : ℕ => (1 : ℚ) / ((d : ℚ) ^ 2))).sum +
      (T.map (fun d : ℕ => (1 : ℚ) / ((d : ℚ) ^ 2))).sum := by
    rw [List.sum_toFinset _ hVnodup, List.map_append, List.sum_append]
  have hT_bound : (T.map (fun d : ℕ => (1 : ℚ) / ((d : ℚ) ^ 2))).sum ≤
      eulerProd Q7 - (P150.map (fun d : ℕ => (1 : ℚ) / ((d : ℚ) ^ 2))).sum := by
    linarith
  have hnum : R P150 + (1 : ℚ) / (143 * 151) +
      (eulerProd Q7 - (P150.map (fun d : ℕ => (1 : ℚ) / ((d : ℚ) ^ 2))).sum) < 1 / 9 := by
    simp only [P150, Q7, R, eulerProd, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    norm_num
  linarith

/- ### Part 7: Order statistics and prime compression for `2 ≤ n < X0` -/

lemma Q8_le_sorted_primes {qs : List ℕ}
    (hpw : qs.Pairwise (· < ·)) (hpr : ∀ q ∈ qs, q.Prime) (h11 : ∀ q ∈ qs, 11 ≤ q) :
    ∀ i (hQ : i < Q8.length) (hq : i < qs.length), Q8[i] ≤ qs[i] := by
  have hnext : ∀ (a b q : ℕ), q.Prime → a < q → (∀ x < b, a < x → ¬ x.Prime) → b ≤ q := by
    intro a b q hq ha hno
    by_contra hlt
    exact hno q (Nat.lt_of_not_ge hlt) ha hq
  intro i hQ hq
  have hi8 : i < 8 := hQ
  have h0 : ∀ h0 : 0 < qs.length, 11 ≤ qs[0] := fun h0 => h11 qs[0] (List.getElem_mem h0)
  have h1 : ∀ h1 : 1 < qs.length, 13 ≤ qs[1] := fun h1 => by
    have hlt := List.pairwise_iff_getElem.mp hpw 0 1 (by omega) h1 (by omega)
    have := h0 (by omega)
    exact hnext 11 13 qs[1] (hpr _ (List.getElem_mem h1)) (by omega) (by decide)
  have h2 : ∀ h2 : 2 < qs.length, 17 ≤ qs[2] := fun h2 => by
    have hlt := List.pairwise_iff_getElem.mp hpw 1 2 (by omega) h2 (by omega)
    have := h1 (by omega)
    exact hnext 13 17 qs[2] (hpr _ (List.getElem_mem h2)) (by omega) (by decide)
  have h3 : ∀ h3 : 3 < qs.length, 19 ≤ qs[3] := fun h3 => by
    have hlt := List.pairwise_iff_getElem.mp hpw 2 3 (by omega) h3 (by omega)
    have := h2 (by omega)
    exact hnext 17 19 qs[3] (hpr _ (List.getElem_mem h3)) (by omega) (by decide)
  have h4 : ∀ h4 : 4 < qs.length, 23 ≤ qs[4] := fun h4 => by
    have hlt := List.pairwise_iff_getElem.mp hpw 3 4 (by omega) h4 (by omega)
    have := h3 (by omega)
    exact hnext 19 23 qs[4] (hpr _ (List.getElem_mem h4)) (by omega) (by decide)
  have h5 : ∀ h5 : 5 < qs.length, 29 ≤ qs[5] := fun h5 => by
    have hlt := List.pairwise_iff_getElem.mp hpw 4 5 (by omega) h5 (by omega)
    have := h4 (by omega)
    exact hnext 23 29 qs[5] (hpr _ (List.getElem_mem h5)) (by omega) (by decide)
  have h6 : ∀ h6 : 6 < qs.length, 31 ≤ qs[6] := fun h6 => by
    have hlt := List.pairwise_iff_getElem.mp hpw 5 6 (by omega) h6 (by omega)
    have := h5 (by omega)
    exact hnext 29 31 qs[6] (hpr _ (List.getElem_mem h6)) (by omega) (by decide)
  have h7 : ∀ h7 : 7 < qs.length, 37 ≤ qs[7] := fun h7 => by
    have hlt := List.pairwise_iff_getElem.mp hpw 6 7 (by omega) h7 (by omega)
    have := h6 (by omega)
    exact hnext 31 37 qs[7] (hpr _ (List.getElem_mem h7)) (by omega) (by decide)
  interval_cases i
  · exact h0 hq
  · exact h1 hq
  · exact h2 hq
  · exact h3 hq
  · exact h4 hq
  · exact h5 hq
  · exact h6 hq
  · exact h7 hq

lemma list_prod_dvd_of_prime_nodup {n : ℕ} : ∀ {L : List ℕ},
    (∀ p ∈ L, p.Prime ∧ p ∣ n) → L.Nodup → L.prod ∣ n
  | [], _, _ => one_dvd n
  | p :: t, h, hnd => by
    rw [List.nodup_cons] at hnd
    have hp := h p List.mem_cons_self
    have ht : ∀ q ∈ t, q.Prime ∧ q ∣ n := fun q hq => h q (List.mem_cons_of_mem p hq)
    have ih := list_prod_dvd_of_prime_nodup ht hnd.2
    have hcop : Nat.Coprime p t.prod := coprime_list_prod fun q hq =>
      (Nat.coprime_primes hp.1 (ht q hq).1).mpr (fun heq => hnd.1 (heq ▸ hq))
    rw [List.prod_cons]
    exact hcop.mul_dvd_of_dvd_of_dvd hp.2 ih

lemma order_stat_le {D U : List ℕ} {f : ℕ → ℕ}
    (hDpw : D.Pairwise (· < ·)) (hUpw : U.Pairwise (· < ·))
    (hinj : ∀ a ∈ D, ∀ b ∈ D, f a = f b → a = b)
    (hle : ∀ x ∈ D, f x ≤ x)
    (hmem : ∀ y, y ∈ U ↔ ∃ x ∈ D, f x = y)
    (i : ℕ) (hU : i < U.length) (hD : i < D.length) :
    U[i] ≤ D[i] := by
  by_contra hgt
  have hlt : D[i] < U[i] := Nat.lt_of_not_ge hgt
  -- The `i + 1` elements `f(D[0]), ..., f(D[i])` are distinct and all `< U[i]`,
  -- so they all lie in `U.take i` (which has length `i`), contradiction!
  let S : Finset ℕ := (D.take (i + 1)).toFinset.image f
  have hS_card : S.card = i + 1 := by
    have htk_nd : (D.take (i + 1)).Nodup := hDpw.nodup.sublist (List.take_sublist _ _)
    have hinj' : Set.InjOn f ((D.take (i + 1)).toFinset : Set ℕ) := by
      intro a ha b hb hab
      rw [Finset.mem_coe, List.mem_toFinset] at ha hb
      exact hinj a (List.mem_of_mem_take ha) b (List.mem_of_mem_take hb) hab
    rw [Finset.card_image_of_injOn hinj', List.toFinset_card_of_nodup htk_nd, List.length_take]
    omega
  have hS_sub : S ⊆ (U.take i).toFinset := by
    intro y hy
    rw [Finset.mem_image] at hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [List.mem_toFinset] at hx ⊢
    have hxD : x ∈ D := List.mem_of_mem_take hx
    have hx_le : x ≤ D[i] := by
      rw [List.mem_iff_getElem] at hx
      rcases hx with ⟨j, hj, rfl⟩
      rw [List.getElem_take]
      have hji : j ≤ i := by
        rw [List.length_take] at hj; omega
      rcases eq_or_lt_of_le hji with rfl | hjlt
      · exact le_refl _
      · exact le_of_lt (List.pairwise_iff_getElem.mp hDpw j i (by omega) hD hjlt)
    have hfx_lt : f x < U[i] := lt_of_le_of_lt ((hle x hxD).trans hx_le) hlt
    have hfxU : f x ∈ U := (hmem (f x)).mpr ⟨x, hxD, rfl⟩
    rw [List.mem_iff_getElem] at hfxU
    rcases hfxU with ⟨m, hm, hUm⟩
    have hmi : m < i := by
      by_contra hge
      have him : i ≤ m := Nat.le_of_not_lt hge
      have hUle : U[i] ≤ U[m] := by
        rcases eq_or_lt_of_le him with rfl | hilt
        · exact le_refl _
        · exact le_of_lt (List.pairwise_iff_getElem.mp hUpw i m hU hm hilt)
      omega
    rw [List.mem_iff_getElem]
    exact ⟨m, by rw [List.length_take]; omega, by rw [List.getElem_take]; exact hUm⟩
  have hcard_le : S.card ≤ (U.take i).toFinset.card := Finset.card_le_card hS_sub
  have htk_le : (U.take i).toFinset.card ≤ i := by
    exact (List.toFinset_card_le _).trans (by rw [List.length_take]; omega)
  omega

lemma not_a_eq_8_of_lt_X0 {n : ℕ} (hn2 : 2 ≤ n) (hnlt : n < X0) : OeisA251758.a n ≠ 8 := by
  intro ha
  have h11 : ∀ p : ℕ, p.Prime → p ∣ n → 11 ≤ p := fun p hp hpn =>
    no_small_prime_of_a_eq_8 hn2 ha hp hpn
  let qs : List ℕ := n.primeFactors.sort (· ≤ ·)
  have hqs_sorted : qs.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hqs_nd : qs.Nodup := Finset.sort_nodup _ _
  have hqs_pw : qs.Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem] at hqs_sorted ⊢
    intro i j hi hj hij
    have hle := hqs_sorted i j hi hj hij
    have hne : qs[i] ≠ qs[j] := fun h => by
      have hinj := (List.nodup_iff_injective_getElem.mp hqs_nd) (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) h
      simp at hinj
      omega
    omega
  have hqs_mem : ∀ p, p ∈ qs ↔ p.Prime ∧ p ∣ n := by
    intro p
    rw [Finset.mem_sort, Nat.mem_primeFactors]
    exact ⟨fun ⟨hp, hpn, _⟩ => ⟨hp, hpn⟩, fun ⟨hp, hpn⟩ => ⟨hp, hpn, by omega⟩⟩
  have hqs_pr : ∀ q ∈ qs, q.Prime := fun q hq => ((hqs_mem q).mp hq).1
  have hqs_11 : ∀ q ∈ qs, 11 ≤ q := fun q hq => h11 q ((hqs_mem q).mp hq).1 ((hqs_mem q).mp hq).2
  have hqs_le_7 : qs.length ≤ 7 := by
    by_contra hgt
    have hge8 : 8 ≤ qs.length := by omega
    have hQ8_le := Q8_le_sorted_primes hqs_pw hqs_pr hqs_11
    have hprod_le : (Q8.prod : ℕ) ≤ (qs.take 8).prod := by
      have h1 : Q8.prod = ∏ i : Fin 8, Q8[i.1]'(by simp [Q8]) := by decide
      have h2 : (qs.take 8).prod = ∏ i : Fin 8, qs[i.1]'(by omega) := by
        rw [← List.prod_ofFn]
        congr 1
        apply List.ext_getElem (by simp; omega)
        intro i hi1 hi2
        rw [List.getElem_take, List.getElem_ofFn]
      rw [h1, h2]
      exact Finset.prod_le_prod' fun i _ => hQ8_le i.1 (by simp [Q8]) (by omega)
    have hQ8_eq : Q8.prod = X0 := by decide
    have hdvd : (qs.take 8).prod ∣ n :=
      list_prod_dvd_of_prime_nodup (fun p hp => (hqs_mem p).mp (List.mem_of_mem_take hp))
        (hqs_nd.sublist (List.take_sublist _ _))
    have hle_n : (qs.take 8).prod ≤ n := Nat.le_of_dvd (by omega) hdvd
    omega
  -- Define the prime-compression map `phi` on divisors of `n`
  let phi : ℕ → ℕ := fun d => ∏ i : Fin qs.length, (Q7[i.1]'(by simp [Q7]; omega)) ^ d.factorization qs[i.1]
  have hQ7_pr : ∀ i : Fin qs.length, (Q7[i.1]'(by simp [Q7]; omega)).Prime := by
    have h := (by decide : ∀ p ∈ Q7, p.Prime)
    intro i; exact h _ (List.getElem_mem _)
  have hQ7_inj : ∀ i j : Fin qs.length,
      Q7[i.1]'(by simp [Q7]; omega) = Q7[j.1]'(by simp [Q7]; omega) → i = j := by
    have hnd : Q7.Nodup := by decide
    intro i j heq
    have hinj := (List.nodup_iff_injective_getElem.mp hnd)
      (a₁ := ⟨i.1, by simp [Q7]; omega⟩) (a₂ := ⟨j.1, by simp [Q7]; omega⟩) heq
    exact Fin.ext (by simpa using hinj)
  have hQ7_le_qs : ∀ i : Fin qs.length, Q7[i.1]'(by simp [Q7]; omega) ≤ qs[i.1] := by
    have hQ8_le := Q8_le_sorted_primes hqs_pw hqs_pr hqs_11
    intro ⟨idx, hidx⟩
    have h78 : Q7[idx]'(by simp [Q7]; omega) = Q8[idx]'(by simp [Q8]; omega) := by
      have hi7 : idx < 7 := by omega
      interval_cases idx <;> rfl
    rw [h78]
    exact hQ8_le idx (by simp [Q8]; omega) hidx
  have hd_prod : ∀ d ∈ divList n, d = ∏ i : Fin qs.length, qs[i.1] ^ d.factorization qs[i.1] := by
    intro d hd
    have hdn : d ∣ n := (mem_divList (by omega)).mp hd
    have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_dvd_of_pos hdn (by omega))
    have hsub : d.primeFactors ⊆ qs.toFinset := by
      intro p hp
      rw [List.mem_toFinset, hqs_mem]
      rw [Nat.mem_primeFactors] at hp
      exact ⟨hp.1, dvd_trans hp.2.1 hdn⟩
    have hprod_fin : ∏ p ∈ qs.toFinset, p ^ d.factorization p = d := by
      conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hd0]
      rw [Finsupp.prod]
      symm
      apply Finset.prod_subset hsub
      intro p _ hp_not
      have h0 : d.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
      rw [h0, pow_zero]
    conv_lhs => rw [← hprod_fin]
    symm
    refine Finset.prod_bij (fun (i : Fin qs.length) _ => qs[i.1])
      (fun i _ => List.mem_toFinset.mpr (List.getElem_mem i.2))
      (fun i _ j _ h => (List.nodup_iff_injective_getElem.mp hqs_nd) (a₁ := i) (a₂ := j) h)
      (fun p hp => by
        obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hp)
        exact ⟨⟨idx, hidx⟩, Finset.mem_univ _, rfl⟩)
      (fun _ _ => rfl)
  have hphi_le : ∀ d ∈ divList n, phi d ≤ d := by
    intro d hd
    conv_rhs => rw [hd_prod d hd]
    exact Finset.prod_le_prod' fun i _ => Nat.pow_le_pow_left (hQ7_le_qs i) _
  have hphi_fact : ∀ (d : ℕ) (i : Fin qs.length),
      (phi d).factorization (Q7[i.1]'(by simp [Q7]; omega)) = d.factorization qs[i.1] := by
    intro d i
    have hne : ∀ j : Fin qs.length, (Q7[j.1]'(by simp [Q7]; omega)) ^ d.factorization qs[j.1] ≠ 0 :=
      fun j => pow_ne_zero _ (Nat.ne_of_gt (hQ7_pr j).pos)
    dsimp only [phi]
    rw [Nat.factorization_prod (fun j _ => hne j), Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single i]
    · rw [(hQ7_pr i).factorization_pow, Finsupp.single_eq_same]
    · intro j _ hji
      rw [(hQ7_pr j).factorization_pow, Finsupp.single_eq_of_ne]
      exact fun heq => hji (hQ7_inj j i heq.symm)
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hphi_inj : ∀ a ∈ divList n, ∀ b ∈ divList n, phi a = phi b → a = b := by
    intro a ha b hb heq
    rw [hd_prod a ha, hd_prod b hb]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← hphi_fact a i, ← hphi_fact b i, heq]
  have hphi_smooth : ∀ d ∈ divList n, IsSmooth Q7 (phi d) := by
    intro d _
    refine ⟨Finset.prod_pos fun i _ => pow_pos (hQ7_pr i).pos _, fun p hp hpd => ?_⟩
    obtain ⟨i, _, hi⟩ := hp.prime.exists_mem_finset_dvd hpd
    have hpi : p ∣ Q7[i.1]'(by simp [Q7]; omega) := hp.dvd_of_dvd_pow hi
    have heq := (Nat.prime_dvd_prime_iff_eq hp (hQ7_pr i)).mp hpi
    rw [heq]
    exact List.getElem_mem _
  let U : List ℕ := ((divList n).map phi).toFinset.sort (· ≤ ·)
  have hU_nd : U.Nodup := Finset.sort_nodup _ _
  have hU_sorted : U.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hU_len : U.length = (divList n).length := by
    have hmap_nd : ((divList n).map phi).Nodup :=
      List.Nodup.map_on (fun a ha b hb h => hphi_inj a ha b hb h) (divList_pairwise_lt n).nodup
    rw [Finset.length_sort, List.toFinset_card_of_nodup hmap_nd, List.length_map]
  have hU_mem : ∀ y, y ∈ U ↔ ∃ x ∈ divList n, phi x = y := by
    intro y
    rw [Finset.mem_sort, List.mem_toFinset, List.mem_map]
  have hU_pw : U.Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem] at hU_sorted ⊢
    intro i j hi hj hij
    have hle := hU_sorted i j hi hj hij
    have hne : U[i] ≠ U[j] := fun h => by
      have hinj := (List.nodup_iff_injective_getElem.mp hU_nd) (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) h
      simp at hinj
      omega
    omega
  have hU_smooth : ∀ y ∈ U, IsSmooth Q7 y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hU_mem y).mp hy
    exact hphi_smooth x hx
  have hRD_le_RU : R (divList n) ≤ R U := by
    apply R_pointwise_le hU_len
    · intro i hi
      exact (hU_smooth U[i] (List.getElem_mem hi)).1
    · intro i hU hD
      exact order_stat_le (divList_pairwise_lt n) hU_pw hphi_inj hphi_le hU_mem i hU hD
  have hRU_lt : R U < 1 / 9 := R_Q7_smooth_lt_one_ninth hU_pw hU_smooth
  have hRD_gt := (R_bounds_of_a_eq_8 hn2 ha).1
  linarith

theorem main :
    IsLeast {x : ℕ | 2 ≤ x ∧ OeisA251758.a x = 8}
      (Nat.kthPrimorial 12 / Nat.kthPrimorial (Nat.primeCounting' 8)) := by
  rw [target_eq_X0]
  refine ⟨⟨by decide, a_X0_eq_8⟩, ?_⟩
  intro n ⟨hn2, ha⟩
  by_contra hlt
  exact not_a_eq_8_of_lt_X0 hn2 (Nat.lt_of_not_ge hlt) ha

end OMAO251758

theorem OMA.solution : type_of% @OeisA251758.conjecture :=
  OMAO251758.main
