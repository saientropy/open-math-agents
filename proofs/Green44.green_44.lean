import FormalConjectures.GreensOpenProblems.«44»

/-!
# Disproof of Green's Open Problem 44

We refute `Green44.green_44` using a short-interval prime cluster inside `(10^12, 2 * 10^12]`
with `N = 10^15`. By a pure-`ℕ` Chebyshev lower bound on the number of primes in `(m, 2m]`
and pigeonhole over `4000` subintervals of width `W = 250000000`, there exists `L ∈ [m, 2m - W]`
such that `(L, L + W]` contains at least `1000` primes `p_0 < ... < p_999`. Every `x ∈ [1, N]`
with `x % L < L / 4` reduces modulo `p_i = L + δ_i` (`0 < δ_i ≤ W`) into the interval
`[-(L / 4), L / 4)` of at most `L / 2 ≤ p_i / 2` residue classes, so choosing `A_i` of size
`p_i / 2` in the complement leaves all such `x` unsieved, yielding `10 * remaining.card > N`.
-/

namespace Green44Disproof

open Finset

private lemma centralBinom_le_bound (m : ℕ) (hm : 2 < m) :
    m.centralBinom ≤
      (2 * m) ^ Nat.sqrt (2 * m) * 4 ^ (2 * m / 3) *
        (2 * m) ^ ((Finset.Ioc m (2 * m)).filter Nat.Prime).card := by
  have hm_pos : 0 < m := by omega
  have h2m_pos : 1 ≤ 2 * m := by omega
  let f : ℕ → ℕ := fun x => x ^ m.centralBinom.factorization x
  have hsupp : m.centralBinom.factorization.support ⊆ Finset.range (2 * m + 1) := by
    intro p hp
    rw [Finsupp.mem_support_iff] at hp
    rw [Finset.mem_range]
    by_contra hge
    push Not at hge
    have hlt : 2 * m < p := by omega
    exact hp (Nat.factorization_choose_eq_zero_of_lt hlt)
  have hcb_eq : m.centralBinom = ∏ p ∈ Finset.range (2 * m + 1), f p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self m.centralBinom_ne_zero]
    exact Finsupp.prod_of_support_subset m.centralBinom.factorization hsupp (fun p e => p ^ e)
      (fun _ _ => pow_zero _)
  let AllP := (Finset.range (2 * m + 1)).filter Nat.Prime
  have hcb_primes : m.centralBinom = ∏ p ∈ AllP, f p := by
    rw [hcb_eq]
    symm
    refine Finset.prod_filter_of_ne fun p _ hne => ?_
    by_contra hnp
    apply hne
    dsimp only [f]
    rw [Nat.factorization_eq_zero_of_not_prime m.centralBinom hnp, pow_zero]
  rw [hcb_primes, ← Finset.prod_filter_mul_prod_filter_not AllP (· ≤ 2 * m / 3)]
  have hSmall_eq :
      AllP.filter (· ≤ 2 * m / 3) = (Finset.range (2 * m / 3 + 1)).filter Nat.Prime := by
    ext p
    simp only [AllP, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun ⟨⟨_, hp⟩, hle⟩ => ⟨by omega, hp⟩, fun ⟨hlt, hp⟩ => ⟨⟨by omega, hp⟩, by omega⟩⟩
  rw [hSmall_eq]
  apply Nat.mul_le_mul
  · let S := (Finset.range (2 * m / 3 + 1)).filter Nat.Prime
    rw [← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt (2 * m))]
    apply Nat.mul_le_mul
    · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ 2 * m)).trans ?_
      · exact Nat.pow_factorization_choose_le (by omega)
      rw [Finset.prod_const]
      have hsub : S.filter (· ≤ Nat.sqrt (2 * m)) ⊆ Finset.Icc 1 (Nat.sqrt (2 * m)) := by
        intro p hp
        simp only [S, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
        exact ⟨hp.1.2.one_lt.le, hp.2⟩
      have hcard : (Finset.Icc 1 (Nat.sqrt (2 * m))).card = Nat.sqrt (2 * m) := by
        rw [Nat.card_Icc]; omega
      exact Nat.pow_le_pow_right h2m_pos ((Finset.card_le_card hsub).trans hcard.le)
    · refine le_trans ?_ (primorial_le_four_pow (2 * m / 3))
      refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
      · simp only [S, Finset.mem_filter] at hp
        have hsq : 2 * m < p ^ 2 := by
          have hlt : Nat.sqrt (2 * m) < p := by omega
          have := Nat.sqrt_lt'.mp hlt
          simpa [sq] using this
        have hle1 : m.centralBinom.factorization p ≤ 1 := Nat.factorization_choose_le_one hsq
        exact (Nat.pow_le_pow_right hp.1.2.pos hle1).trans (pow_one p).le
      refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
      intro p hp _
      exact (Finset.mem_filter.mp hp).2.one_lt.le
  · let T := AllP.filter (fun p => ¬ p ≤ 2 * m / 3)
    have hT_eq : ∏ p ∈ T, f p = ∏ p ∈ T.filter (m < ·), f p := by
      symm
      refine Finset.prod_filter_of_ne fun p hp hne => ?_
      by_contra hle
      push Not at hle
      simp only [T, AllP, Finset.mem_filter] at hp
      have h3p : 2 * m < 3 * p := by omega
      have hz : m.centralBinom.factorization p = 0 :=
        Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hm hle h3p
      apply hne
      dsimp only [f]
      rw [hz, pow_zero]
    rw [hT_eq]
    have hTsub : T.filter (m < ·) ⊆ (Finset.Ioc m (2 * m)).filter Nat.Prime := by
      intro p hp
      simp only [T, AllP, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hp ⊢
      exact ⟨⟨hp.2, by omega⟩, hp.1.1.2⟩
    calc
      ∏ p ∈ T.filter (m < ·), f p
          ≤ ∏ _p ∈ T.filter (m < ·), (2 * m) :=
            Finset.prod_le_prod' fun p _ => Nat.pow_factorization_choose_le (by omega)
      _ = (2 * m) ^ (T.filter (m < ·)).card := Finset.prod_const _
      _ ≤ (2 * m) ^ ((Finset.Ioc m (2 * m)).filter Nat.Prime).card :=
            Nat.pow_le_pow_right h2m_pos (Finset.card_le_card hTsub)

private lemma central_binom_contradiction {m c e k1 k2 : ℕ}
    (hm : m ≤ 2 ^ e) (h2m : 2 * m ≤ 2 ^ e) (hk1 : Nat.sqrt (2 * m) ≤ k1) (hk2 : c ≤ k2)
    (hlow : 4 ^ m < m * m.centralBinom)
    (hup : m.centralBinom ≤ (2 * m) ^ Nat.sqrt (2 * m) * 4 ^ (2 * m / 3) * (2 * m) ^ c)
    (hsub : 2 * m / 3 ≤ m)
    (hexp : e + e * k1 + e * k2 < 2 * (m - 2 * m / 3)) :
    False := by
  have h2e_pos : 0 < 2 ^ e := Nat.pow_pos (by decide)
  have hprod :
      m * ((2 * m) ^ Nat.sqrt (2 * m) * (2 * m) ^ c) ≤ 2 ^ (e + e * k1 + e * k2) := by
    calc
      m * ((2 * m) ^ Nat.sqrt (2 * m) * (2 * m) ^ c)
          ≤ 2 ^ e * ((2 ^ e) ^ k1 * (2 ^ e) ^ k2) := by
            apply Nat.mul_le_mul hm
            apply Nat.mul_le_mul
            · exact (Nat.pow_le_pow_left h2m _).trans (Nat.pow_le_pow_right h2e_pos hk1)
            · exact (Nat.pow_le_pow_left h2m _).trans (Nat.pow_le_pow_right h2e_pos hk2)
      _ = 2 ^ (e + e * k1 + e * k2) := by
            rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, add_assoc]
  have hlt_pow : 2 ^ (e + e * k1 + e * k2) < 4 ^ (m - 2 * m / 3) := by
    have h4 : 4 ^ (m - 2 * m / 3) = 2 ^ (2 * (m - 2 * m / 3)) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [h4]
    exact Nat.pow_lt_pow_right (by norm_num) hexp
  have hcontra : m * m.centralBinom < 4 ^ m := by
    calc
      m * m.centralBinom
          ≤ m * ((2 * m) ^ Nat.sqrt (2 * m) * 4 ^ (2 * m / 3) * (2 * m) ^ c) :=
            Nat.mul_le_mul_left m hup
      _ = 4 ^ (2 * m / 3) * (m * ((2 * m) ^ Nat.sqrt (2 * m) * (2 * m) ^ c)) := by ac_rfl
      _ ≤ 4 ^ (2 * m / 3) * 2 ^ (e + e * k1 + e * k2) := Nat.mul_le_mul_left _ hprod
      _ < 4 ^ (2 * m / 3) * 4 ^ (m - 2 * m / 3) :=
            Nat.mul_lt_mul_of_pos_left hlt_pow (Nat.pow_pos (by decide))
      _ = 4 ^ m := by rw [← pow_add, Nat.add_sub_of_le hsub]
  exact lt_asymm hlow hcontra

private lemma many_primes_in_dyadic (m : ℕ) (hm : m = 10 ^ 12) :
    4000000 ≤ ((Finset.Ioc m (2 * m)).filter Nat.Prime).card := by
  by_contra hlt
  push Not at hlt
  have hsqrt : Nat.sqrt (2 * m) ≤ 1414214 := by
    have hsq : 2 * m < 1414215 ^ 2 := by rw [hm]; norm_num
    have hlt' : Nat.sqrt (2 * m) < 1414215 := Nat.sqrt_lt'.mpr hsq
    exact Nat.lt_succ_iff.mp hlt'
  exact central_binom_contradiction (m := m) (c := ((Finset.Ioc m (2 * m)).filter Nat.Prime).card)
    (e := 41) (k1 := 1414214) (k2 := 4000000)
    (by rw [hm]; norm_num) (by rw [hm]; norm_num) hsqrt hlt.le
    (Nat.four_pow_lt_mul_centralBinom m (by rw [hm]; norm_num))
    (centralBinom_le_bound m (by rw [hm]; norm_num))
    (by rw [hm]; norm_num) (by rw [hm]; norm_num)

private lemma exists_dense_window (m W : ℕ) (hm : m = 10 ^ 12) (hW : W = 250000000) :
    ∃ b < 4000,
      1000 ≤ ((Finset.Ioc (m + b * W) (m + (b + 1) * W)).filter Nat.Prime).card := by
  have h4000 : 4000 * W = m := by rw [hm, hW]; norm_num
  have hW_pos : 0 < W := by rw [hW]; norm_num
  let B : ℕ → Finset ℕ := fun b => (Finset.Ioc (m + b * W) (m + (b + 1) * W)).filter Nat.Prime
  have hcover : (Finset.Ioc m (2 * m)).filter Nat.Prime ⊆ (Finset.range 4000).biUnion B := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hq
    rw [Finset.mem_biUnion]
    refine ⟨(q - m - 1) / W, Finset.mem_range.mpr ?_, ?_⟩
    · have : q - m - 1 < 4000 * W := by omega
      exact Nat.div_lt_of_lt_mul (by linarith)
    · simp only [B, Finset.mem_filter, Finset.mem_Ioc]
      have hdiv : (q - m - 1) / W * W ≤ q - m - 1 := Nat.div_mul_le_self _ _
      have hmod : q - m - 1 < ((q - m - 1) / W + 1) * W := by
        rw [add_mul, one_mul]
        have := Nat.lt_div_mul_add (a := q - m - 1) hW_pos
        linarith
      exact ⟨⟨by omega, by omega⟩, hq.2⟩
  have hsum : 4000000 ≤ ∑ b ∈ Finset.range 4000, (B b).card := by
    calc
      4000000 ≤ ((Finset.Ioc m (2 * m)).filter Nat.Prime).card := many_primes_in_dyadic m hm
      _ ≤ ((Finset.range 4000).biUnion B).card := Finset.card_le_card hcover
      _ ≤ ∑ b ∈ Finset.range 4000, (B b).card := Finset.card_biUnion_le
  by_contra hall
  push Not at hall
  have hle : ∑ b ∈ Finset.range 4000, (B b).card ≤ ∑ _b ∈ Finset.range 4000, 999 := by
    refine Finset.sum_le_sum fun b hb => ?_
    have hlt : (B b).card < 1000 := hall b (Finset.mem_range.mp hb)
    exact Nat.lt_succ_iff.mp hlt
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hle
  omega

private lemma disproof_aux (m W N : ℕ) (hm : m = 10 ^ 12) (hW : W = 250000000) (hN : N = 10 ^ 15)
    (h : ∀ (N : ℕ) (p : Fin 1000 → ℕ) (A : (i : Fin 1000) → Finset (ZMod (p i))),
      let remaining := (Finset.Icc 1 N).filter (fun x => ∀ i, (x : ZMod (p i)) ∉ A i)
      (∀ i, (p i).Prime) →
      StrictMono p →
      (p 999) ^ 10 < N ^ 9 →
      (∀ i, (A i).card = (p i) / 2) →
      10 * remaining.card ≤ N) : False := by
  have hm_pos : 0 < m := by rw [hm]; norm_num
  have h4000W : 4000 * W = m := by rw [hm, hW]; norm_num
  have h1000W : 1000 * W = m / 4 := by rw [hm, hW]; norm_num
  have h1000m : 1000 * m = N := by rw [hm, hN]; norm_num
  have h500_2m : 500 * (2 * m) = N := by rw [hm, hN]; norm_num
  have hm_div4 : 4 ∣ m := by rw [hm]; norm_num
  have hW_div4 : 4 ∣ W := by rw [hW]; norm_num
  have hpow_bound : (2 * m) ^ 10 < N ^ 9 := by rw [hm, hN]; norm_num
  obtain ⟨b, hb, hBcard⟩ := exists_dense_window m W hm hW
  set L : ℕ := m + b * W
  have hL_ge : m ≤ L := by omega
  have hLW_le : L + W ≤ 2 * m := by
    have : (b + 1) * W ≤ 4000 * W := Nat.mul_le_mul_right W hb
    dsimp only [L]
    linarith
  have hL_div4 : 4 * (L / 4) = L := by
    have h4L : 4 ∣ L := dvd_add hm_div4 (dvd_mul_of_dvd_right hW_div4 b)
    exact Nat.mul_div_cancel' h4L
  let B := (Finset.Ioc L (L + W)).filter Nat.Prime
  have hBcard' : 1000 ≤ B.card := by
    have hEq : B = (Finset.Ioc (m + b * W) (m + (b + 1) * W)).filter Nat.Prime := by
      dsimp only [B, L]
      congr 1
      congr 1
      ring
    rw [hEq]
    exact hBcard
  obtain ⟨Q, hQsub, hQcard⟩ := Finset.exists_subset_card_eq hBcard'
  let p : Fin 1000 → ℕ := fun i => Q.orderEmbOfFin hQcard i
  have hp_mem : ∀ i, p i ∈ B := fun i => hQsub (Q.orderEmbOfFin_mem hQcard i)
  have hp_prime : ∀ i, (p i).Prime := fun i => (Finset.mem_filter.mp (hp_mem i)).2
  have hp_gt : ∀ i, L < p i := fun i => (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hp_mem i)).1).1
  have hp_le : ∀ i, p i ≤ L + W := fun i => (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hp_mem i)).1).2
  have hp_mono : StrictMono p := (Q.orderEmbOfFin hQcard).strictMono
  have hp_bound : (p 999) ^ 10 < N ^ 9 := by
    have h999 : p 999 ≤ 2 * m := (hp_le 999).trans hLW_le
    exact (Nat.pow_le_pow_left h999 10).trans_lt hpow_bound
  let bad : (i : Fin 1000) → Finset (ZMod (p i)) := fun i =>
    (Finset.Ico (-(L / 4 : ℤ)) (L / 4 : ℤ)).image (Int.cast : ℤ → ZMod (p i))
  have hexA : ∀ i : Fin 1000, ∃ s : Finset (ZMod (p i)), Disjoint s (bad i) ∧ s.card = p i / 2 := by
    intro i
    have : NeZero (p i) := ⟨(hp_prime i).ne_zero⟩
    have hcompl_ge : p i / 2 ≤ (Finset.univ \ bad i).card := by
      have hbad_card : (bad i).card ≤ L / 2 := by
        calc
          (bad i).card ≤ (Finset.Ico (-(L / 4 : ℤ)) (L / 4 : ℤ)).card := Finset.card_image_le
          _ = ((L / 4 : ℤ) - (-(L / 4 : ℤ))).toNat := Int.card_Ico _ _
          _ ≤ L / 2 := by omega
      have hcompl : (Finset.univ \ bad i).card = p i - (bad i).card := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, ZMod.card]
      have hLp : L < p i := hp_gt i
      omega
    obtain ⟨s, hs_sub, hs_card⟩ := Finset.exists_subset_card_eq hcompl_ge
    exact ⟨s, Finset.disjoint_left.mpr fun x hxs hxb => (Finset.mem_sdiff.mp (hs_sub hxs)).2 hxb,
      hs_card⟩
  let A : (i : Fin 1000) → Finset (ZMod (p i)) := fun i => Classical.choose (hexA i)
  have hA_disj : ∀ i, Disjoint (A i) (bad i) := fun i => (Classical.choose_spec (hexA i)).1
  have hA_card : ∀ i, (A i).card = p i / 2 := fun i => (Classical.choose_spec (hexA i)).2
  have hrem := h N p A hp_prime hp_mono hp_bound hA_card
  let S := (Finset.Icc 1 N).filter (fun x => x % L < L / 4)
  have hS_sub : S ⊆ (Finset.Icc 1 N).filter (fun x => ∀ i, (x : ZMod (p i)) ∉ A i) := by
    intro x hx
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hx ⊢
    refine ⟨hx.1, fun i hxA => ?_⟩
    have hx_not_bad : (x : ZMod (p i)) ∉ bad i := Finset.disjoint_left.mp (hA_disj i) hxA
    apply hx_not_bad
    let q : ℕ := x / L
    let r : ℕ := x % L
    let δ : ℕ := p i - L
    have hL_pos : 0 < L := by omega
    have hq_le : q ≤ 1000 := by
      have hmul : q * L ≤ N := by
        calc
          q * L ≤ x := Nat.div_mul_le_self x L
          _ ≤ N := hx.1.2
      have : q * m ≤ 1000 * m := (Nat.mul_le_mul_left q hL_ge).trans (by omega)
      exact Nat.le_of_mul_le_mul_right this hm_pos
    have hδ_le : δ ≤ W := by
      have := hp_le i
      omega
    have hqδ_le : q * δ ≤ L / 4 := by
      have h1 : q * δ ≤ 1000 * W := Nat.mul_le_mul hq_le hδ_le
      omega
    have hp_eq : L + δ = p i := by
      have := hp_gt i
      omega
    have hL_cast : (L : ZMod (p i)) = -(δ : ZMod (p i)) := by
      have h0 : ((L + δ : ℕ) : ZMod (p i)) = 0 := by rw [hp_eq, ZMod.natCast_self]
      push_cast at h0
      exact eq_neg_of_add_eq_zero_left h0
    let z : ℤ := (r : ℤ) - ((q * δ : ℕ) : ℤ)
    have hz_mem : z ∈ Finset.Ico (-(L / 4 : ℤ)) (L / 4 : ℤ) := by
      rw [Finset.mem_Ico]
      have hr_lt : r < L / 4 := hx.2
      omega
    have hz_cast : (z : ZMod (p i)) = (x : ZMod (p i)) := by
      have hx_eq : x = q * L + r := by
        dsimp only [q, r]
        rw [mul_comm]
        exact (Nat.div_add_mod x L).symm
      rw [hx_eq]
      dsimp only [z]
      push_cast
      rw [hL_cast]
      ring
    exact Finset.mem_image.mpr ⟨z, hz_mem, hz_cast⟩
  have hS_card : N < 10 * S.card := by
    let qmax : ℕ := N / L
    have hL_pos : 0 < L := by omega
    have hL_le_2m : L ≤ 2 * m := by omega
    have hqmax_ge : 500 ≤ qmax := by
      have h500 : 500 * L ≤ N := by
        calc
          500 * L ≤ 500 * (2 * m) := Nat.mul_le_mul_left 500 hL_le_2m
          _ = N := h500_2m
      exact (Nat.le_div_iff_mul_le hL_pos).mpr h500
    let D := Finset.Ico 1 qmax ×ˢ Finset.range (L / 4)
    let g : ℕ × ℕ → ℕ := fun qr => qr.1 * L + qr.2
    have hg_sub : D.image g ⊆ S := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨⟨q, r⟩, hqr, rfl⟩
      simp only [D, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hqr
      simp only [S, Finset.mem_filter, Finset.mem_Icc]
      have hr_lt_L : r < L := by omega
      have hg_ge : 1 ≤ q * L + r := by nlinarith
      have hg_le : q * L + r ≤ N := by
        have hq1 : q + 1 ≤ qmax := hqr.1.2
        have hqmaxL : qmax * L ≤ N := Nat.div_mul_le_self N L
        nlinarith
      have hmod : (q * L + r) % L = r := by
        rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hr_lt_L]
      exact ⟨⟨hg_ge, hg_le⟩, by simpa [g, hmod] using hqr.2⟩
    have hg_inj : Set.InjOn g (D : Set (ℕ × ℕ)) := by
      intro a ha b hb hab
      simp only [D, Finset.mem_coe, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at ha hb
      have ha_lt : a.2 < L := by omega
      have hb_lt : b.2 < L := by omega
      have hmod : (a.1 * L + a.2) % L = (b.1 * L + b.2) % L := congrArg (· % L) hab
      rw [Nat.mul_add_mod_self_right, Nat.mul_add_mod_self_right,
        Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] at hmod
      have hq_eq : a.1 = b.1 := by
        dsimp only [g] at hab
        have : a.1 * L = b.1 * L := by omega
        exact Nat.eq_of_mul_eq_mul_right hL_pos this
      exact Prod.ext hq_eq hmod
    have hcard_ge : (qmax - 1) * (L / 4) ≤ S.card := by
      have h1 : (D.image g).card = D.card := Finset.card_image_of_injOn hg_inj
      have h2 : D.card = (qmax - 1) * (L / 4) := by
        simp [D, Finset.card_product, Nat.card_Ico]
      calc
        (qmax - 1) * (L / 4) = (D.image g).card := by rw [h1, h2]
        _ ≤ S.card := Finset.card_le_card hg_sub
    have hN_lt : N < (qmax + 1) * L := by
      have := Nat.lt_div_mul_add (a := N) hL_pos
      dsimp only [qmax]
      linarith
    have hL4_pos : 0 < L / 4 := by omega
    have hq_sub : 4 * (qmax + 1) < 10 * (qmax - 1) := by omega
    calc
      N < (qmax + 1) * L := hN_lt
      _ = (qmax + 1) * (4 * (L / 4)) := congrArg ((qmax + 1) * ·) hL_div4.symm
      _ = 4 * (qmax + 1) * (L / 4) := by ring
      _ < 10 * (qmax - 1) * (L / 4) := Nat.mul_lt_mul_of_pos_right hq_sub hL4_pos
      _ = 10 * ((qmax - 1) * (L / 4)) := by ring
      _ ≤ 10 * S.card := Nat.mul_le_mul_left 10 hcard_ge
  have hS_le_rem : S.card ≤ ((Finset.Icc 1 N).filter (fun x => ∀ i, (x : ZMod (p i)) ∉ A i)).card :=
    Finset.card_le_card hS_sub
  exact Nat.not_lt_of_ge ((Nat.mul_le_mul_left 10 hS_le_rem).trans hrem) hS_card

end Green44Disproof

theorem OMA.disproof : ¬ (type_of% @Green44.green_44) := fun h =>
  Green44Disproof.disproof_aux (10 ^ 12) 250000000 (10 ^ 15) rfl rfl rfl h
