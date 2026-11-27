import FormalConjectures.OEIS.«60841»

/-!
Proof of `OeisA60841.conjecture1`: for every $n \ge 1$, the reciprocal determinant of the
$n \times n$ matrix $M_{i,j} = 1 / \operatorname{lcm}(i+1, j+1)$ is an integer if and only if
$n \in \{1, \dots, 34, 36, 38\}$.
-/

open scoped Matrix

namespace OeisA60841Proof

private lemma sum_fin_totient_dvd (n g : ℕ) (hg0 : 0 < g) (hgn : g ≤ n) :
    (∑ k : Fin n, if (k.val + 1) ∣ g then Nat.totient (k.val + 1) else 0) = g := by
  rw [← Finset.sum_filter]
  have hbij :
      (∑ k ∈ Finset.univ.filter (fun k : Fin n => (k.val + 1) ∣ g), Nat.totient (k.val + 1)) =
        ∑ d ∈ g.divisors, Nat.totient d := by
    refine Finset.sum_bij (fun k _ => k.val + 1) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact Nat.mem_divisors.mpr ⟨hk, hg0.ne'⟩
    · intro k₁ _ k₂ _ h
      exact Fin.ext (by omega)
    · intro d hd
      rw [Nat.mem_divisors] at hd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd.1 hg0
      have hdle : d ≤ g := Nat.le_of_dvd hg0 hd.1
      refine ⟨⟨d - 1, by omega⟩, ?_, by dsimp; omega⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hsub : d - 1 + 1 = d := by omega
      rw [hsub]
      exact hd.1
    · intro _ _
      rfl
  rw [hbij, Nat.sum_totient]

private def diagInv (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.diagonal fun i : Fin n => (1 : ℚ) / ((i.val + 1 : ℕ) : ℚ)

private def divMat (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i k : Fin n => if (k.val + 1) ∣ (i.val + 1) then (1 : ℚ) else 0

private def totMat (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.diagonal fun k : Fin n => (Nat.totient (k.val + 1) : ℚ)

private lemma lcmMatrix_eq_factor (n : ℕ) :
    OeisA60841.lcmMatrix n = diagInv n * (divMat n * totMat n * (divMat n)ᵀ) * diagInv n := by
  ext i j
  simp only [OeisA60841.lcmMatrix, Matrix.of_apply, diagInv, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  have hmid :
      (divMat n * totMat n * (divMat n)ᵀ) i j = (Nat.gcd (i.val + 1) (j.val + 1) : ℚ) := by
    rw [Matrix.mul_apply]
    simp only [totMat, Matrix.mul_diagonal, divMat, Matrix.transpose_apply, Matrix.of_apply]
    have hterm :
        ∀ k : Fin n,
          (if (k.val + 1) ∣ (i.val + 1) then (1 : ℚ) else 0) * (Nat.totient (k.val + 1) : ℚ) *
              (if (k.val + 1) ∣ (j.val + 1) then (1 : ℚ) else 0) =
            ((if (k.val + 1) ∣ Nat.gcd (i.val + 1) (j.val + 1) then Nat.totient (k.val + 1)
              else 0 : ℕ) : ℚ) := by
      intro k
      by_cases hi : (k.val + 1) ∣ (i.val + 1) <;> by_cases hj : (k.val + 1) ∣ (j.val + 1)
      · have hg : (k.val + 1) ∣ Nat.gcd (i.val + 1) (j.val + 1) := Nat.dvd_gcd hi hj
        simp [hi, hj, hg]
      · have hg : ¬ (k.val + 1) ∣ Nat.gcd (i.val + 1) (j.val + 1) := fun h =>
          hj (dvd_trans h (Nat.gcd_dvd_right _ _))
        simp [hi, hj, hg]
      · have hg : ¬ (k.val + 1) ∣ Nat.gcd (i.val + 1) (j.val + 1) := fun h =>
          hi (dvd_trans h (Nat.gcd_dvd_left _ _))
        simp [hi, hj, hg]
      · have hg : ¬ (k.val + 1) ∣ Nat.gcd (i.val + 1) (j.val + 1) := fun h =>
          hi (dvd_trans h (Nat.gcd_dvd_left _ _))
        simp [hi, hj, hg]
    simp_rw [hterm]
    rw [← Nat.cast_sum]
    have hg0 : 0 < Nat.gcd (i.val + 1) (j.val + 1) :=
      Nat.gcd_pos_of_pos_left _ (Nat.succ_pos _)
    have hgn : Nat.gcd (i.val + 1) (j.val + 1) ≤ n :=
      le_trans (Nat.gcd_le_left _ (Nat.succ_pos _)) i.isLt
    exact_mod_cast sum_fin_totient_dvd n (Nat.gcd (i.val + 1) (j.val + 1)) hg0 hgn
  rw [hmid]
  have ha : ((i.val + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hb : ((j.val + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hl : (Nat.lcm (i.val + 1) (j.val + 1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.lcm_ne_zero (Nat.succ_ne_zero _) (Nat.succ_ne_zero _)
  have hgl : (Nat.gcd (i.val + 1) (j.val + 1) : ℚ) * (Nat.lcm (i.val + 1) (j.val + 1) : ℚ) =
      ((i.val + 1 : ℕ) : ℚ) * ((j.val + 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.gcd_mul_lcm (i.val + 1) (j.val + 1)
  field_simp
  linarith

private lemma divMat_isLowerTriangular (n : ℕ) : (divMat n).IsLowerTriangular := by
  intro i j hij
  have hlt : i.val < j.val := hij
  simp only [divMat, Matrix.of_apply]
  have hndvd : ¬ (j.val + 1) ∣ (i.val + 1) := fun h => by
    have := Nat.le_of_dvd (Nat.succ_pos _) h
    omega
  simp [hndvd]

private lemma divMat_det (n : ℕ) : (divMat n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (divMat_isLowerTriangular n)]
  apply Finset.prod_eq_one
  intro i _
  simp [divMat]

private def myGcd : ℕ → ℕ → ℕ → ℕ
  | 0, a, _ => a
  | fuel + 1, a, b => if b = 0 then a else myGcd fuel b (a % b)

private lemma myGcd_eq_gcd : ∀ fuel a b : ℕ, b < fuel → myGcd fuel a b = Nat.gcd a b
  | 0, _, b, h => by omega
  | fuel + 1, a, b, h => by
    unfold myGcd
    split_ifs with hb
    · subst hb; simp
    · have hlt : a % b < fuel := lt_of_lt_of_le (Nat.mod_lt a (Nat.pos_of_ne_zero hb)) (by omega)
      rw [myGcd_eq_gcd fuel b (a % b) hlt, Nat.gcd_comm b (a % b), ← Nat.gcd_rec, Nat.gcd_comm]

private def myTotientAux (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => myTotientAux n k + (if myGcd (n + 1) n k == 1 then 1 else 0)

private def myTotient (n : ℕ) : ℕ := myTotientAux n n

private lemma myTotientAux_eq (n : ℕ) :
    ∀ m : ℕ, m ≤ n → myTotientAux n m = ∑ k ∈ Finset.range m, if n.Coprime k then 1 else 0
  | 0, _ => by simp [myTotientAux]
  | m + 1, hm => by
    rw [myTotientAux, myTotientAux_eq n m (by omega), Finset.sum_range_succ]
    congr 1
    rw [myGcd_eq_gcd (n + 1) n m (by omega)]
    change (if (Nat.gcd n m == 1) = true then 1 else 0) = if Nat.gcd n m = 1 then 1 else 0
    simp [beq_iff_eq]

private lemma myTotient_eq (n : ℕ) : myTotient n = Nat.totient n := by
  rw [myTotient, myTotientAux_eq n n le_rfl, Nat.totient, Finset.card_filter]

private def numProd : ℕ → ℕ
  | 0 => 1
  | n + 1 => numProd n * (n + 1) ^ 2

private def denProd : ℕ → ℕ
  | 0 => 1
  | n + 1 => denProd n * myTotient (n + 1)

private lemma numProd_pos (n : ℕ) : 0 < numProd n := by
  induction n with
  | zero => simp [numProd]
  | succ m ih => exact Nat.mul_pos ih (by positivity)

private lemma denProd_pos (n : ℕ) : 0 < denProd n := by
  induction n with
  | zero => simp [denProd]
  | succ m ih =>
    rw [denProd, myTotient_eq]
    exact Nat.mul_pos ih (Nat.totient_pos.mpr (Nat.succ_pos _))

private lemma det_inv_eq_div (n : ℕ) :
    ((OeisA60841.lcmMatrix n).det)⁻¹ = (numProd n : ℚ) / (denProd n : ℚ) := by
  have hdet : (OeisA60841.lcmMatrix n).det =
      ∏ i : Fin n, ((Nat.totient (i.val + 1) : ℚ) / (((i.val + 1 : ℕ) : ℚ) ^ 2)) := by
    rw [lcmMatrix_eq_factor, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose, divMat_det, diagInv, totMat, Matrix.det_diagonal, Matrix.det_diagonal]
    simp only [mul_one, one_mul]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    ring
  rw [hdet, ← Finset.prod_inv_distrib]
  have hinv :
      (∏ i : Fin n, ((Nat.totient (i.val + 1) : ℚ) / (((i.val + 1 : ℕ) : ℚ) ^ 2))⁻¹) =
        ∏ i : Fin n, ((((i.val + 1 : ℕ) : ℚ) ^ 2) / (Nat.totient (i.val + 1) : ℚ)) := by
    refine Finset.prod_congr rfl fun i _ => by rw [inv_div]
  rw [hinv]
  have hprod : ∀ m : ℕ,
      (∏ i : Fin m, ((((i.val + 1 : ℕ) : ℚ) ^ 2) / (Nat.totient (i.val + 1) : ℚ))) =
        (numProd m : ℚ) / (denProd m : ℚ) := by
    intro m
    induction m with
    | zero => simp [numProd, denProd]
    | succ k ih =>
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih, numProd, denProd, myTotient_eq]
      push_cast
      ring
  exact hprod n

private lemma div_den_eq_one_iff_dvd {a b : ℕ} (hb : b ≠ 0) :
    ((a : ℚ) / (b : ℚ)).den = 1 ↔ b ∣ a := by
  constructor
  · intro hden
    set q : ℚ := (a : ℚ) / (b : ℚ)
    have hqnn : 0 ≤ q := by positivity
    have hqnum : 0 ≤ q.num := Rat.num_nonneg.mpr hqnn
    have hqeq : q = ((q.num.toNat : ℕ) : ℚ) := by
      have h1 : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
      rw [h1, hden]
      simp only [Nat.cast_one, div_one]
      exact_mod_cast (Int.toNat_of_nonneg hqnum).symm
    have hmul : (a : ℚ) = ((q.num.toNat * b : ℕ) : ℚ) := by
      have hbQ : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb
      have hqdef : (a : ℚ) = q * (b : ℚ) := by
        dsimp [q]
        field_simp
      rw [hqdef, hqeq]
      push_cast
      rfl
    have hnat : a = q.num.toNat * b := Nat.cast_injective hmul
    exact ⟨q.num.toNat, by rw [hnat, mul_comm]⟩
  · rintro ⟨c, rfl⟩
    have hbQ : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb
    have hdiv : ((b * c : ℕ) : ℚ) / (b : ℚ) = (c : ℚ) := by
      push_cast
      field_simp
    rw [hdiv]
    simp

private lemma det_inv_den_eq_one_iff (n : ℕ) :
    ((OeisA60841.lcmMatrix n).det)⁻¹.den = 1 ↔ denProd n ∣ numProd n := by
  rw [det_inv_eq_div, div_den_eq_one_iff_dvd (denProd_pos n).ne']

private lemma not_dvd_of_v2_lt {n : ℕ}
    (hlt : (numProd n).factorization 2 < (denProd n).factorization 2) :
    ¬ (denProd n ∣ numProd n) := by
  intro hdvd
  have hle : (denProd n).factorization 2 ≤ (numProd n).factorization 2 :=
    (Nat.factorization_le_iff_dvd (denProd_pos n).ne' (numProd_pos n).ne').mpr hdvd 2
  omega

private def v2Aux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n % 2 = 0 then 1 + v2Aux fuel (n / 2) else 0

private def v2 (n : ℕ) : ℕ := v2Aux n n

private lemma v2Aux_eq_factorization :
    ∀ fuel n : ℕ, n ≠ 0 → n ≤ fuel → v2Aux fuel n = n.factorization 2
  | 0, n, hn, hle => by omega
  | fuel + 1, n, hn, hle => by
    unfold v2Aux
    split_ifs with hmod
    · have hhalf0 : n / 2 ≠ 0 := by omega
      have hhalfle : n / 2 ≤ fuel := by omega
      have ih := v2Aux_eq_factorization fuel (n / 2) hhalf0 hhalfle
      have hmul : n = 2 * (n / 2) := by omega
      conv_rhs => rw [hmul]
      rw [Nat.factorization_mul (by decide) hhalf0, Finsupp.add_apply,
        Nat.Prime.factorization_self Nat.prime_two, ih]
    · have hndvd : ¬ 2 ∣ n := by omega
      exact (Nat.factorization_eq_zero_of_not_dvd hndvd).symm

private lemma v2_eq_factorization {n : ℕ} (hn : n ≠ 0) : v2 n = n.factorization 2 :=
  v2Aux_eq_factorization n n hn le_rfl

private def v2NumSum : ℕ → ℕ
  | 0 => 0
  | n + 1 => v2NumSum n + 2 * v2 (n + 1)

private def v2DenSum : ℕ → ℕ
  | 0 => 0
  | n + 1 => v2DenSum n + v2 (myTotient (n + 1))

private lemma numProd_factorization_two (n : ℕ) :
    (numProd n).factorization 2 = v2NumSum n := by
  induction n with
  | zero => simp [numProd, v2NumSum]
  | succ m ih =>
    rw [numProd, v2NumSum, Nat.factorization_mul (numProd_pos m).ne' (by positivity),
      Finsupp.add_apply, ih, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      v2_eq_factorization (Nat.succ_ne_zero m)]

private lemma denProd_factorization_two (n : ℕ) :
    (denProd n).factorization 2 = v2DenSum n := by
  induction n with
  | zero => simp [denProd, v2DenSum]
  | succ m ih =>
    have ht0 : Nat.totient (m + 1) ≠ 0 := (Nat.totient_pos.mpr (Nat.succ_pos m)).ne'
    rw [denProd, v2DenSum, myTotient_eq, Nat.factorization_mul (denProd_pos m).ne' ht0,
      Finsupp.add_apply, ih, v2_eq_factorization ht0]

private def checkSmallAux : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => true
  | fuel + 1, k, num, den =>
    let k' := k + 1
    let num' := num * (k' * k')
    let den' := den * myTotient k'
    ((num' % den' == 0) == (k' ≤ 34 || k' == 36 || k' == 38)) &&
      checkSmallAux fuel k' num' den'

private lemma checkSmallAux_sound :
    ∀ fuel k : ℕ, checkSmallAux fuel k (numProd k) (denProd k) = true →
      ∀ n : ℕ, k < n → n ≤ k + fuel → (denProd n ∣ numProd n ↔ (n ≤ 34 ∨ n = 36 ∨ n = 38))
  | 0, k, _, n, hlt, hle => by omega
  | fuel + 1, k, hchk, n, hlt, hle => by
    simp only [checkSmallAux, Bool.and_eq_true] at hchk
    rcases hchk with ⟨hnow, hrest⟩
    have hnum : numProd k * ((k + 1) * (k + 1)) = numProd (k + 1) := by
      simp [numProd, sq]
    have hden : denProd k * myTotient (k + 1) = denProd (k + 1) := rfl
    rw [hnum, hden] at hnow hrest
    by_cases hn : n = k + 1
    · subst hn
      rw [Nat.dvd_iff_mod_eq_zero]
      have h1 := beq_iff_eq.mp hnow
      have h2 := congrArg (· = true) h1
      simp only [beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq, eq_iff_iff] at h2
      tauto
    · exact checkSmallAux_sound fuel (k + 1) hrest n (by omega) (by omega)

private lemma small_cases (n : ℕ) (hn1 : 1 ≤ n) (hn38 : n ≤ 38) :
    denProd n ∣ numProd n ↔ (n ≤ 34 ∨ n = 36 ∨ n = 38) := by
  have hchk : checkSmallAux 38 0 (numProd 0) (denProd 0) = true := by decide +kernel
  exact checkSmallAux_sound 38 0 hchk n (by omega) (by omega)

private def checkMidAux : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => true
  | fuel + 1, k, sn, sd =>
    let k' := k + 1
    let sn' := sn + 2 * v2 k'
    let sd' := sd + v2 (myTotient k')
    (k' < 39 || sn' < sd') && checkMidAux fuel k' sn' sd'

private lemma checkMidAux_sound :
    ∀ fuel k : ℕ, checkMidAux fuel k (v2NumSum k) (v2DenSum k) = true →
      ∀ n : ℕ, k < n → n ≤ k + fuel → 39 ≤ n → v2NumSum n < v2DenSum n
  | 0, k, _, n, hlt, hle, _ => by omega
  | fuel + 1, k, hchk, n, hlt, hle, h39 => by
    simp only [checkMidAux, Bool.and_eq_true] at hchk
    rcases hchk with ⟨hnow, hrest⟩
    change (decide (k + 1 < 39) || decide (v2NumSum (k + 1) < v2DenSum (k + 1))) = true at hnow
    change checkMidAux fuel (k + 1) (v2NumSum (k + 1)) (v2DenSum (k + 1)) = true at hrest
    by_cases hn : n = k + 1
    · subst hn
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hnow
      omega
    · exact checkMidAux_sound fuel (k + 1) hrest n (by omega) (by omega) h39

private lemma mid_cases (n : ℕ) (hn39 : 39 ≤ n) (hn84 : n ≤ 84) :
    ¬ (denProd n ∣ numProd n) := by
  have hchk : checkMidAux 84 0 (v2NumSum 0) (v2DenSum 0) = true := by decide +kernel
  have hlt := checkMidAux_sound 84 0 hchk n (by omega) (by omega) hn39
  exact not_dvd_of_v2_lt (by rw [numProd_factorization_two, denProd_factorization_two]; exact hlt)

private def v2SingleSum : ℕ → ℕ
  | 0 => 0
  | n + 1 => v2SingleSum n + (n + 1).factorization 2

private lemma v2NumSum_eq_two_mul (n : ℕ) : v2NumSum n = 2 * v2SingleSum n := by
  induction n with
  | zero => simp [v2NumSum, v2SingleSum]
  | succ m ih =>
    rw [v2NumSum, v2SingleSum, ih, v2_eq_factorization (Nat.succ_ne_zero m)]
    ring

private lemma v2SingleSum_eq (n : ℕ) : v2SingleSum n = n / 2 + v2SingleSum (n / 2) := by
  induction n with
  | zero => simp [v2SingleSum]
  | succ m ih =>
    rw [v2SingleSum]
    by_cases hpar : (m + 1) % 2 = 0
    · have hhalf : (m + 1) / 2 = m / 2 + 1 := by omega
      have hmul : m + 1 = 2 * ((m + 1) / 2) := by omega
      have hpos : (m + 1) / 2 ≠ 0 := by omega
      have hfac : (m + 1).factorization 2 = 1 + ((m + 1) / 2).factorization 2 := by
        conv_lhs => rw [hmul]
        rw [Nat.factorization_mul (by decide) hpos, Finsupp.add_apply,
          Nat.Prime.factorization_self Nat.prime_two]
      rw [ih, hfac, hhalf, v2SingleSum]
      omega
    · have hhalf : (m + 1) / 2 = m / 2 := by omega
      have hndvd : ¬ 2 ∣ (m + 1) := by omega
      have hfac : (m + 1).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hndvd
      rw [ih, hfac, hhalf]
      omega

private lemma v2SingleSum_lt (n : ℕ) (hn : 1 ≤ n) : v2SingleSum n < n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [v2SingleSum_eq]
    by_cases h2 : n < 2
    · have hn1 : n = 1 := by omega
      subst hn1
      simp [v2SingleSum]
    · have hhalf1 : 1 ≤ n / 2 := by omega
      have hhalflt : n / 2 < n := by omega
      have hrec := ih (n / 2) hhalflt hhalf1
      omega

private lemma totient_factorization_two_eq {k : ℕ} (hk : k ≠ 0) :
    (Nat.totient k).factorization 2 + (if 2 ∣ k then 1 else 0) =
      k.factorization 2 + ∑ p ∈ k.primeFactors, (p - 1).factorization 2 := by
  have h1 := Nat.totient_mul_prod_primeFactors k
  have hphi0 : Nat.totient k ≠ 0 := (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hk)).ne'
  have hp0 : ∀ p ∈ k.primeFactors, p ≠ 0 := fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hp10 : ∀ p ∈ k.primeFactors, p - 1 ≠ 0 := fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hprod_p0 : ∏ p ∈ k.primeFactors, p ≠ 0 := Finset.prod_ne_zero_iff.mpr hp0
  have hprod_p10 : ∏ p ∈ k.primeFactors, (p - 1) ≠ 0 := Finset.prod_ne_zero_iff.mpr hp10
  have hfac := congrArg (fun x => x.factorization 2) h1
  rw [Nat.factorization_mul hphi0 hprod_p0, Nat.factorization_mul hk hprod_p10,
    Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_prod hp0, Nat.factorization_prod hp10,
    Finsupp.finsetSum_apply, Finsupp.finsetSum_apply] at hfac
  have hsum2 : (∑ p ∈ k.primeFactors, p.factorization 2) = if 2 ∣ k then 1 else 0 := by
    have hterm : ∀ p ∈ k.primeFactors, p.factorization 2 = if p = 2 then 1 else 0 := by
      intro p hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      by_cases hp2 : p = 2
      · subst hp2; simp [Nat.Prime.factorization_self Nat.prime_two]
      · simp only [hp2, ↓reduceIte]
        exact Nat.factorization_eq_zero_of_not_dvd fun h =>
          hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpr).mp h).symm
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    by_cases h2k : 2 ∣ k
    · have hmem : 2 ∈ k.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2k, hk⟩
      simp [h2k, hmem]
    · have hmem : 2 ∉ k.primeFactors := fun h => h2k (Nat.dvd_of_mem_primeFactors h)
      simp [h2k, hmem]
  rw [hsum2] at hfac
  exact hfac

private def tenPrimes : Finset ℕ := {3, 5, 7, 11, 13, 17, 19, 29, 37, 41}

private lemma mem_tenPrimes_prime {p : ℕ} (hp : p ∈ tenPrimes) : p.Prime := by
  simp only [tenPrimes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private lemma totient_factorization_two_lower {k : ℕ} (hk : k ≠ 0) :
    k.factorization 2 + ∑ p ∈ tenPrimes, (if p ∣ k then (p - 1).factorization 2 else 0) ≤
      (Nat.totient k).factorization 2 + (if 2 ∣ k then 1 else 0) := by
  rw [totient_factorization_two_eq hk]
  apply Nat.add_le_add_left
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset
  intro p hp
  simp only [Finset.mem_filter] at hp
  exact Nat.mem_primeFactors.mpr ⟨mem_tenPrimes_prime hp.1, hp.2, hk⟩

private def divCount (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => divCount d n + (if d ∣ (n + 1) then 1 else 0)

private lemma divCount_eq_div (d n : ℕ) (_hd : 0 < d) : divCount d n = n / d := by
  induction n with
  | zero => simp [divCount]
  | succ m ih =>
    rw [divCount, ih, Nat.succ_div]

private lemma v2_sum_lower (n : ℕ) :
    v2SingleSum n + ∑ p ∈ tenPrimes, (p - 1).factorization 2 * (n / p) ≤
      v2DenSum n + n / 2 := by
  have h1 : ∀ m : ℕ,
      v2SingleSum m + ∑ p ∈ tenPrimes, (p - 1).factorization 2 * divCount p m ≤
        v2DenSum m + divCount 2 m := by
    intro m
    induction m with
    | zero => simp [v2SingleSum, v2DenSum, divCount]
    | succ k ih =>
      have hk : k + 1 ≠ 0 := Nat.succ_ne_zero k
      have ht0 : Nat.totient (k + 1) ≠ 0 := (Nat.totient_pos.mpr (Nat.succ_pos k)).ne'
      have hstep := totient_factorization_two_lower hk
      rw [v2SingleSum, v2DenSum, myTotient_eq, divCount, v2_eq_factorization ht0]
      have hsum :
          ∑ p ∈ tenPrimes, (p - 1).factorization 2 * divCount p (k + 1) =
            (∑ p ∈ tenPrimes, (p - 1).factorization 2 * divCount p k) +
              ∑ p ∈ tenPrimes, (if p ∣ (k + 1) then (p - 1).factorization 2 else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [divCount, mul_add]
        split_ifs <;> ring
      rw [hsum]
      omega
  have h := h1 n
  rw [divCount_eq_div 2 n (by decide)] at h
  have heq :
      ∑ p ∈ tenPrimes, (p - 1).factorization 2 * divCount p n =
        ∑ p ∈ tenPrimes, (p - 1).factorization 2 * (n / p) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [divCount_eq_div p n (mem_tenPrimes_prime hp).pos]
  rw [heq] at h
  exact h

private def rhsBound (n : ℕ) : ℕ :=
  n / 3 + 2 * (n / 5) + n / 7 + n / 11 + 2 * (n / 13) +
    4 * (n / 17) + n / 19 + 2 * (n / 29) + 2 * (n / 37) + 3 * (n / 41)

private lemma tenPrimes_sum_eq (n : ℕ) :
    (∑ p ∈ tenPrimes, (p - 1).factorization 2 * (n / p)) = rhsBound n := by
  have f2 : (2 : ℕ).factorization 2 = 1 := by
    simpa using Nat.Prime.factorization_self Nat.prime_two
  have f4 : (4 : ℕ).factorization 2 = 2 := by
    have : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [this, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, f2]
  have f6 : (6 : ℕ).factorization 2 = 1 := by
    have : (6 : ℕ) = 2 * 3 := by norm_num
    rw [this, Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply, f2,
      Nat.factorization_eq_zero_of_not_dvd (by decide)]
  have f10 : (10 : ℕ).factorization 2 = 1 := by
    have : (10 : ℕ) = 2 * 5 := by norm_num
    rw [this, Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply, f2,
      Nat.factorization_eq_zero_of_not_dvd (by decide)]
  have f12 : (12 : ℕ).factorization 2 = 2 := by
    have : (12 : ℕ) = 4 * 3 := by norm_num
    rw [this, Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply, f4,
      Nat.factorization_eq_zero_of_not_dvd (by decide)]
  have f16 : (16 : ℕ).factorization 2 = 4 := by
    have : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [this, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, f2]
  have f18 : (18 : ℕ).factorization 2 = 1 := by
    have : (18 : ℕ) = 2 * 9 := by norm_num
    rw [this, Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply, f2,
      Nat.factorization_eq_zero_of_not_dvd (by decide)]
  have f28 : (28 : ℕ).factorization 2 = 2 := by
    have : (28 : ℕ) = 4 * 7 := by norm_num
    rw [this, Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply, f4,
      Nat.factorization_eq_zero_of_not_dvd (by decide)]
  have f36 : (36 : ℕ).factorization 2 = 2 := by
    have : (36 : ℕ) = 4 * 9 := by norm_num
    rw [this, Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply, f4,
      Nat.factorization_eq_zero_of_not_dvd (by decide)]
  have f40 : (40 : ℕ).factorization 2 = 3 := by
    have : (40 : ℕ) = 2 ^ 3 * 5 := by norm_num
    rw [this, Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, f2,
      Nat.factorization_eq_zero_of_not_dvd (by decide)]
  unfold tenPrimes
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  change (2 : ℕ).factorization 2 * (n / 3) +
      ((4 : ℕ).factorization 2 * (n / 5) +
      ((6 : ℕ).factorization 2 * (n / 7) +
      ((10 : ℕ).factorization 2 * (n / 11) +
      ((12 : ℕ).factorization 2 * (n / 13) +
      ((16 : ℕ).factorization 2 * (n / 17) +
      ((18 : ℕ).factorization 2 * (n / 19) +
      ((28 : ℕ).factorization 2 * (n / 29) +
      ((36 : ℕ).factorization 2 * (n / 37) +
      (40 : ℕ).factorization 2 * (n / 41))))))))) = rhsBound n
  rw [f2, f4, f6, f10, f12, f16, f18, f28, f36, f40]
  unfold rhsBound
  ring

private lemma linear_bound_ge_166 (n : ℕ) (hn : 166 ≤ n) : n + n / 2 ≤ rhsBound n := by
  unfold rhsBound
  have h2 : 2 * (n / 2) ≤ n := by omega
  have h3 : n ≤ 3 * (n / 3) + 2 := by omega
  have h5 : n ≤ 5 * (n / 5) + 4 := by omega
  have h7 : n ≤ 7 * (n / 7) + 6 := by omega
  have h11 : n ≤ 11 * (n / 11) + 10 := by omega
  have h13 : n ≤ 13 * (n / 13) + 12 := by omega
  have h17 : n ≤ 17 * (n / 17) + 16 := by omega
  have h19 : n ≤ 19 * (n / 19) + 18 := by omega
  have h29 : n ≤ 29 * (n / 29) + 28 := by omega
  have h37 : n ≤ 37 * (n / 37) + 36 := by omega
  have h41 : n ≤ 41 * (n / 41) + 40 := by omega
  have w3 := Nat.mul_le_mul_left 142239487390 h3
  have w5 := Nat.mul_le_mul_left 170687384868 h5
  have w7 := Nat.mul_le_mul_left 60959780310 h7
  have w11 := Nat.mul_le_mul_left 38792587470 h11
  have w13 := Nat.mul_le_mul_left 65648994180 h13
  have w17 := Nat.mul_le_mul_left 100404344040 h17
  have w19 := Nat.mul_le_mul_left 22458866430 h19
  have w29 := Nat.mul_le_mul_left 29428859460 h29
  have w37 := Nat.mul_le_mul_left 23065862820 h37
  have w41 := Nat.mul_le_mul_left 31223302110 h41
  linarith

private def checkLinearAux : ℕ → ℕ → Bool
  | 0, _ => true
  | fuel + 1, k => (k + k / 2 ≤ rhsBound k) && checkLinearAux fuel (k + 1)

private lemma checkLinearAux_sound :
    ∀ fuel k : ℕ, checkLinearAux fuel k = true →
      ∀ n : ℕ, k ≤ n → n < k + fuel → n + n / 2 ≤ rhsBound n
  | 0, k, _, n, h1, h2 => by omega
  | fuel + 1, k, hchk, n, h1, h2 => by
    simp only [checkLinearAux, Bool.and_eq_true, decide_eq_true_eq] at hchk
    by_cases hn : n = k
    · subst hn; exact hchk.1
    · exact checkLinearAux_sound fuel (k + 1) hchk.2 n (by omega) (by omega)

private lemma linear_bound_ge_85 (n : ℕ) (hn : 85 ≤ n) : n + n / 2 ≤ rhsBound n := by
  by_cases h166 : 166 ≤ n
  · exact linear_bound_ge_166 n h166
  · have hchk : checkLinearAux 81 85 = true := by decide +kernel
    exact checkLinearAux_sound 81 85 hchk n hn (by omega)

private lemma large_cases (n : ℕ) (hn85 : 85 ≤ n) : ¬ (denProd n ∣ numProd n) := by
  have h1 := v2_sum_lower n
  rw [tenPrimes_sum_eq] at h1
  have h2 := linear_bound_ge_85 n hn85
  have h3 := v2SingleSum_lt n (by omega)
  have h4 : v2NumSum n < v2DenSum n := by
    rw [v2NumSum_eq_two_mul]
    omega
  exact not_dvd_of_v2_lt (by rw [numProd_factorization_two, denProd_factorization_two]; exact h4)

end OeisA60841Proof

theorem OMA.solution : type_of% @OeisA60841.conjecture1 := by
  intro n hn1
  rw [OeisA60841Proof.det_inv_den_eq_one_iff]
  have hmem : n ∈ OeisA60841.integerDetN ↔ (n ≤ 34 ∨ n = 36 ∨ n = 38) := by
    simp only [OeisA60841.integerDetN, Set.mem_union, Set.mem_Icc, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    omega
  rw [hmem]
  by_cases h38 : n ≤ 38
  · exact OeisA60841Proof.small_cases n hn1 h38
  · have hnot : ¬ (n ≤ 34 ∨ n = 36 ∨ n = 38) := by omega
    have hne : ¬ (OeisA60841Proof.denProd n ∣ OeisA60841Proof.numProd n) := by
      by_cases h84 : n ≤ 84
      · exact OeisA60841Proof.mid_cases n (by omega) h84
      · exact OeisA60841Proof.large_cases n (by omega)
    exact ⟨fun h => absurd h hne, fun h => absurd h hnot⟩
