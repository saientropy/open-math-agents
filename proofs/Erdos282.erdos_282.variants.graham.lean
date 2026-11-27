import FormalConjectures.ErdosProblems.«282»

/-!
Disproof of `Erdos282.erdos_282.variants.graham` using the counterexample
`x = 1 / 119`, `a = 1`, `d = 3`.
-/

namespace OMAErdos282Graham

open Filter Erdos282

/-- State invariant at the start of each 6-step block: `x = 1 / D` with `A` containing
all integers `≥ D` congruent to `1 (mod 3)`, and `D` satisfying minimal prime-power
congruences modulo `2`, `3`, `5`/`25`, and `7`. -/
def Good (A : Set ℕ) (D : ℕ) : Prop :=
  (∀ m ∈ A, m % 3 = 1) ∧
  (∀ m, m % 3 = 1 → D ≤ m → m ∈ A) ∧
  D % 2 = 1 ∧
  D % 3 = 2 ∧
  (D % 5 = 4 ∨ D % 25 = 7) ∧
  D % 7 = 0

lemma sInf_eq_step {A : Set ℕ} {r D n : ℕ}
    (hr : 0 < r)
    (hA_sub : ∀ m ∈ A, m % 3 = 1)
    (hA_ge : ∀ m, m % 3 = 1 → n ≤ m → m ∈ A)
    (hn3 : n % 3 = 1)
    (hstep : r * n = D + r + 1) :
    sInf { m : ℕ | m ∈ A ∧ 1 / ((r : ℚ) / (D : ℚ)) ≤ (m : ℚ) } = n := by
  have hrq : (0 : ℚ) < r := Nat.cast_pos.mpr hr
  have hiff : ∀ m : ℕ, 1 / ((r : ℚ) / (D : ℚ)) ≤ (m : ℚ) ↔ D ≤ r * m := by
    intro m
    rw [one_div_div, div_le_iff₀ hrq]
    have : ((D : ℚ) ≤ (m : ℚ) * (r : ℚ)) ↔ D ≤ m * r := by exact_mod_cast Iff.rfl
    rw [this, mul_comm]
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨hA_ge n hn3 le_rfl, (hiff n).mpr ?_⟩
    omega
  · intro m ⟨hmA, hle⟩
    have hm3 : m % 3 = 1 := hA_sub m hmA
    have hrm : D ≤ r * m := (hiff m).mp hle
    by_contra hlt
    have hlt' : m < n := Nat.lt_of_not_ge hlt
    have hgap : m + 3 ≤ n := by omega
    have hmul : r * (m + 3) ≤ r * n := Nat.mul_le_mul_left r hgap
    rw [Nat.mul_add] at hmul
    omega

lemma greedy_step_zero {A : Set ℕ} {r D n : ℕ}
    (hr : 0 < r) (hD : 0 < D) (hn : 0 < n)
    (hA_sub : ∀ m ∈ A, m % 3 = 1)
    (hA_ge : ∀ m, m % 3 = 1 → n ≤ m → m ∈ A)
    (hn3 : n % 3 = 1)
    (hstep : r * n = D + r + 1) :
    greedyUnitFractionRem A ((r : ℚ) / (D : ℚ)) 0 = ((r + 1 : ℕ) : ℚ) / ((D * n : ℕ) : ℚ) := by
  have hpos : ¬ ((r : ℚ) / (D : ℚ) ≤ 0) :=
    not_le.mpr (div_pos (Nat.cast_pos.mpr hr) (Nat.cast_pos.mpr hD))
  rw [greedyUnitFractionRem, if_neg hpos]
  dsimp only
  rw [sInf_eq_step hr hA_sub hA_ge hn3 hstep]
  have hDq : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hstepq : (r : ℚ) * (n : ℚ) = (D : ℚ) + (r : ℚ) + 1 := by exact_mod_cast hstep
  push_cast
  field_simp [hDq, hnq]
  linarith

lemma greedy_step_succ {A : Set ℕ} {r D n : ℕ}
    (hr : 0 < r) (hD : 0 < D) (hn : 0 < n)
    (hA_sub : ∀ m ∈ A, m % 3 = 1)
    (hA_ge : ∀ m, m % 3 = 1 → n ≤ m → m ∈ A)
    (hn3 : n % 3 = 1)
    (hstep : r * n = D + r + 1)
    (t : ℕ) :
    greedyUnitFractionRem A ((r : ℚ) / (D : ℚ)) (t + 1) =
      greedyUnitFractionRem (A \ {n}) (((r + 1 : ℕ) : ℚ) / ((D * n : ℕ) : ℚ)) t := by
  have hpos : ¬ ((r : ℚ) / (D : ℚ) ≤ 0) :=
    not_le.mpr (div_pos (Nat.cast_pos.mpr hr) (Nat.cast_pos.mpr hD))
  rw [greedyUnitFractionRem, if_neg hpos]
  dsimp only
  rw [sInf_eq_step hr hA_sub hA_ge hn3 hstep]
  have hDq : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hstepq : (r : ℚ) * (n : ℚ) = (D : ℚ) + (r : ℚ) + 1 := by exact_mod_cast hstep
  have hrem : (r : ℚ) / (D : ℚ) - 1 / (n : ℚ) = ((r + 1 : ℕ) : ℚ) / ((D * n : ℕ) : ℚ) := by
    push_cast
    field_simp [hDq, hnq]
    linarith
  rw [hrem]

lemma mul_mod_eq {a b m ra rb : ℕ} (ha : a % m = ra) (hb : b % m = rb) :
    (a * b) % m = (ra * rb) % m := by
  rw [Nat.mul_mod, ha, hb]

lemma mod4_of_odd_mul_add2 {D : ℕ} (h : D % 2 = 1) : (D * (D + 2)) % 4 = 3 := by
  have h4 : D % 4 = 1 ∨ D % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · rw [mul_mod_eq h4 (by omega : (D + 2) % 4 = 3)]
  · rw [mul_mod_eq h4 (by omega : (D + 2) % 4 = 1)]

lemma mod9_of_mod3_mul_add2 {D : ℕ} (h : D % 3 = 2) : (D * (D + 2)) % 9 = 8 := by
  have h9 : D % 9 = 2 ∨ D % 9 = 5 ∨ D % 9 = 8 := by omega
  rcases h9 with h9 | h9 | h9
  · rw [mul_mod_eq h9 (by omega : (D + 2) % 9 = 4)]
  · rw [mul_mod_eq h9 (by omega : (D + 2) % 9 = 7)]
  · rw [mul_mod_eq h9 (by omega : (D + 2) % 9 = 1)]

lemma mod8_of_odd_mul_add4 {D : ℕ} (h : D % 2 = 1) : (D * (D + 4)) % 8 = 5 := by
  have h8 : D % 8 = 1 ∨ D % 8 = 3 ∨ D % 8 = 5 ∨ D % 8 = 7 := by omega
  rcases h8 with h8 | h8 | h8 | h8
  · rw [mul_mod_eq h8 (by omega : (D + 4) % 8 = 5)]
  · rw [mul_mod_eq h8 (by omega : (D + 4) % 8 = 7)]
  · rw [mul_mod_eq h8 (by omega : (D + 4) % 8 = 1)]
  · rw [mul_mod_eq h8 (by omega : (D + 4) % 8 = 3)]

lemma mod4_of_odd_mul_add6 {D : ℕ} (h : D % 2 = 1) : (D * (D + 6)) % 4 = 3 := by
  have h4 : D % 4 = 1 ∨ D % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · rw [mul_mod_eq h4 (by omega : (D + 6) % 4 = 3)]
  · rw [mul_mod_eq h4 (by omega : (D + 6) % 4 = 1)]

lemma mod25_of_mod5_mul_add2 {D : ℕ} (h : D % 5 = 4) : (D * (D + 2)) % 25 = 24 := by
  have h25 : D % 25 = 4 ∨ D % 25 = 9 ∨ D % 25 = 14 ∨ D % 25 = 19 ∨ D % 25 = 24 := by omega
  rcases h25 with h25 | h25 | h25 | h25 | h25
  · rw [mul_mod_eq h25 (by omega : (D + 2) % 25 = 6)]
  · rw [mul_mod_eq h25 (by omega : (D + 2) % 25 = 11)]
  · rw [mul_mod_eq h25 (by omega : (D + 2) % 25 = 16)]
  · rw [mul_mod_eq h25 (by omega : (D + 2) % 25 = 21)]
  · rw [mul_mod_eq h25 (by omega : (D + 2) % 25 = 1)]

lemma mod9_step34 {D2 n2 D3 n3 D4 : ℕ}
    (hD2 : D2 % 9 = 8) (hn2 : n2 % 3 = 1)
    (hD3 : D3 = D2 * n2) (hs3 : 4 * n3 = D3 + 4 + 1) (hD4 : D4 = D3 * n3) :
    D4 % 9 = 8 := by
  have hn2_9 : n2 % 9 = 1 ∨ n2 % 9 = 4 ∨ n2 % 9 = 7 := by omega
  rcases hn2_9 with h9 | h9 | h9
  · have h3 : D3 % 9 = 8 := by rw [hD3, mul_mod_eq hD2 h9]
    have h3' : n3 % 9 = 1 := by omega
    rw [hD4, mul_mod_eq h3 h3']
  · have h3 : D3 % 9 = 5 := by rw [hD3, mul_mod_eq hD2 h9]
    have h3' : n3 % 9 = 7 := by omega
    rw [hD4, mul_mod_eq h3 h3']
  · have h3 : D3 % 9 = 2 := by rw [hD3, mul_mod_eq hD2 h9]
    have h3' : n3 % 9 = 4 := by omega
    rw [hD4, mul_mod_eq h3 h3']

lemma mod25_to_D4 {D n0 D1 n1 D2 n2 D3 n3 D4 : ℕ}
    (hD5 : D % 5 = 4 ∨ D % 25 = 7)
    (hn0 : n0 = D + 2) (hD1 : D1 = D * n0)
    (hs1 : 2 * n1 = D1 + 2 + 1) (hD2 : D2 = D1 * n1)
    (hs2 : 3 * n2 = D2 + 3 + 1) (hD3 : D3 = D2 * n2)
    (hs3 : 4 * n3 = D3 + 4 + 1) (hD4 : D4 = D3 * n3) :
    D4 % 25 = 24 ∨ D4 % 25 = 14 := by
  rcases hD5 with h5_4 | h25_7
  · left
    have hD1_25 : D1 % 25 = 24 := by rw [hD1, hn0]; exact mod25_of_mod5_mul_add2 h5_4
    have hn1_25 : n1 % 25 = 1 := by omega
    have hD2_25 : D2 % 25 = 24 := by rw [hD2, mul_mod_eq hD1_25 hn1_25]
    have hn2_25 : n2 % 25 = 1 := by omega
    have hD3_25 : D3 % 25 = 24 := by rw [hD3, mul_mod_eq hD2_25 hn2_25]
    have hn3_25 : n3 % 25 = 1 := by omega
    rw [hD4, mul_mod_eq hD3_25 hn3_25]
  · right
    have hn0_25 : n0 % 25 = 9 := by omega
    have hD1_25 : D1 % 25 = 13 := by rw [hD1, mul_mod_eq h25_7 hn0_25]
    have hn1_25 : n1 % 25 = 8 := by omega
    have hD2_25 : D2 % 25 = 4 := by rw [hD2, mul_mod_eq hD1_25 hn1_25]
    have hn2_25 : n2 % 25 = 11 := by omega
    have hD3_25 : D3 % 25 = 19 := by rw [hD3, mul_mod_eq hD2_25 hn2_25]
    have hn3_25 : n3 % 25 = 6 := by omega
    rw [hD4, mul_mod_eq hD3_25 hn3_25]

lemma mod25_step56 {D4 n4 D5 n5 D6 : ℕ}
    (hD4 : D4 % 25 = 24 ∨ D4 % 25 = 14)
    (hs4 : 5 * n4 = D4 + 5 + 1) (hD5 : D5 = D4 * n4)
    (hs5 : 6 * n5 = D5 + 6 + 1) (hD6 : 7 * D6 = D5 * n5) :
    D6 % 5 = 4 ∨ D6 % 25 = 7 := by
  rcases hD4 with h24 | h14
  · right
    have hn4_25 : n4 % 25 = 1 ∨ n4 % 25 = 6 ∨ n4 % 25 = 11 ∨ n4 % 25 = 16 ∨ n4 % 25 = 21 := by
      omega
    have h7D6 : (7 * D6) % 25 = 24 := by
      rw [hD6]
      rcases hn4_25 with h | h | h | h | h
      · have h5 : D5 % 25 = 24 := by rw [hD5, mul_mod_eq h24 h]
        have hn5 : n5 % 25 = 1 := by omega
        rw [mul_mod_eq h5 hn5]
      · have h5 : D5 % 25 = 19 := by rw [hD5, mul_mod_eq h24 h]
        have hn5 : n5 % 25 = 21 := by omega
        rw [mul_mod_eq h5 hn5]
      · have h5 : D5 % 25 = 14 := by rw [hD5, mul_mod_eq h24 h]
        have hn5 : n5 % 25 = 16 := by omega
        rw [mul_mod_eq h5 hn5]
      · have h5 : D5 % 25 = 9 := by rw [hD5, mul_mod_eq h24 h]
        have hn5 : n5 % 25 = 11 := by omega
        rw [mul_mod_eq h5 hn5]
      · have h5 : D5 % 25 = 4 := by rw [hD5, mul_mod_eq h24 h]
        have hn5 : n5 % 25 = 6 := by omega
        rw [mul_mod_eq h5 hn5]
    omega
  · left
    have hD4_5 : D4 % 5 = 4 := by omega
    have hn4_5 : n4 % 5 = 4 := by omega
    have hD5_5 : D5 % 5 = 1 := by rw [hD5, mul_mod_eq hD4_5 hn4_5]
    have hn5_5 : n5 % 5 = 3 := by omega
    have h7D6 : (7 * D6) % 5 = 3 := by rw [hD6, mul_mod_eq hD5_5 hn5_5]
    omega

-- Isolated per-step arithmetic lemmas to keep every `omega` context tiny and instant.

lemma step0_aux {D : ℕ} (hD2 : D % 2 = 1) (hD3 : D % 3 = 2) (hD7 : D % 7 = 0) :
    ∃ n0 D1 : ℕ, 7 ≤ D ∧ 9 ≤ n0 ∧ 63 ≤ D1 ∧ n0 = D + 2 ∧ D1 = D * n0 ∧
      1 * n0 = D + 1 + 1 ∧ n0 % 3 = 1 ∧ D1 % 4 = 3 ∧ D1 % 9 = 8 ∧ D1 % 7 = 0 := by
  have hD_ge : 7 ≤ D := by omega
  refine ⟨D + 2, D * (D + 2), hD_ge, by omega, Nat.mul_le_mul hD_ge (by omega : 9 ≤ D + 2),
    rfl, rfl, by omega, by omega, mod4_of_odd_mul_add2 hD2, mod9_of_mod3_mul_add2 hD3, ?_⟩
  rw [Nat.mul_mod, hD7]; norm_num

lemma step1_aux {D n0 D1 : ℕ} (hD : 7 ≤ D) (hn0 : 9 ≤ n0) (hD1 : D1 = D * n0)
    (hD1_ge : 63 ≤ D1) (h4 : D1 % 4 = 3) (h9 : D1 % 9 = 8) (h7 : D1 % 7 = 0) :
    ∃ n1 D2 : ℕ, 0 < n1 ∧ n0 < n1 ∧ 63 ≤ D2 ∧ D2 = D1 * n1 ∧
      2 * n1 = D1 + 2 + 1 ∧ n1 % 3 = 1 ∧ D2 % 2 = 1 ∧ D2 % 9 = 8 ∧ D2 % 7 = 0 := by
  let n1 := (D1 + 3) / 2
  have hs1 : 2 * n1 = D1 + 2 + 1 := by omega
  have hn1_pos : 0 < n1 := by omega
  have hn0_lt : n0 < n1 := by
    have : 2 * n0 < D * n0 := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    omega
  have hD2_ge : 63 ≤ D1 * n1 := by
    have : D1 * 1 ≤ D1 * n1 := Nat.mul_le_mul_left D1 hn1_pos
    omega
  refine ⟨n1, D1 * n1, hn1_pos, hn0_lt, hD2_ge, rfl, hs1, by omega,
    mul_mod_eq (by omega : D1 % 2 = 1) (by omega : n1 % 2 = 1),
    mul_mod_eq h9 (by omega : n1 % 9 = 1), ?_⟩
  rw [Nat.mul_mod, h7]; norm_num

lemma step2_aux {D1 n1 D2 : ℕ} (hD1 : 63 ≤ D1) (hn1 : 0 < n1) (hD2 : D2 = D1 * n1)
    (hD2_ge : 63 ≤ D2) (h2 : D2 % 2 = 1) (h9 : D2 % 9 = 8) (h7 : D2 % 7 = 0) :
    ∃ n2 D3 : ℕ, 0 < n2 ∧ n1 < n2 ∧ 63 ≤ D3 ∧ D3 = D2 * n2 ∧
      3 * n2 = D2 + 3 + 1 ∧ n2 % 3 = 1 ∧ D3 % 8 = 7 ∧ D3 % 3 = 2 ∧ D3 % 7 = 0 := by
  let n2 := (D2 + 4) / 3
  have hs2 : 3 * n2 = D2 + 3 + 1 := by omega
  have hn2_pos : 0 < n2 := by omega
  have hn1_lt : n1 < n2 := by
    have : 3 * n1 < D1 * n1 := Nat.mul_lt_mul_of_pos_right (by omega) hn1
    omega
  have hD3_ge : 63 ≤ D2 * n2 := by
    have : D2 * 1 ≤ D2 * n2 := Nat.mul_le_mul_left D2 hn2_pos
    omega
  have hD3_8 : (D2 * n2) % 8 = 7 := by
    have hmul : 3 * (D2 * n2) = D2 * (D2 + 4) := by
      calc 3 * (D2 * n2) = D2 * (3 * n2) := by ring
        _ = D2 * (D2 + 4) := by rw [hs2]
    have h3 : (3 * (D2 * n2)) % 8 = 5 := by rw [hmul]; exact mod8_of_odd_mul_add4 h2
    omega
  refine ⟨n2, D2 * n2, hn2_pos, hn1_lt, hD3_ge, rfl, hs2, by omega, hD3_8,
    mul_mod_eq (by omega : D2 % 3 = 2) (by omega : n2 % 3 = 1), ?_⟩
  rw [Nat.mul_mod, h7]; norm_num

lemma step3_aux {D2 n2 D3 : ℕ} (hD2_ge : 63 ≤ D2) (hn2 : 0 < n2) (hD3 : D3 = D2 * n2)
    (hD2_9 : D2 % 9 = 8) (hn2_3 : n2 % 3 = 1)
    (hD3_ge : 63 ≤ D3) (h8 : D3 % 8 = 7) (h3 : D3 % 3 = 2) (h7 : D3 % 7 = 0) :
    ∃ n3 D4 : ℕ, 0 < n3 ∧ n2 < n3 ∧ 63 ≤ D4 ∧ D4 = D3 * n3 ∧
      4 * n3 = D3 + 4 + 1 ∧ n3 % 3 = 1 ∧ D4 % 2 = 1 ∧ D4 % 9 = 8 ∧ D4 % 7 = 0 := by
  let n3 := (D3 + 5) / 4
  have hs3 : 4 * n3 = D3 + 4 + 1 := by omega
  have hn3_pos : 0 < n3 := by omega
  have hn2_lt : n2 < n3 := by
    have : 4 * n2 < D2 * n2 := Nat.mul_lt_mul_of_pos_right (by omega) hn2
    omega
  have hD4_ge : 63 ≤ D3 * n3 := by
    have : D3 * 1 ≤ D3 * n3 := Nat.mul_le_mul_left D3 hn3_pos
    omega
  refine ⟨n3, D3 * n3, hn3_pos, hn2_lt, hD4_ge, rfl, hs3, by omega,
    mul_mod_eq (by omega : D3 % 2 = 1) (by omega : n3 % 2 = 1),
    mod9_step34 hD2_9 hn2_3 hD3 hs3 rfl, ?_⟩
  rw [Nat.mul_mod, h7]; norm_num

lemma step4_aux {D3 n3 D4 : ℕ} (hD3_ge : 63 ≤ D3) (hn3 : 0 < n3) (hD4 : D4 = D3 * n3)
    (hD4_ge : 63 ≤ D4) (h2 : D4 % 2 = 1) (h9 : D4 % 9 = 8) (h7 : D4 % 7 = 0)
    (h25 : D4 % 25 = 24 ∨ D4 % 25 = 14) :
    ∃ n4 D5 : ℕ, 0 < n4 ∧ n3 < n4 ∧ 63 ≤ D5 ∧ D5 = D4 * n4 ∧
      5 * n4 = D4 + 5 + 1 ∧ n4 % 3 = 1 ∧ D5 % 4 = 3 ∧ D5 % 9 = 8 ∧ D5 % 7 = 0 := by
  have h5 : D4 % 5 = 4 := by omega
  let n4 := (D4 + 6) / 5
  have hs4 : 5 * n4 = D4 + 5 + 1 := by omega
  have hn4_pos : 0 < n4 := by omega
  have hn3_lt : n3 < n4 := by
    have : 5 * n3 < D3 * n3 := Nat.mul_lt_mul_of_pos_right (by omega) hn3
    omega
  have hD5_ge : 63 ≤ D4 * n4 := by
    have : D4 * 1 ≤ D4 * n4 := Nat.mul_le_mul_left D4 hn4_pos
    omega
  have hD5_4 : (D4 * n4) % 4 = 3 := by
    have hmul : 5 * (D4 * n4) = D4 * (D4 + 6) := by
      calc 5 * (D4 * n4) = D4 * (5 * n4) := by ring
        _ = D4 * (D4 + 6) := by rw [hs4]
    have h5d : (5 * (D4 * n4)) % 4 = 3 := by rw [hmul]; exact mod4_of_odd_mul_add6 h2
    omega
  refine ⟨n4, D4 * n4, hn4_pos, hn3_lt, hD5_ge, rfl, hs4, by omega, hD5_4,
    mul_mod_eq h9 (by omega : n4 % 9 = 1), ?_⟩
  rw [Nat.mul_mod, h7]; norm_num

lemma step5_aux {D4 n4 D5 : ℕ} (hD4_ge : 63 ≤ D4) (hn4 : 0 < n4) (hD5 : D5 = D4 * n4)
    (hD4_25 : D4 % 25 = 24 ∨ D4 % 25 = 14) (hs4 : 5 * n4 = D4 + 5 + 1)
    (hD5_ge : 63 ≤ D5) (h4 : D5 % 4 = 3) (h9 : D5 % 9 = 8) (h7 : D5 % 7 = 0) :
    ∃ n5 D6 : ℕ, 0 < n5 ∧ n4 < n5 ∧ n5 < D6 ∧ 0 < D6 ∧
      6 * n5 = D5 + 6 + 1 ∧ 7 * D6 = D5 * n5 ∧ n5 % 3 = 1 ∧
      D6 % 2 = 1 ∧ D6 % 3 = 2 ∧ (D6 % 5 = 4 ∨ D6 % 25 = 7) ∧ D6 % 7 = 0 := by
  let n5 := (D5 + 7) / 6
  let D6 := (D5 / 7) * n5
  have hs5 : 6 * n5 = D5 + 6 + 1 := by omega
  have hn5_pos : 0 < n5 := by omega
  have hn4_lt : n4 < n5 := by
    have : 6 * n4 < D4 * n4 := Nat.mul_lt_mul_of_pos_right (by omega) hn4
    omega
  have hmul : 7 * D6 = D5 * n5 := by
    have h7' : 7 * (D5 / 7) = D5 := by omega
    calc 7 * D6 = (7 * (D5 / 7)) * n5 := by ring
      _ = D5 * n5 := by rw [h7']
  have hn5_lt_D6 : n5 < D6 := by
    have hq : 1 < D5 / 7 := by omega
    have : 1 * n5 < (D5 / 7) * n5 := Nat.mul_lt_mul_of_pos_right hq hn5_pos
    omega
  have hn5_2 : n5 % 2 = 1 := by omega
  have hn5_3 : n5 % 3 = 1 := by omega
  have hn5_7 : n5 % 7 = 0 := by omega
  have hD6_2 : D6 % 2 = 1 := by
    have h1 : (7 * D6) % 2 = 1 := by rw [hmul, mul_mod_eq (by omega : D5 % 2 = 1) hn5_2]
    omega
  have hD6_3 : D6 % 3 = 2 := by
    have h1 : (7 * D6) % 3 = 2 := by rw [hmul, mul_mod_eq (by omega : D5 % 3 = 2) hn5_3]
    omega
  have hD6_7 : D6 % 7 = 0 := by rw [Nat.mul_mod, hn5_7]; norm_num
  have hD6_5 : D6 % 5 = 4 ∨ D6 % 25 = 7 :=
    mod25_step56 hD4_25 hs4 hD5 hs5 hmul
  exact ⟨n5, D6, hn5_pos, hn4_lt, hn5_lt_D6, Nat.lt_trans hn5_pos hn5_lt_D6, hs5, hmul, hn5_3,
    hD6_2, hD6_3, hD6_5, hD6_7⟩

lemma good_step6 {A : Set ℕ} {D : ℕ} (h : Good A D) :
    ∃ A' D', Good A' D' ∧
      ∀ t, greedyUnitFractionRem A ((1 : ℚ) / (D : ℚ)) (t + 6) =
        greedyUnitFractionRem A' ((1 : ℚ) / (D' : ℚ)) t := by
  rcases h with ⟨hA_sub, hA_ge, hD2, hD3, hD5, hD7⟩
  obtain ⟨n0, D1, hD_ge, hn0_ge, hD1_ge, hn0_eq, hD1_eq, hs0, hn0_3, hD1_4, hD1_9, hD1_7⟩ :=
    step0_aux hD2 hD3 hD7
  obtain ⟨n1, D2, hn1_pos, hn0_lt_n1, hD2_ge, hD2_eq, hs1, hn1_3, hD2_2, hD2_9, hD2_7⟩ :=
    step1_aux hD_ge hn0_ge hD1_eq hD1_ge hD1_4 hD1_9 hD1_7
  obtain ⟨n2, D3, hn2_pos, hn1_lt_n2, hD3_ge, hD3_eq, hs2, hn2_3, hD3_8, hD3_3, hD3_7⟩ :=
    step2_aux hD1_ge hn1_pos hD2_eq hD2_ge hD2_2 hD2_9 hD2_7
  obtain ⟨n3, D4, hn3_pos, hn2_lt_n3, hD4_ge, hD4_eq, hs3, hn3_3, hD4_2, hD4_9, hD4_7⟩ :=
    step3_aux hD2_ge hn2_pos hD3_eq hD2_9 hn2_3 hD3_ge hD3_8 hD3_3 hD3_7
  have hD4_25 : D4 % 25 = 24 ∨ D4 % 25 = 14 :=
    mod25_to_D4 hD5 hn0_eq hD1_eq hs1 hD2_eq hs2 hD3_eq hs3 hD4_eq
  obtain ⟨n4, D5, hn4_pos, hn3_lt_n4, hD5_ge, hD5_eq, hs4, hn4_3, hD5_4, hD5_9, hD5_7⟩ :=
    step4_aux hD3_ge hn3_pos hD4_eq hD4_ge hD4_2 hD4_9 hD4_7 hD4_25
  obtain ⟨n5, D6, hn5_pos, hn4_lt_n5, hn5_lt_D6, hD6_pos, hs5, hD5_mul, hn5_3,
    hD6_2, hD6_3, hD6_5, hD6_7⟩ :=
    step5_aux hD4_ge hn4_pos hD5_eq hD4_25 hs4 hD5_ge hD5_4 hD5_9 hD5_7
  clear hD2 hD3 hD5 hD7 hD1_4 hD1_9 hD1_7 hD2_2 hD2_9 hD2_7 hD3_8 hD3_3 hD3_7 hD4_2 hD4_9 hD4_7
    hD4_25 hD5_4 hD5_9 hD5_7
  let A1 := A \ {n0}
  let A2 := A1 \ {n1}
  let A3 := A2 \ {n2}
  let A4 := A3 \ {n3}
  let A5 := A4 \ {n4}
  let A6 := A5 \ {n5}
  have hA1_sub : ∀ m ∈ A1, m % 3 = 1 := fun m hm => hA_sub m hm.1
  have hA2_sub : ∀ m ∈ A2, m % 3 = 1 := fun m hm => hA1_sub m hm.1
  have hA3_sub : ∀ m ∈ A3, m % 3 = 1 := fun m hm => hA2_sub m hm.1
  have hA4_sub : ∀ m ∈ A4, m % 3 = 1 := fun m hm => hA3_sub m hm.1
  have hA5_sub : ∀ m ∈ A5, m % 3 = 1 := fun m hm => hA4_sub m hm.1
  have hA6_sub : ∀ m ∈ A6, m % 3 = 1 := fun m hm => hA5_sub m hm.1
  have hD_le_n0 : D ≤ n0 := hn0_eq ▸ Nat.le_add_right D 2
  have hA0_ge : ∀ m, m % 3 = 1 → n0 ≤ m → m ∈ A :=
    fun m hm hle => hA_ge m hm (le_trans hD_le_n0 hle)
  have hA1_ge : ∀ m, m % 3 = 1 → n1 ≤ m → m ∈ A1 := fun m hm hle =>
    ⟨hA0_ge m hm (le_trans (le_of_lt hn0_lt_n1) hle),
      Set.notMem_singleton_iff.mpr (ne_of_gt (lt_of_lt_of_le hn0_lt_n1 hle))⟩
  have hA2_ge : ∀ m, m % 3 = 1 → n2 ≤ m → m ∈ A2 := fun m hm hle =>
    ⟨hA1_ge m hm (le_trans (le_of_lt hn1_lt_n2) hle),
      Set.notMem_singleton_iff.mpr (ne_of_gt (lt_of_lt_of_le hn1_lt_n2 hle))⟩
  have hA3_ge : ∀ m, m % 3 = 1 → n3 ≤ m → m ∈ A3 := fun m hm hle =>
    ⟨hA2_ge m hm (le_trans (le_of_lt hn2_lt_n3) hle),
      Set.notMem_singleton_iff.mpr (ne_of_gt (lt_of_lt_of_le hn2_lt_n3 hle))⟩
  have hA4_ge : ∀ m, m % 3 = 1 → n4 ≤ m → m ∈ A4 := fun m hm hle =>
    ⟨hA3_ge m hm (le_trans (le_of_lt hn3_lt_n4) hle),
      Set.notMem_singleton_iff.mpr (ne_of_gt (lt_of_lt_of_le hn3_lt_n4 hle))⟩
  have hA5_ge : ∀ m, m % 3 = 1 → n5 ≤ m → m ∈ A5 := fun m hm hle =>
    ⟨hA4_ge m hm (le_trans (le_of_lt hn4_lt_n5) hle),
      Set.notMem_singleton_iff.mpr (ne_of_gt (lt_of_lt_of_le hn4_lt_n5 hle))⟩
  have hA6_ge : ∀ m, m % 3 = 1 → D6 ≤ m → m ∈ A6 := fun m hm hle =>
    ⟨hA5_ge m hm (le_trans (le_of_lt hn5_lt_D6) hle),
      Set.notMem_singleton_iff.mpr (ne_of_gt (lt_of_lt_of_le hn5_lt_D6 hle))⟩
  refine ⟨A6, D6, ⟨hA6_sub, hA6_ge, hD6_2, hD6_3, hD6_5, hD6_7⟩, ?_⟩
  intro t
  have hD_pos : 0 < D := lt_of_lt_of_le (by decide : 0 < 7) hD_ge
  have hn0_pos : 0 < n0 := lt_of_lt_of_le (by decide : 0 < 9) hn0_ge
  have hD1_pos : 0 < D1 := lt_of_lt_of_le (by decide : 0 < 63) hD1_ge
  have hD2_pos : 0 < D2 := lt_of_lt_of_le (by decide : 0 < 63) hD2_ge
  have hD3_pos : 0 < D3 := lt_of_lt_of_le (by decide : 0 < 63) hD3_ge
  have hD4_pos : 0 < D4 := lt_of_lt_of_le (by decide : 0 < 63) hD4_ge
  have hD5_pos : 0 < D5 := lt_of_lt_of_le (by decide : 0 < 63) hD5_ge
  have h0 := greedy_step_succ (by decide : 0 < 1) hD_pos hn0_pos
    hA_sub hA0_ge hn0_3 hs0 (t + 5)
  have h1 := greedy_step_succ (by decide : 0 < 2) hD1_pos hn1_pos
    hA1_sub hA1_ge hn1_3 hs1 (t + 4)
  have h2 := greedy_step_succ (by decide : 0 < 3) hD2_pos hn2_pos
    hA2_sub hA2_ge hn2_3 hs2 (t + 3)
  have h3 := greedy_step_succ (by decide : 0 < 4) hD3_pos hn3_pos
    hA3_sub hA3_ge hn3_3 hs3 (t + 2)
  have h4 := greedy_step_succ (by decide : 0 < 5) hD4_pos hn4_pos
    hA4_sub hA4_ge hn4_3 hs4 (t + 1)
  have h5 := greedy_step_succ (by decide : 0 < 6) hD5_pos hn5_pos
    hA5_sub hA5_ge hn5_3 hs5 t
  rw [← hD1_eq] at h0
  rw [← hD2_eq] at h1
  rw [← hD3_eq] at h2
  rw [← hD4_eq] at h3
  rw [← hD5_eq] at h4
  have hfrac : ((7 : ℕ) : ℚ) / ((D5 * n5 : ℕ) : ℚ) = (1 : ℚ) / (D6 : ℚ) := by
    have hD6q : (D6 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD6_pos)
    have hD5n5q : ((D5 * n5 : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos hD5_pos hn5_pos))
    have hmulq : (7 : ℚ) * (D6 : ℚ) = ((D5 * n5 : ℕ) : ℚ) := by exact_mod_cast hD5_mul
    push_cast
    field_simp [hD6q, hD5n5q]
    push_cast at hmulq
    linarith
  simp only [Nat.cast_one] at h0
  calc
    greedyUnitFractionRem A ((1 : ℚ) / (D : ℚ)) (t + 6)
        = greedyUnitFractionRem A1 (((1 + 1 : ℕ) : ℚ) / (D1 : ℚ)) (t + 5) := h0
    _ = greedyUnitFractionRem A2 (((2 + 1 : ℕ) : ℚ) / (D2 : ℚ)) (t + 4) := h1
    _ = greedyUnitFractionRem A3 (((3 + 1 : ℕ) : ℚ) / (D3 : ℚ)) (t + 3) := h2
    _ = greedyUnitFractionRem A4 (((4 + 1 : ℕ) : ℚ) / (D4 : ℚ)) (t + 2) := h3
    _ = greedyUnitFractionRem A5 (((5 + 1 : ℕ) : ℚ) / (D5 : ℚ)) (t + 1) := h4
    _ = greedyUnitFractionRem A6 (((6 + 1 : ℕ) : ℚ) / ((D5 * n5 : ℕ) : ℚ)) t := h5
    _ = greedyUnitFractionRem A6 ((1 : ℚ) / (D6 : ℚ)) t := by rw [hfrac]

lemma good_pos_at_zero {A : Set ℕ} {D : ℕ} (h : Good A D) :
    0 < greedyUnitFractionRem A ((1 : ℚ) / (D : ℚ)) 0 := by
  rcases h with ⟨hA_sub, hA_ge, hD2, hD3, _, hD7⟩
  have hD_pos : 0 < D := by omega
  have h0 := greedy_step_zero (by omega : 0 < 1) hD_pos (by omega : 0 < D + 2)
    hA_sub (fun m hm hle => hA_ge m hm (by omega)) (by omega) (by omega)
  simp only [Nat.cast_one] at h0
  rw [h0]
  positivity

lemma good_iter (k : ℕ) :
    ∃ A D, Good A D ∧
      ∀ t, greedyUnitFractionRem { n | n ≡ 1 [MOD 3] } ((1 : ℚ) / 119) (t + 6 * k) =
        greedyUnitFractionRem A ((1 : ℚ) / (D : ℚ)) t := by
  induction k with
  | zero =>
    refine ⟨{ n | n ≡ 1 [MOD 3] }, 119, ?_, ?_⟩
    · refine ⟨?_, ?_, by decide, by decide, Or.inl (by decide), by decide⟩
      · intro m hm
        simpa [Nat.ModEq] using hm
      · intro m hm _
        simpa [Nat.ModEq] using hm
    · intro t
      norm_num
  | succ k ih =>
    rcases ih with ⟨A, D, hGood, hEq⟩
    rcases good_step6 hGood with ⟨A', D', hGood', hStep⟩
    refine ⟨A', D', hGood', ?_⟩
    intro t
    have hidx : t + 6 * (k + 1) = (t + 6) + 6 * k := by ring
    rw [hidx, hEq (t + 6), hStep t]

end OMAErdos282Graham

theorem OMA.disproof : ¬ (type_of% @Erdos282.erdos_282.variants.graham) := by
  intro h
  have hden : (1 / 119 : ℚ).den = 119 := by norm_num
  have hcop : ((1 / 119 : ℚ).den / (1 / 119 : ℚ).den.gcd (Nat.gcd 1 3)).gcd (3 / Nat.gcd 1 3) = 1 := by
    rw [hden]; decide
  have hspec := h (1 / 119 : ℚ) (by norm_num) 1 3 (by decide) hcop
  rw [Filter.EventuallyEq, Filter.eventually_atTop] at hspec
  rcases hspec with ⟨N, hN⟩
  rcases OMAErdos282Graham.good_iter N with ⟨A, D, hGood, hEq⟩
  have hpos := OMAErdos282Graham.good_pos_at_zero hGood
  have hzero : Erdos282.greedyUnitFractionRem { n | n ≡ 1 [MOD 3] } (1 / 119 : ℚ) (0 + 6 * N) = 0 :=
    hN (0 + 6 * N) (by omega)
  rw [hEq 0] at hzero
  linarith
