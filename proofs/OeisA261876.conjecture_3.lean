import FormalConjectures.OEIS.«261876»

/-!
Disproof of `OeisA261876.conjecture_3` using the triple `(42, 98, 14)` and `n = 56271`.
Since `56271 ≡ 7 (mod 8)`, any 4-square representation consists of one summand `≡ 2 (mod 4)`
and three odd summands. We scan all such representations and rule out all 24 ordered triples
via 14 quadratic-residue bitmasks.
-/

namespace OeisA261876Disproof

private def isQROf (m mask v : ℕ) : Bool :=
  ((mask >>> (v % m)) &&& 1) == 1

private lemma isQROf_of_isSquare (m mask : ℕ) (hm : 0 < m)
    (hmask : ∀ r : Fin m, ((mask >>> ((r.val * r.val) % m)) &&& 1) == 1)
    {v : ℕ} (hv : IsSquare v) : isQROf m mask v = true := by
  rcases hv with ⟨r, rfl⟩
  unfold isQROf
  rw [Nat.mul_mod]
  exact hmask ⟨r % m, Nat.mod_lt r hm⟩

private lemma qr_64 : ∀ r : Fin 64, ((144680414395695635 >>> ((r.val * r.val) % 64)) &&& 1) == 1 := by decide
private lemma qr_63 : ∀ r : Fin 63, ((288872697407275667 >>> ((r.val * r.val) % 63)) &&& 1) == 1 := by decide
private lemma qr_25 : ∀ r : Fin 25, ((19483219 >>> ((r.val * r.val) % 25)) &&& 1) == 1 := by decide
private lemma qr_11 : ∀ r : Fin 11, ((571 >>> ((r.val * r.val) % 11)) &&& 1) == 1 := by decide
private lemma qr_13 : ∀ r : Fin 13, ((5659 >>> ((r.val * r.val) % 13)) &&& 1) == 1 := by decide
private lemma qr_17 : ∀ r : Fin 17, ((107287 >>> ((r.val * r.val) % 17)) &&& 1) == 1 := by decide
private lemma qr_19 : ∀ r : Fin 19, ((199411 >>> ((r.val * r.val) % 19)) &&& 1) == 1 := by decide
private lemma qr_23 : ∀ r : Fin 23, ((340831 >>> ((r.val * r.val) % 23)) &&& 1) == 1 := by decide
private lemma qr_29 : ∀ r : Fin 29, ((332473075 >>> ((r.val * r.val) % 29)) &&& 1) == 1 := by decide
private lemma qr_31 : ∀ r : Fin 31, ((303908791 >>> ((r.val * r.val) % 31)) &&& 1) == 1 := by decide
private lemma qr_37 : ∀ r : Fin 37, ((96068509339 >>> ((r.val * r.val) % 37)) &&& 1) == 1 := by decide
private lemma qr_41 : ∀ r : Fin 41, ((1870503675703 >>> ((r.val * r.val) % 41)) &&& 1) == 1 := by decide
private lemma qr_43 : ∀ r : Fin 43, ((3678700564051 >>> ((r.val * r.val) % 43)) &&& 1) == 1 := by decide
private lemma qr_47 : ∀ r : Fin 47, ((4626135339999 >>> ((r.val * r.val) % 47)) &&& 1) == 1 := by decide

private def notSq (v : ℕ) : Bool :=
  !isQROf 64 144680414395695635 v ||
  !isQROf 63 288872697407275667 v ||
  !isQROf 25 19483219 v ||
  !isQROf 11 571 v ||
  !isQROf 13 5659 v ||
  !isQROf 17 107287 v ||
  !isQROf 19 199411 v ||
  !isQROf 23 340831 v ||
  !isQROf 29 332473075 v ||
  !isQROf 31 303908791 v ||
  !isQROf 37 96068509339 v ||
  !isQROf 41 1870503675703 v ||
  !isQROf 43 3678700564051 v ||
  !isQROf 47 4626135339999 v

private lemma not_isSquare_of_notSq {v : ℕ} (h : notSq v = true) : ¬ IsSquare v := by
  intro hv
  have h64 := isQROf_of_isSquare 64 144680414395695635 (by decide) qr_64 hv
  have h63 := isQROf_of_isSquare 63 288872697407275667 (by decide) qr_63 hv
  have h25 := isQROf_of_isSquare 25 19483219 (by decide) qr_25 hv
  have h11 := isQROf_of_isSquare 11 571 (by decide) qr_11 hv
  have h13 := isQROf_of_isSquare 13 5659 (by decide) qr_13 hv
  have h17 := isQROf_of_isSquare 17 107287 (by decide) qr_17 hv
  have h19 := isQROf_of_isSquare 19 199411 (by decide) qr_19 hv
  have h23 := isQROf_of_isSquare 23 340831 (by decide) qr_23 hv
  have h29 := isQROf_of_isSquare 29 332473075 (by decide) qr_29 hv
  have h31 := isQROf_of_isSquare 31 303908791 (by decide) qr_31 hv
  have h37 := isQROf_of_isSquare 37 96068509339 (by decide) qr_37 hv
  have h41 := isQROf_of_isSquare 41 1870503675703 (by decide) qr_41 hv
  have h43 := isQROf_of_isSquare 43 3678700564051 (by decide) qr_43 hv
  have h47 := isQROf_of_isSquare 47 4626135339999 (by decide) qr_47 hv
  simp [notSq, h64, h63, h25, h11, h13, h17, h19, h23, h29, h31, h37, h41, h43, h47] at h

private def evalTriple (x y z : ℕ) : ℕ :=
  x * y * (42 * (x * x) + 98 * (y * y) + 14 * (z * z))

private def check24 (a b c d : ℕ) : Bool :=
  notSq (evalTriple a b c) && notSq (evalTriple a b d) &&
  notSq (evalTriple a c b) && notSq (evalTriple a c d) &&
  notSq (evalTriple a d b) && notSq (evalTriple a d c) &&
  notSq (evalTriple b a c) && notSq (evalTriple b a d) &&
  notSq (evalTriple b c a) && notSq (evalTriple b c d) &&
  notSq (evalTriple b d a) && notSq (evalTriple b d c) &&
  notSq (evalTriple c a b) && notSq (evalTriple c a d) &&
  notSq (evalTriple c b a) && notSq (evalTriple c b d) &&
  notSq (evalTriple c d a) && notSq (evalTriple c d b) &&
  notSq (evalTriple d a b) && notSq (evalTriple d a c) &&
  notSq (evalTriple d b a) && notSq (evalTriple d b c) &&
  notSq (evalTriple d c a) && notSq (evalTriple d c b)

private def HasSq (a b c d : ℕ) : Prop :=
  ∃ p q r : ℕ, (p, q, r) ∈ [
    (a, b, c), (a, b, d), (a, c, b), (a, c, d), (a, d, b), (a, d, c),
    (b, a, c), (b, a, d), (b, c, a), (b, c, d), (b, d, a), (b, d, c),
    (c, a, b), (c, a, d), (c, b, a), (c, b, d), (c, d, a), (c, d, b),
    (d, a, b), (d, a, c), (d, b, a), (d, b, c), (d, c, a), (d, c, b)
  ] ∧ IsSquare (evalTriple p q r)

private lemma not_hasSq_of_check24 {a b c d : ℕ} (h : check24 a b c d = true) :
    ¬ HasSq a b c d := by
  intro ⟨p, q, r, hmem, hsq⟩
  simp only [check24, Bool.and_eq_true] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact not_isSquare_of_notSq (by tauto) hsq

private lemma hasSq_swap12 {a b c d : ℕ} (h : HasSq a b c d) : HasSq b a c d := by
  rcases h with ⟨p, q, r, hmem, hsq⟩
  refine ⟨p, q, r, ?_, hsq⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem ⊢
  tauto

private lemma hasSq_swap13 {a b c d : ℕ} (h : HasSq a b c d) : HasSq c b a d := by
  rcases h with ⟨p, q, r, hmem, hsq⟩
  refine ⟨p, q, r, ?_, hsq⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem ⊢
  tauto

private lemma hasSq_swap14 {a b c d : ℕ} (h : HasSq a b c d) : HasSq d b c a := by
  rcases h with ⟨p, q, r, hmem, hsq⟩
  refine ⟨p, q, r, ?_, hsq⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem ⊢
  tauto

private lemma hasSq_swap23 {a b c d : ℕ} (h : HasSq a b c d) : HasSq a c b d := by
  rcases h with ⟨p, q, r, hmem, hsq⟩
  refine ⟨p, q, r, ?_, hsq⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem ⊢
  tauto

private lemma hasSq_swap34 {a b c d : ℕ} (h : HasSq a b c d) : HasSq a b d c := by
  rcases h with ⟨p, q, r, hmem, hsq⟩
  refine ⟨p, q, r, ?_, hsq⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem ⊢
  tauto

private def isqrt256 (x : ℕ) : ℕ :=
  let r0 := 0
  let r1 := if (r0 + 128) * (r0 + 128) ≤ x then r0 + 128 else r0
  let r2 := if (r1 + 64) * (r1 + 64) ≤ x then r1 + 64 else r1
  let r3 := if (r2 + 32) * (r2 + 32) ≤ x then r2 + 32 else r2
  let r4 := if (r3 + 16) * (r3 + 16) ≤ x then r3 + 16 else r3
  let r5 := if (r4 + 8) * (r4 + 8) ≤ x then r4 + 8 else r4
  let r6 := if (r5 + 4) * (r5 + 4) ≤ x then r5 + 4 else r5
  let r7 := if (r6 + 2) * (r6 + 2) ≤ x then r6 + 2 else r6
  if (r7 + 1) * (r7 + 1) ≤ x then r7 + 1 else r7

private def checkSqrtAux : ℕ → Bool
  | 0 => true
  | k + 1 => (isqrt256 (k * k) == k) && checkSqrtAux k

private lemma checkSqrtAux_sound :
    ∀ n : ℕ, checkSqrtAux n = true → ∀ w : ℕ, w < n → isqrt256 (w * w) = w
  | 0, _, w, hw => by omega
  | k + 1, h, w, hw => by
    simp only [checkSqrtAux, Bool.and_eq_true, beq_iff_eq] at h
    by_cases hwk : w = k
    · subst hwk; exact h.1
    · exact checkSqrtAux_sound k h.2 w (by omega)

private lemma isqrt256_sq (w : ℕ) (hw : w ≤ 255) : isqrt256 (w * w) = w := by
  have h : checkSqrtAux 256 = true := by decide +kernel
  exact checkSqrtAux_sound 256 h w (by omega)

private def checkV (e u R : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | fuel + 1, v =>
    let v2 := v * v
    if 2 * v2 > R then true
    else
      let rem := R - v2
      let ok :=
        if isQROf 63 288872697407275667 rem && isQROf 25 19483219 rem then
          let w := isqrt256 rem
          if w * w == rem then check24 e u v w else true
        else true
      ok && checkV e u R fuel (v + 2)

private lemma checkV_sound (e u R : ℕ) :
    ∀ fuel v0 : ℕ, checkV e u R fuel v0 = true →
      ∀ v w : ℕ, v * v + w * w = R → v ≤ w →
        v0 ≤ v → (v - v0) % 2 = 0 → v - v0 < 2 * fuel → w ≤ 255 →
        ¬ HasSq e u v w
  | 0, v0, _, v, w, _, _, _, _, hlt, _ => by omega
  | fuel + 1, v0, hchk, v, w, hsum, hvw, hv0, hpar, hlt, hw255 => by
    unfold checkV at hchk
    by_cases hstop : 2 * (v0 * v0) > R
    · have h1 : v0 * v0 ≤ v * v := Nat.mul_le_mul hv0 hv0
      have h2 : v * v ≤ w * w := Nat.mul_le_mul hvw hvw
      omega
    · simp only [hstop, ↓reduceIte, Bool.and_eq_true] at hchk
      rcases hchk with ⟨hok, hrest⟩
      by_cases hv : v = v0
      · subst hv
        have hrem : R - v * v = w * w := by omega
        have hsq : IsSquare (w * w) := ⟨w, rfl⟩
        have h63 := isQROf_of_isSquare 63 288872697407275667 (by decide) qr_63 hsq
        have h25 := isQROf_of_isSquare 25 19483219 (by decide) qr_25 hsq
        have hsqrt : isqrt256 (w * w) = w := isqrt256_sq w hw255
        rw [hrem] at hok
        simp [h63, h25, hsqrt] at hok
        exact not_hasSq_of_check24 hok
      · exact checkV_sound e u R fuel (v0 + 2) hrest v w hsum hvw
          (by omega) (by omega) (by omega) hw255

private def checkU (e R0 : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | fuel + 1, u =>
    let u2 := u * u
    if 3 * u2 > R0 then true
    else
      checkV e u (R0 - u2) 85 u && checkU e R0 fuel (u + 2)

private lemma checkU_sound (e R0 : ℕ) (hR0 : R0 ≤ 56271) :
    ∀ fuel u0 : ℕ, checkU e R0 fuel u0 = true →
      ∀ u v w : ℕ, u * u + v * v + w * w = R0 → u ≤ v → v ≤ w →
        u0 ≤ u → (u - u0) % 2 = 0 → (v - u) % 2 = 0 →
        u - u0 < 2 * fuel → w ≤ 255 →
        ¬ HasSq e u v w
  | 0, u0, _, u, v, w, _, _, _, _, _, _, hlt, _ => by omega
  | fuel + 1, u0, hchk, u, v, w, hsum, huv, hvw, hu0, hparu, hparv, hlt, hw255 => by
    unfold checkU at hchk
    by_cases hstop : 3 * (u0 * u0) > R0
    · have h1 : u0 * u0 ≤ u * u := Nat.mul_le_mul hu0 hu0
      have h2 : u * u ≤ v * v := Nat.mul_le_mul huv huv
      have h3 : v * v ≤ w * w := Nat.mul_le_mul hvw hvw
      omega
    · simp only [hstop, ↓reduceIte, Bool.and_eq_true] at hchk
      rcases hchk with ⟨hV, hrest⟩
      by_cases hu : u = u0
      · subst hu
        have hvlt : v ≤ 167 := by
          by_contra h
          have : v ≥ 168 := by omega
          have h1 : 168 * 168 ≤ v * v := Nat.mul_le_mul this this
          have h2 : v * v ≤ w * w := Nat.mul_le_mul hvw hvw
          omega
        exact checkV_sound e u (R0 - u * u) 85 u hV v w (by omega) hvw huv hparv
          (by omega) hw255
      · exact checkU_sound e R0 hR0 fuel (u0 + 2) hrest u v w hsum huv hvw
          (by omega) (by omega) hparv (by omega) hw255

private def checkM (m : ℕ) : Bool :=
  let e := 4 * m + 2
  let e2 := e * e
  if e2 ≥ 56271 then true
  else checkU e (56271 - e2) 70 1

private def checkRange (lo count : ℕ) : Bool :=
  match count with
  | 0 => true
  | k + 1 => checkM lo && checkRange (lo + 1) k

private lemma checkRange_sound :
    ∀ count lo : ℕ, checkRange lo count = true →
      ∀ m : ℕ, lo ≤ m → m < lo + count → checkM m = true
  | 0, lo, _, m, h1, h2 => by omega
  | k + 1, lo, hchk, m, h1, h2 => by
    simp only [checkRange, Bool.and_eq_true] at hchk
    by_cases hm : m = lo
    · subst hm; exact hchk.1
    · exact checkRange_sound k (lo + 1) hchk.2 m (by omega) (by omega)

set_option maxHeartbeats 2000000 in
private lemma range_0_10 : checkRange 0 10 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
private lemma range_10_10 : checkRange 10 10 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
private lemma range_20_10 : checkRange 20 10 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
private lemma range_30_10 : checkRange 30 10 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
private lemma range_40_10 : checkRange 40 10 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
private lemma range_50_10 : checkRange 50 10 = true := by decide +kernel

private lemma all_m_ok (m : ℕ) (hm : m < 60) : checkM m = true := by
  by_cases h10 : m < 10
  · exact checkRange_sound 10 0 range_0_10 m (by omega) h10
  · by_cases h20 : m < 20
    · exact checkRange_sound 10 10 range_10_10 m (by omega) h20
    · by_cases h30 : m < 30
      · exact checkRange_sound 10 20 range_20_10 m (by omega) h30
      · by_cases h40 : m < 40
        · exact checkRange_sound 10 30 range_30_10 m (by omega) h40
        · by_cases h50 : m < 50
          · exact checkRange_sound 10 40 range_40_10 m (by omega) h50
          · exact checkRange_sound 10 50 range_50_10 m (by omega) hm

private lemma sq_mod_eight (a : ℕ) :
    (a % 4 = 0 ∧ (a ^ 2) % 8 = 0) ∨
    (a % 4 = 2 ∧ (a ^ 2) % 8 = 4) ∨
    (a % 2 = 1 ∧ (a ^ 2) % 8 = 1) := by
  have h : a = 4 * (a / 4) + a % 4 := (Nat.div_add_mod a 4).symm
  have hr : a % 4 < 4 := Nat.mod_lt a (by decide)
  set q := a / 4
  set r := a % 4
  have hsq : a ^ 2 = 16 * q ^ 2 + 8 * q * r + r ^ 2 := by rw [h]; ring
  interval_cases r
  · left; exact ⟨rfl, by omega⟩
  · right; right; exact ⟨by omega, by omega⟩
  · right; left; exact ⟨rfl, by omega⟩
  · right; right; exact ⟨by omega, by omega⟩

private lemma parity_decomp {x y z w : ℕ} (hsum : 56271 = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) :
    (x % 4 = 2 ∧ y % 2 = 1 ∧ z % 2 = 1 ∧ w % 2 = 1) ∨
    (y % 4 = 2 ∧ x % 2 = 1 ∧ z % 2 = 1 ∧ w % 2 = 1) ∨
    (z % 4 = 2 ∧ x % 2 = 1 ∧ y % 2 = 1 ∧ w % 2 = 1) ∨
    (w % 4 = 2 ∧ x % 2 = 1 ∧ y % 2 = 1 ∧ z % 2 = 1) := by
  have hx := sq_mod_eight x
  have hy := sq_mod_eight y
  have hz := sq_mod_eight z
  have hw := sq_mod_eight w
  have hmod : (x ^ 2 % 8 + y ^ 2 % 8 + z ^ 2 % 8 + w ^ 2 % 8) % 8 = 7 := by omega
  rcases hx with ⟨_, hx⟩ | ⟨hx4, hx⟩ | ⟨hx1, hx⟩ <;>
    rcases hy with ⟨_, hy⟩ | ⟨hy4, hy⟩ | ⟨hy1, hy⟩ <;>
    rcases hz with ⟨_, hz⟩ | ⟨hz4, hz⟩ | ⟨hz1, hz⟩ <;>
    rcases hw with ⟨_, hw⟩ | ⟨hw4, hw⟩ | ⟨hw1, hw⟩ <;>
    omega

private lemma canonical_impossible {e u v w : ℕ}
    (he4 : e % 4 = 2) (hu1 : u % 2 = 1) (hv1 : v % 2 = 1) (hw1 : w % 2 = 1)
    (huv : u ≤ v) (hvw : v ≤ w)
    (hsum : 56271 = e ^ 2 + u ^ 2 + v ^ 2 + w ^ 2) :
    ¬ HasSq e u v w := by
  set m := e / 4
  have he : e = 4 * m + 2 := by omega
  have he2 : e * e < 56271 := by
    have : u * u ≥ 1 := by
      have : u ≥ 1 := by omega
      exact Nat.mul_le_mul this this
    nlinarith
  have hm : m < 60 := by
    by_contra h
    have : e ≥ 242 := by omega
    nlinarith
  have hchk := all_m_ok m hm
  unfold checkM at hchk
  have hnotge : ¬ (4 * m + 2) * (4 * m + 2) ≥ 56271 := by rw [← he]; omega
  simp only [hnotge, ↓reduceIte] at hchk
  rw [← he] at hchk
  have hu_le : u ≤ 137 := by
    by_contra h
    have : u ≥ 138 := by omega
    nlinarith
  have hw_le : w ≤ 255 := by
    by_contra h
    have : w ≥ 256 := by omega
    nlinarith
  have hsub : u * u + v * v + w * w = 56271 - e * e := by
    simp only [sq] at hsum
    omega
  exact checkU_sound e (56271 - e * e) (by omega) 70 1 hchk u v w
    hsub huv hvw (by omega) (by omega) (by omega) (by omega) hw_le

private lemma sort3_impossible {e a b c : ℕ}
    (he4 : e % 4 = 2) (ha1 : a % 2 = 1) (hb1 : b % 2 = 1) (hc1 : c % 2 = 1)
    (hsum : 56271 = e ^ 2 + a ^ 2 + b ^ 2 + c ^ 2) :
    ¬ HasSq e a b c := by
  intro hsq
  by_cases hab : a ≤ b
  · by_cases hbc : b ≤ c
    · exact canonical_impossible he4 ha1 hb1 hc1 hab hbc hsum hsq
    · by_cases hac : a ≤ c
      · exact canonical_impossible he4 ha1 hc1 hb1 hac (by omega) (by linarith) (hasSq_swap34 hsq)
      · exact canonical_impossible he4 hc1 ha1 hb1 (by omega) hab (by linarith)
          (hasSq_swap23 (hasSq_swap34 hsq))
  · by_cases hac : a ≤ c
    · exact canonical_impossible he4 hb1 ha1 hc1 (by omega) hac (by linarith) (hasSq_swap23 hsq)
    · by_cases hbc : b ≤ c
      · exact canonical_impossible he4 hb1 hc1 ha1 hbc (by omega) (by linarith)
          (hasSq_swap34 (hasSq_swap23 hsq))
      · exact canonical_impossible he4 hc1 hb1 ha1 (by omega) (by omega) (by linarith)
          (hasSq_swap23 (hasSq_swap34 (hasSq_swap23 hsq)))

end OeisA261876Disproof

theorem OMA.disproof : ¬ (type_of% @OeisA261876.conjecture_3) := by
  intro h
  have ht : (42, 98, 14) ∈ OeisA261876.triples := by decide
  rcases h (42, 98, 14) ht 56271 with ⟨x, y, z, w, hsum, hsq⟩
  have hHas : OeisA261876Disproof.HasSq x y z w := by
    refine ⟨x, y, z, by simp, ?_⟩
    simpa [OeisA261876Disproof.evalTriple, sq] using hsq
  rcases OeisA261876Disproof.parity_decomp hsum with
    ⟨hx4, hy1, hz1, hw1⟩ | ⟨hy4, hx1, hz1, hw1⟩ | ⟨hz4, hx1, hy1, hw1⟩ | ⟨hw4, hx1, hy1, hz1⟩
  · exact OeisA261876Disproof.sort3_impossible hx4 hy1 hz1 hw1 hsum hHas
  · exact OeisA261876Disproof.sort3_impossible hy4 hx1 hz1 hw1 (by linarith)
      (OeisA261876Disproof.hasSq_swap12 hHas)
  · exact OeisA261876Disproof.sort3_impossible hz4 hy1 hx1 hw1 (by linarith)
      (OeisA261876Disproof.hasSq_swap13 hHas)
  · exact OeisA261876Disproof.sort3_impossible hw4 hy1 hz1 hx1 (by linarith)
      (OeisA261876Disproof.hasSq_swap14 hHas)
