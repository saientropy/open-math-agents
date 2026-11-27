import FormalConjectures.OEIS.«79727»
import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Proof of Peter Bala's Conjecture 4 for OEIS A079727

For any finite set `S` of primes in OEIS A003625 (`p ≡ 3, 5, 6 (mod 7)`), letting
`N = ∏ p ∈ S, p`, we prove `N^2 ∣ a ((N - 1) / 2)`.
-/

open scoped BigOperators
open Polynomial Finset Nat

namespace OeisA79727Conjecture4

/- ### Section 1: The quadratic integer ring `R[ω] / (ω^2 - ω + 2)` -/

structure ZOmega (R : Type*) where
  re : R
  im : R

namespace ZOmega

lemma ext_iff {R : Type*} {x y : ZOmega R} : x = y ↔ x.re = y.re ∧ x.im = y.im := by
  cases x; cases y; simp

lemma ext {R : Type*} {x y : ZOmega R} (hre : x.re = y.re) (him : x.im = y.im) : x = y :=
  ext_iff.mpr ⟨hre, him⟩

instance {R : Type*} [CommRing R] : Zero (ZOmega R) := ⟨⟨0, 0⟩⟩
instance {R : Type*} [CommRing R] : One (ZOmega R) := ⟨⟨1, 0⟩⟩
instance {R : Type*} [CommRing R] : Add (ZOmega R) := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance {R : Type*} [CommRing R] : Neg (ZOmega R) := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance {R : Type*} [CommRing R] : Sub (ZOmega R) := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩
instance {R : Type*} [CommRing R] : Mul (ZOmega R) :=
  ⟨fun x y => ⟨x.re * y.re - 2 * x.im * y.im, x.re * y.im + x.im * y.re + x.im * y.im⟩⟩

@[simp] lemma zero_re {R : Type*} [CommRing R] : (0 : ZOmega R).re = 0 := rfl
@[simp] lemma zero_im {R : Type*} [CommRing R] : (0 : ZOmega R).im = 0 := rfl
@[simp] lemma one_re {R : Type*} [CommRing R] : (1 : ZOmega R).re = 1 := rfl
@[simp] lemma one_im {R : Type*} [CommRing R] : (1 : ZOmega R).im = 0 := rfl
@[simp] lemma add_re {R : Type*} [CommRing R] (x y : ZOmega R) : (x + y).re = x.re + y.re := rfl
@[simp] lemma add_im {R : Type*} [CommRing R] (x y : ZOmega R) : (x + y).im = x.im + y.im := rfl
@[simp] lemma neg_re {R : Type*} [CommRing R] (x : ZOmega R) : (-x).re = -x.re := rfl
@[simp] lemma neg_im {R : Type*} [CommRing R] (x : ZOmega R) : (-x).im = -x.im := rfl
@[simp] lemma sub_re {R : Type*} [CommRing R] (x y : ZOmega R) : (x - y).re = x.re - y.re := rfl
@[simp] lemma sub_im {R : Type*} [CommRing R] (x y : ZOmega R) : (x - y).im = x.im - y.im := rfl
@[simp] lemma mul_re {R : Type*} [CommRing R] (x y : ZOmega R) :
    (x * y).re = x.re * y.re - 2 * x.im * y.im := rfl
@[simp] lemma mul_im {R : Type*} [CommRing R] (x y : ZOmega R) :
    (x * y).im = x.re * y.im + x.im * y.re + x.im * y.im := rfl

instance {R : Type*} [CommRing R] : CommRing (ZOmega R) where
  add_assoc a b c := ext (add_assoc _ _ _) (add_assoc _ _ _)
  zero_add a := ext (zero_add _) (zero_add _)
  add_zero a := ext (add_zero _) (add_zero _)
  nsmul := nsmulRec
  add_comm a b := ext (add_comm _ _) (add_comm _ _)
  zsmul := zsmulRec
  neg_add_cancel a := ext (neg_add_cancel _) (neg_add_cancel _)
  sub_eq_add_neg a b := ext (sub_eq_add_neg _ _) (sub_eq_add_neg _ _)
  mul_assoc a b c := ext (by simp; ring) (by simp; ring)
  one_mul a := ext (by simp) (by simp)
  mul_one a := ext (by simp) (by simp)
  left_distrib a b c := ext (by simp; ring) (by simp; ring)
  right_distrib a b c := ext (by simp; ring) (by simp; ring)
  zero_mul a := ext (by simp) (by simp)
  mul_zero a := ext (by simp) (by simp)
  mul_comm a b := ext (by simp; ring) (by simp; ring)

@[simp] lemma natCast_re {R : Type*} [CommRing R] (n : ℕ) : (n : ZOmega R).re = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih]

@[simp] lemma natCast_im {R : Type*} [CommRing R] (n : ℕ) : (n : ZOmega R).im = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih]

@[simp] lemma intCast_re {R : Type*} [CommRing R] (n : ℤ) : (n : ZOmega R).re = n := by
  cases n <;> simp

@[simp] lemma intCast_im {R : Type*} [CommRing R] (n : ℤ) : (n : ZOmega R).im = 0 := by
  cases n <;> simp

@[simp] lemma ofNat_re {R : Type*} [CommRing R] (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : ZOmega R).re = OfNat.ofNat n := by
  rw [← Nat.cast_ofNat (R := ZOmega R), natCast_re, Nat.cast_ofNat]

@[simp] lemma ofNat_im {R : Type*} [CommRing R] (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : ZOmega R).im = 0 := by
  rw [← Nat.cast_ofNat (R := ZOmega R), natCast_im]

def of {R : Type*} [CommRing R] : R →+* ZOmega R where
  toFun r := ⟨r, 0⟩
  map_one' := rfl
  map_mul' a b := ext (by simp) (by simp)
  map_zero' := rfl
  map_add' a b := ext (by simp) (by simp)

@[simp] lemma of_re {R : Type*} [CommRing R] (r : R) : (of r).re = r := rfl
@[simp] lemma of_im {R : Type*} [CommRing R] (r : R) : (of r).im = 0 := rfl

def omega {R : Type*} [CommRing R] : ZOmega R := ⟨0, 1⟩
def x0 {R : Type*} [CommRing R] : ZOmega R := ⟨2, -3⟩

lemma x0_mul_one_sub {R : Type*} [CommRing R] :
    (x0 : ZOmega R) * (1 - x0) = 16 := by
  apply ext <;> simp [x0] <;> ring

lemma neg_x0_mul_one_sub {R : Type*} [CommRing R] :
    (x0 : ZOmega R) ^ 2 - x0 = -16 := by
  apply ext <;> simp [x0, pow_two] <;> ring

lemma two_omega_sub_one_sq {R : Type*} [CommRing R] :
    (2 * (omega : ZOmega R) - 1) ^ 2 = -7 := by
  apply ext <;> simp [omega, pow_two] <;> ring

def mapRingHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    ZOmega R →+* ZOmega S where
  toFun x := ⟨f x.re, f x.im⟩
  map_one' := ext (map_one f) (map_zero f)
  map_mul' a b := ext (by simp [map_sub, map_mul, map_ofNat]) (by simp [map_add, map_mul])
  map_zero' := ext (map_zero f) (map_zero f)
  map_add' a b := ext (map_add f _ _) (map_add f _ _)

lemma mapRingHom_x0 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    mapRingHom f (x0 : ZOmega R) = (x0 : ZOmega S) := by
  apply ext <;> simp [mapRingHom, x0, map_ofNat]

end ZOmega

/- ### Section 2: Quadratic reciprocity for `-7` and `OeisA3625.A` -/

lemma A3625_ne_two {p : ℕ} (hp : OeisA3625.A p) : p ≠ 2 := by
  rcases hp with ⟨_, h | h | h⟩ <;> omega

lemma A3625_ne_seven {p : ℕ} (hp : OeisA3625.A p) : p ≠ 7 := by
  rcases hp with ⟨_, h | h | h⟩ <;> omega

lemma A3625_odd {p : ℕ} (hp : OeisA3625.A p) : Odd p :=
  hp.1.odd_of_ne_two (A3625_ne_two hp)

lemma A3625_three_le {p : ℕ} (hp : OeisA3625.A p) : 3 ≤ p := by
  have := hp.1.two_le
  have := A3625_ne_two hp
  omega

private lemma zmod7_ne_zero_356 (r : ℕ) (hr : r = 3 ∨ r = 5 ∨ r = 6) : ((r : ℤ) : ZMod 7) ≠ 0 := by
  rcases hr with rfl | rfl | rfl <;> decide

private lemma zmod7_pow_356 (r : ℕ) (hr : r = 3 ∨ r = 5 ∨ r = 6) :
    ((r : ℤ) : ZMod 7) ^ (7 / 2) = (-1 : ZMod 7) := by
  rcases hr with rfl | rfl | rfl <;> decide

private lemma zmod7_one_ne_neg_one : ((1 : ℤ) : ZMod 7) ≠ (-1 : ZMod 7) := by decide

private lemma leg7_val (r : ℕ) (hr : r = 3 ∨ r = 5 ∨ r = 6) :
    have : Fact (Nat.Prime 7) := ⟨by decide⟩
    legendreSym 7 (r : ℤ) = -1 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hne0 : ((r : ℤ) : ZMod 7) ≠ 0 := zmod7_ne_zero_356 r hr
  have hpow7 : ((legendreSym 7 (r : ℤ) : ℤ) : ZMod 7) = (-1 : ZMod 7) := by
    rw [legendreSym.eq_pow]
    exact zmod7_pow_356 r hr
  rcases legendreSym.eq_one_or_neg_one 7 hne0 with h1 | hm1
  · rw [h1] at hpow7
    exact absurd hpow7 zmod7_one_ne_neg_one
  · exact hm1

private lemma prime_dvd_factorial_le {p k : ℕ} (hp : p.Prime) (hd : p ∣ k !) : p ≤ k := by
  induction k with
  | zero =>
    simp only [Nat.factorial_zero] at hd
    have := Nat.le_of_dvd (by decide) hd
    have := hp.two_le; omega
  | succ k ih =>
    rw [Nat.factorial_succ] at hd
    rcases hp.dvd_mul.mp hd with h1 | h2
    · exact Nat.le_of_dvd (Nat.succ_pos k) h1
    · exact le_trans (ih h2) (Nat.le_succ k)

private lemma prime_dvd_choose_self {p j : ℕ} (hp : p.Prime) (hj0 : 0 < j) (hjp : j < p) :
    p ∣ p.choose j := by
  have heq : j * p.choose j = p * (p - 1).choose (j - 1) := by
    have h := Nat.add_one_mul_choose_eq (p - 1) (j - 1)
    rw [show p - 1 + 1 = p by omega, show j - 1 + 1 = j by omega] at h
    linarith
  have hcop : Nat.Coprime p j := hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd hj0 hd; omega)
  exact hcop.dvd_of_dvd_mul_left ⟨(p - 1).choose (j - 1), heq⟩

lemma neg_seven_pow_half {p : ℕ} [Fact p.Prime] (hp : OeisA3625.A p) :
    ((-7 : ZMod p) ^ ((p - 1) / 2)) = -1 := by
  have hp2 : p ≠ 2 := A3625_ne_two hp
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (A3625_odd hp)
  have hdiv : (p - 1) / 2 = p / 2 := by omega
  rw [hdiv]
  have hpow : ((-7 : ZMod p) ^ (p / 2)) = (legendreSym p (-7) : ZMod p) := by
    have := legendreSym.eq_pow p (-7 : ℤ)
    simpa using this.symm
  rw [hpow]
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hmul : legendreSym p (-7) = legendreSym p (-1) * legendreSym p 7 := by
    have := legendreSym.mul p (-1) 7
    simpa using this
  have hneg1 : legendreSym p (-1) = (-1 : ℤ) ^ (p / 2) := by
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_eq_neg_one_pow hodd]
  have hqr : legendreSym 7 p = (-1 : ℤ) ^ (p / 2 * (7 / 2)) * legendreSym p 7 :=
    legendreSym.quadratic_reciprocity' hp2 (by decide)
  have hleg7 : legendreSym p (-7) = legendreSym 7 p := by
    rw [hmul, hneg1, hqr]
    congr 1
    rw [show (7 : ℕ) / 2 = 3 by decide, mul_comm (p / 2) 3, pow_mul]
    norm_num
  rw [hleg7]
  have hmod : legendreSym 7 (p : ℤ) = legendreSym 7 ((p % 7 : ℕ) : ℤ) := by
    rw [legendreSym.mod 7 (p : ℤ)]
    congr 1
  rw [hmod, leg7_val (p % 7) hp.2]
  simp

/- ### Section 3: Lemma A (`aeval x0 (shiftedLegendre m) = 0` in `ZOmega (ZMod p)`) -/

private noncomputable def veluD : ℤ[X] := 1 + 7 * X - 21 * X ^ 2 - 91 * X ^ 3
private noncomputable def veluN : ℤ[X] :=
  1 + 14 * X + 343 * X ^ 2 - 588 * X ^ 3 - 24353 * X ^ 4 - 120050 * X ^ 5
    - 285719 * X ^ 6 - 422576 * X ^ 7
private noncomputable def veluQs : ℤ[X] := 1 - 35 * X ^ 2 - 98 * X ^ 3
private noncomputable def veluW : ℤ[X] :=
  veluN * veluD - X * derivative veluN * veluD + 2 * X * veluN * derivative veluD

private lemma derivative_veluD :
    derivative veluD = 7 - 42 * X - 273 * X ^ 2 := by
  simp only [veluD, derivative_sub, derivative_add, derivative_one, derivative_mul,
    derivative_X, derivative_pow, derivative_ofNat, Nat.cast_ofNat, map_ofNat]
  ring

private lemma derivative_veluN :
    derivative veluN =
      14 + 686 * X - 1764 * X ^ 2 - 97412 * X ^ 3 - 600250 * X ^ 4
        - 1714314 * X ^ 5 - 2958032 * X ^ 6 := by
  simp only [veluN, derivative_sub, derivative_add, derivative_one, derivative_mul,
    derivative_X, derivative_pow, derivative_ofNat, Nat.cast_ofNat, map_ofNat]
  ring

private noncomputable def polyOfList : List ℤ → ℤ[X]
  | [] => 0
  | a :: l => C a + X * polyOfList l

private def listAdd : List ℤ → List ℤ → List ℤ
  | [], l => l
  | l, [] => l
  | a :: l1, b :: l2 => (a + b) :: listAdd l1 l2

private def listScale (c : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: l => (c * a) :: listScale c l

private def listMul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: l1, l2 => listAdd (listScale a l2) (0 :: listMul l1 l2)

private lemma polyOfList_add (l1 l2 : List ℤ) :
    polyOfList (listAdd l1 l2) = polyOfList l1 + polyOfList l2 := by
  induction l1 generalizing l2 with
  | nil => simp [listAdd, polyOfList]
  | cons a l1 ih =>
    cases l2 with
    | nil => simp [listAdd, polyOfList]
    | cons b l2 =>
      simp only [listAdd, polyOfList, ih, map_add]
      ring

private lemma polyOfList_scale (c : ℤ) (l : List ℤ) :
    polyOfList (listScale c l) = C c * polyOfList l := by
  induction l with
  | nil => simp [listScale, polyOfList]
  | cons a l ih =>
    simp only [listScale, polyOfList, ih, map_mul]
    ring

private lemma polyOfList_mul (l1 l2 : List ℤ) :
    polyOfList (listMul l1 l2) = polyOfList l1 * polyOfList l2 := by
  induction l1 with
  | nil => simp [listMul, polyOfList]
  | cons a l1 ih =>
    simp only [listMul, polyOfList_add, polyOfList_scale, polyOfList, map_zero, zero_add, ih]
    ring

private lemma veluD_eq_list : veluD = polyOfList [1, 7, -21, -91] := by
  simp only [veluD, polyOfList, map_one, map_neg, map_ofNat]
  ring

private lemma veluN_eq_list :
    veluN = polyOfList [1, 14, 343, -588, -24353, -120050, -285719, -422576] := by
  simp only [veluN, polyOfList, map_one, map_neg, map_ofNat]
  ring

private lemma veluQs_eq_list : veluQs = polyOfList [1, 0, -35, -98] := by
  simp only [veluQs, polyOfList, map_one, map_zero, map_neg, map_ofNat]
  ring

private def listNorm : List ℤ → List ℤ
  | [] => []
  | a :: l =>
    match listNorm l with
    | [] => if a = 0 then [] else [a]
    | l' => a :: l'

private lemma polyOfList_norm (l : List ℤ) : polyOfList (listNorm l) = polyOfList l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [listNorm]
    cases h : listNorm l with
    | nil =>
      have hl : polyOfList l = 0 := by rw [← ih, h]; rfl
      split_ifs with ha
      · simp [polyOfList, ha, hl]
      · simp [polyOfList, hl]
    | cons b l' =>
      have hl : polyOfList l = polyOfList (b :: l') := by rw [← ih, h]
      simp [polyOfList, hl]

private lemma veluW_eq_list :
    veluW = polyOfList [1, 21, -252, 1764, 43806, 519302, 3834740, 15183924, 27681129, 8252237] := by
  have h1 : veluW =
      polyOfList [1, 14, 343, -588, -24353, -120050, -285719, -422576] * polyOfList [1, 7, -21, -91] +
      polyOfList [0, -14, -686, 1764, 97412, 600250, 1714314, 2958032] * polyOfList [1, 7, -21, -91] +
      polyOfList [1, 14, 343, -588, -24353, -120050, -285719, -422576] * polyOfList [0, 14, -84, -546] := by
    have hdN : -(X * derivative veluN) =
        polyOfList [0, -14, -686, 1764, 97412, 600250, 1714314, 2958032] := by
      rw [derivative_veluN]; simp only [polyOfList, map_zero, map_neg, map_ofNat]; ring
    have hdD : 2 * X * derivative veluD = polyOfList [0, 14, -84, -546] := by
      rw [derivative_veluD]; simp only [polyOfList, map_zero, map_neg, map_ofNat]; ring
    calc veluW
        = veluN * veluD + (-(X * derivative veluN)) * veluD + veluN * (2 * X * derivative veluD) := by
          simp only [veluW]; ring
      _ = _ := by rw [hdN, hdD, veluN_eq_list, veluD_eq_list]
  rw [h1, ← polyOfList_mul, ← polyOfList_mul, ← polyOfList_mul, ← polyOfList_add, ← polyOfList_add,
    ← polyOfList_norm]
  exact congr_arg polyOfList (by decide +kernel)

private lemma velu_ring_identity :
    veluN ^ 3 - 1715 * X ^ 2 * veluD ^ 4 * veluN + 33614 * X ^ 3 * veluD ^ 6 =
      veluW ^ 2 * veluQs := by
  have hlhs : veluN ^ 3 - 1715 * X ^ 2 * veluD ^ 4 * veluN + 33614 * X ^ 3 * veluD ^ 6 =
      veluN * (veluN * veluN) +
      polyOfList [0, 0, -1715] * ((veluD * veluD) * (veluD * veluD) * veluN) +
      polyOfList [0, 0, 0, 33614] * ((veluD * veluD) * (veluD * veluD) * (veluD * veluD)) := by
    have c1 : (-1715 : ℤ[X]) * X ^ 2 = polyOfList [0, 0, -1715] := by
      simp only [polyOfList, map_zero, map_neg, map_ofNat]; ring
    have c2 : (33614 : ℤ[X]) * X ^ 3 = polyOfList [0, 0, 0, 33614] := by
      simp only [polyOfList, map_zero, map_ofNat]; ring
    rw [← c1, ← c2]; ring
  have hrhs : veluW ^ 2 * veluQs = (veluW * veluW) * veluQs := by ring
  rw [hlhs, hrhs, veluN_eq_list, veluD_eq_list, veluW_eq_list, veluQs_eq_list]
  simp only [← polyOfList_mul, ← polyOfList_add]
  rw [← polyOfList_norm, ← polyOfList_norm (listMul _ _)]
  exact congr_arg polyOfList (by decide +kernel)

private lemma X_pow_dvd_of_mul_eval_ne_zero {F : Type*} [Field F] :
    ∀ (k : ℕ) (A B : F[X]), A.eval 0 ≠ 0 → X ^ k ∣ A * B → X ^ k ∣ B
  | 0, _, _, _, _ => by simp
  | k + 1, A, B, hA, hdvd => by
    have hX : X ∣ A * B := dvd_trans (dvd_pow_self X (Nat.succ_ne_zero k)) hdvd
    have h0 : (A * B).eval 0 = 0 := by
      rcases hX with ⟨q, hq⟩
      simp [hq]
    rw [eval_mul] at h0
    have hB0 : B.eval 0 = 0 := (mul_eq_zero.mp h0).resolve_left hA
    have hXB : X ∣ B := by
      rw [X_dvd_iff, coeff_zero_eq_eval_zero]
      exact hB0
    rcases hXB with ⟨B', rfl⟩
    rw [show (X : F[X]) ^ (k + 1) = X * X ^ k by ring, mul_left_comm] at hdvd
    have hXne : (X : F[X]) ≠ 0 := X_ne_zero
    have hdvd' : X ^ k ∣ A * B' := (mul_dvd_mul_iff_left hXne).mp hdvd
    have ih := X_pow_dvd_of_mul_eval_ne_zero k A B' hA hdvd'
    rcases ih with ⟨q, hq⟩
    exact ⟨q, by rw [hq]; ring⟩

private lemma X_pow_dvd_derivative {R : Type*} [CommRing R] {k : ℕ} {A : R[X]}
    (h : X ^ (k + 1) ∣ A) : X ^ k ∣ derivative A := by
  rcases h with ⟨q, rfl⟩
  rw [derivative_mul, derivative_X_pow]
  refine dvd_add ?_ ?_
  · refine dvd_mul_of_dvd_left ?_ _
    exact dvd_mul_of_dvd_right (dvd_refl _) _
  · rw [pow_succ]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

private lemma X_pow_dvd_pow_p_sub_one {p : ℕ} [Fact p.Prime] {h : (ZMod p)[X]}
    (h0 : h.eval 0 = 1) : X ^ p ∣ h ^ p - 1 := by
  have hsub : (h - 1).eval 0 = 0 := by simp [h0]
  have hX : X ∣ h - 1 := by
    rw [X_dvd_iff, coeff_zero_eq_eval_zero]
    exact hsub
  rcases hX with ⟨q, hq⟩
  have hh : h = 1 + X * q := by linear_combination hq
  rw [hh, add_pow_char, one_pow, add_sub_cancel_left, mul_pow]
  exact dvd_mul_right _ _

private lemma X_pow_two_p_dvd_pow_p_sub_one {p : ℕ} [Fact p.Prime] {h : (ZMod p)[X]}
    (h0 : h.eval 0 = 1) : X ^ (2 * p) ∣ (h.comp (X ^ 2)) ^ p - 1 := by
  have hsub : (h - 1).eval 0 = 0 := by simp [h0]
  have hX : X ∣ h - 1 := by
    rw [X_dvd_iff, coeff_zero_eq_eval_zero]
    exact hsub
  rcases hX with ⟨q, hq⟩
  have hh : h = 1 + X * q := by linear_combination hq
  have hcomp : h.comp (X ^ 2) = 1 + X ^ 2 * q.comp (X ^ 2) := by
    rw [hh, add_comp, one_comp, mul_comp, X_comp]
  rw [hcomp, add_pow_char, one_pow, add_sub_cancel_left, mul_pow, ← pow_mul]
  exact dvd_mul_right _ _

private lemma X_pow_dvd_comp_of_dvd {R : Type*} [CommRing R] {k : ℕ} {f g v : R[X]}
    (hv : X ∣ v) (hfg : X ^ k ∣ f - g) : X ^ k ∣ f.comp v - g.comp v := by
  rcases hfg with ⟨q, hq⟩
  have hsub : f.comp v - g.comp v = (f - g).comp v := by rw [sub_comp]
  rw [hsub, hq, mul_comp, pow_comp, X_comp]
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hv k) _

private lemma X_pow_dvd_comp_right {R : Type*} [CommRing R] {k : ℕ} (f : R[X]) {v w : R[X]}
    (h : X ^ k ∣ v - w) : X ^ k ∣ f.comp v - f.comp w := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [add_comp, add_comp]
    have : p.comp v + q.comp v - (p.comp w + q.comp w) =
        (p.comp v - p.comp w) + (q.comp v - q.comp w) := by ring
    rw [this]
    exact dvd_add hp hq
  | monomial n a =>
    simp only [monomial_comp]
    have : C a * v ^ n - C a * w ^ n = C a * (v ^ n - w ^ n) := by ring
    rw [this]
    exact dvd_mul_of_dvd_right (dvd_trans h (sub_dvd_pow_sub_pow v w n)) _

private lemma coeff_sub_eq_zero_of_X_pow_dvd {R : Type*} [CommRing R] {k n : ℕ} {f g : R[X]}
    (h : X ^ k ∣ f - g) (hn : n < k) : f.coeff n = g.coeff n := by
  rcases h with ⟨q, hq⟩
  have h0 : (f - g).coeff n = 0 := by
    rw [hq, coeff_X_pow_mul']
    exact if_neg (not_le.mpr hn)
  rw [coeff_sub, sub_eq_zero] at h0
  exact h0

private lemma coeff_comp_X_pow_mul_C {R : Type*} [CommRing R] (f : R[X]) (c : R) (k : ℕ) :
    (f.comp (C c * X ^ 2)).coeff (2 * k) = c ^ k * f.coeff k := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [add_comp, coeff_add, coeff_add, mul_add, hp, hq]
  | monomial n a =>
    simp only [monomial_comp, mul_pow, ← C_pow, ← pow_mul, ← mul_assoc, ← C_mul,
      coeff_C_mul_X_pow, coeff_monomial]
    by_cases h : n = k
    · subst h; simp [mul_comm]
    · have h2 : 2 * k ≠ 2 * n := by omega
      simp [h, h2]

private lemma veluQs_pow_coeff_m_eq_zero {p : ℕ} [Fact p.Prime] (hp : OeisA3625.A p) :
    ((veluQs.map (Int.castRingHom (ZMod p))) ^ ((p - 1) / 2)).coeff ((p - 1) / 2) = 0 := by
  set m := (p - 1) / 2
  have hp2 : p ≠ 2 := A3625_ne_two hp
  have hp3 : 3 ≤ p := A3625_three_le hp
  have h2m : 2 * m = p - 1 := by
    have := Nat.odd_iff.mp (A3625_odd hp)
    omega
  set fmap : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  set D : (ZMod p)[X] := veluD.map fmap
  set N : (ZMod p)[X] := veluN.map fmap
  set Qs : (ZMod p)[X] := veluQs.map fmap
  set W : (ZMod p)[X] := veluW.map fmap
  set Dt2 : (ZMod p)[X] := D.comp (X ^ 2)
  set Nt2 : (ZMod p)[X] := N.comp (X ^ 2)
  set Q : (ZMod p)[X] := Qs.comp (X ^ 2)
  set P : (ZMod p)[X] := Qs.comp (C (-7 : ZMod p) * X ^ 2)
  set v : (ZMod p)[X] := X * Dt2 * Nt2 ^ m
  have hD0 : D.eval 0 = 1 := by simp [D, veluD]
  have hN0 : N.eval 0 = 1 := by simp [N, veluN]
  have hQs0 : Qs.eval 0 = 1 := by simp [Qs, veluQs]
  have hDt2_0 : Dt2.eval 0 = 1 := by simp [Dt2, eval_comp, hD0]
  have hNt2_0 : Nt2.eval 0 = 1 := by simp [Nt2, eval_comp, hN0]
  have hQ0 : Q.eval 0 = 1 := by simp [Q, eval_comp, hQs0]
  have hP0 : P.eval 0 = 1 := by simp [P, eval_comp, hQs0]
  have hv0 : v.eval 0 = 0 := by simp [v]
  have hv_dvd : X ∣ v := ⟨Dt2 * Nt2 ^ m, by simp only [v]; ring⟩
  -- Key relation: X^(2p+2) | v^2 * Nt2 - X^2 * Dt2^2
  have hNt2p : X ^ (2 * p) ∣ Nt2 ^ p - 1 := X_pow_two_p_dvd_pow_p_sub_one hN0
  have hv2N : X ^ (2 * p + 2) ∣ v ^ 2 * Nt2 - X ^ 2 * Dt2 ^ 2 := by
    have heq : v ^ 2 * Nt2 - X ^ 2 * Dt2 ^ 2 = X ^ 2 * Dt2 ^ 2 * (Nt2 ^ p - 1) := by
      have hp_eq : 2 * m + 1 = p := by omega
      calc v ^ 2 * Nt2 - X ^ 2 * Dt2 ^ 2
          = X ^ 2 * Dt2 ^ 2 * (Nt2 ^ (2 * m + 1) - 1) := by
            simp only [v]; ring
        _ = X ^ 2 * Dt2 ^ 2 * (Nt2 ^ p - 1) := by rw [hp_eq]
    rw [heq]
    rcases hNt2p with ⟨q, hq⟩
    refine ⟨Dt2 ^ 2 * q, ?_⟩
    rw [hq]; ring
  -- Differentiate hv2N to get relation for v'
  have hdv2N : X ^ (2 * p + 1) ∣ derivative (v ^ 2 * Nt2 - X ^ 2 * Dt2 ^ 2) :=
    X_pow_dvd_derivative hv2N
  have hderiv_calc : derivative (v ^ 2 * Nt2 - X ^ 2 * Dt2 ^ 2) =
      2 * v * derivative v * Nt2 + 2 * X * v ^ 2 * (derivative N).comp (X ^ 2)
        - 2 * X * Dt2 ^ 2 - 4 * X ^ 3 * Dt2 * (derivative D).comp (X ^ 2) := by
    have hdN : derivative Nt2 = 2 * X * (derivative N).comp (X ^ 2) := by
      simp only [Nt2, derivative_comp, derivative_X_pow, Nat.cast_ofNat, map_ofNat]
      ring
    have hdD : derivative Dt2 = 2 * X * (derivative D).comp (X ^ 2) := by
      simp only [Dt2, derivative_comp, derivative_X_pow, Nat.cast_ofNat, map_ofNat]
      ring
    simp only [derivative_sub, derivative_mul, derivative_pow, derivative_X,
      Nat.cast_ofNat, map_ofNat, hdN, hdD]
    ring
  rw [hderiv_calc] at hdv2N
  have hWcomp : W.comp (X ^ 2) =
      Nt2 * Dt2 - X ^ 2 * (derivative N).comp (X ^ 2) * Dt2
        + 2 * X ^ 2 * Nt2 * (derivative D).comp (X ^ 2) := by
    have hWmap : W = N * D - X * derivative N * D + 2 * X * N * derivative D := by
      simp only [W, veluW, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_ofNat, Polynomial.map_X, derivative_map, N, D]
    rw [hWmap]
    simp only [add_comp, sub_comp, mul_comp, X_comp, ofNat_comp, Nat.cast_ofNat, Nt2, Dt2]
  -- Show X^(2p+1) | 2 * v * v' * Nt2^2 - 2 * X * Dt2 * W(X^2)
  have hlin : X ^ (2 * p + 1) ∣ 2 * v * derivative v * Nt2 ^ 2 - 2 * X * Dt2 * W.comp (X ^ 2) := by
    have hid : 2 * v * derivative v * Nt2 ^ 2 - 2 * X * Dt2 * W.comp (X ^ 2) =
        Nt2 * (2 * v * derivative v * Nt2 + 2 * X * v ^ 2 * (derivative N).comp (X ^ 2)
          - 2 * X * Dt2 ^ 2 - 4 * X ^ 3 * Dt2 * (derivative D).comp (X ^ 2))
        - 2 * X * (derivative N).comp (X ^ 2) * (v ^ 2 * Nt2 - X ^ 2 * Dt2 ^ 2) := by
      rw [hWcomp]; ring
    rw [hid]
    refine dvd_sub (dvd_mul_of_dvd_right hdv2N _) ?_
    have hv2N' : X ^ (2 * p + 1) ∣ v ^ 2 * Nt2 - X ^ 2 * Dt2 ^ 2 :=
      dvd_trans (pow_dvd_pow X (by omega)) hv2N
    exact dvd_mul_of_dvd_right hv2N' _
  -- Square hlin to get X^p | Nt2^3 * (v')^2 - W(X^2)^2
  have hsq : X ^ p ∣ Nt2 ^ 3 * (derivative v) ^ 2 - W.comp (X ^ 2) ^ 2 := by
    have hlin2 : X ^ (2 * p + 1) ∣
        (2 * v * derivative v * Nt2 ^ 2) ^ 2 - (2 * X * Dt2 * W.comp (X ^ 2)) ^ 2 := by
      have : (2 * v * derivative v * Nt2 ^ 2) ^ 2 - (2 * X * Dt2 * W.comp (X ^ 2)) ^ 2 =
          (2 * v * derivative v * Nt2 ^ 2 + 2 * X * Dt2 * W.comp (X ^ 2)) *
          (2 * v * derivative v * Nt2 ^ 2 - 2 * X * Dt2 * W.comp (X ^ 2)) := by ring
      rw [this]
      exact dvd_mul_of_dvd_right hlin _
    have hcomb : X ^ (2 * p + 1) ∣
        4 * X ^ 2 * Dt2 ^ 2 * (Nt2 ^ 3 * (derivative v) ^ 2 - W.comp (X ^ 2) ^ 2) := by
      have hid : 4 * X ^ 2 * Dt2 ^ 2 * (Nt2 ^ 3 * (derivative v) ^ 2 - W.comp (X ^ 2) ^ 2) =
          ((2 * v * derivative v * Nt2 ^ 2) ^ 2 - (2 * X * Dt2 * W.comp (X ^ 2)) ^ 2)
          - 4 * (derivative v) ^ 2 * Nt2 ^ 3 * (v ^ 2 * Nt2 - X ^ 2 * Dt2 ^ 2) := by ring
      rw [hid]
      exact dvd_sub hlin2 (dvd_mul_of_dvd_right (dvd_trans (pow_dvd_pow X (by omega)) hv2N) _)
    have hcomb' : X ^ (p + 2) ∣
        X ^ 2 * (4 * Dt2 ^ 2 * (Nt2 ^ 3 * (derivative v) ^ 2 - W.comp (X ^ 2) ^ 2)) := by
      have hle : p + 2 ≤ 2 * p + 1 := by omega
      have := dvd_trans (pow_dvd_pow X hle) hcomb
      convert this using 1; ring
    have hcancelX2 : X ^ p ∣
        4 * Dt2 ^ 2 * (Nt2 ^ 3 * (derivative v) ^ 2 - W.comp (X ^ 2) ^ 2) := by
      rw [pow_add, mul_comm (X ^ p)] at hcomb'
      exact (mul_dvd_mul_iff_left (pow_ne_zero 2 X_ne_zero)).mp hcomb'
    have h4D0 : (4 * Dt2 ^ 2).eval 0 ≠ 0 := by
      simp only [eval_mul, eval_pow, eval_ofNat, hDt2_0, one_pow, mul_one]
      have h2ne : (2 : ZMod p) ≠ 0 := by
        intro h2
        have h2d : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h2)
        have := Nat.le_of_dvd (by decide) h2d
        omega
      intro h4
      have : (2 : ZMod p) * 2 = 0 := by linear_combination h4
      exact h2ne ((mul_self_eq_zero).mp this)
    exact X_pow_dvd_of_mul_eval_ne_zero p _ _ h4D0 hcancelX2
  -- Use the Velu ring identity to deduce X^p | P.comp v - (v')^2 * Q
  have hPv : X ^ p ∣ P.comp v - (derivative v) ^ 2 * Q := by
    have hvelu_p : N ^ 3 - 1715 * X ^ 2 * D ^ 4 * N + 33614 * X ^ 3 * D ^ 6 = W ^ 2 * Qs := by
      have := congr_arg (Polynomial.map fmap) velu_ring_identity
      simpa only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_pow, Polynomial.map_ofNat, Polynomial.map_X, N, D, W, Qs] using this
    have hvelu_t2 : Nt2 ^ 3 - 1715 * X ^ 4 * Dt2 ^ 4 * Nt2 + 33614 * X ^ 6 * Dt2 ^ 6 =
        W.comp (X ^ 2) ^ 2 * Q := by
      have := congr_arg (fun r => r.comp (X ^ 2)) hvelu_p
      simp only [add_comp, sub_comp, mul_comp, pow_comp, ofNat_comp, X_comp] at this
      convert this using 1; ring
    have hP_eq : P = 1 - 1715 * X ^ 4 + 33614 * X ^ 6 := by
      have hQs_eq : Qs = 1 - 35 * X ^ 2 - 98 * X ^ 3 := by
        simp only [Qs, veluQs, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
          Polynomial.map_pow, Polynomial.map_ofNat, Polynomial.map_X]
      simp only [P, hQs_eq, sub_comp, one_comp, mul_comp, pow_comp, ofNat_comp, X_comp,
        Nat.cast_ofNat]
      have h1 : (C (-7 : ZMod p) * X ^ 2) ^ 2 = C (49 : ZMod p) * X ^ 4 := by
        rw [mul_pow, ← C_pow, ← pow_mul]
        congr 1; congr 1; ring
      have h2 : (C (-7 : ZMod p) * X ^ 2) ^ 3 = C (-343 : ZMod p) * X ^ 6 := by
        rw [mul_pow, ← C_pow, ← pow_mul]
        congr 1; congr 1; ring
      rw [h1, h2]
      simp only [map_neg, map_ofNat]
      ring
    have hPv_eq : P.comp v = 1 - 1715 * v ^ 4 + 33614 * v ^ 6 := by
      rw [hP_eq]
      simp only [add_comp, sub_comp, one_comp, mul_comp, pow_comp, ofNat_comp, X_comp,
        Nat.cast_ofNat]
    have hv2N_p : X ^ p ∣ v ^ 2 * Nt2 - X ^ 2 * Dt2 ^ 2 :=
      dvd_trans (pow_dvd_pow X (by omega)) hv2N
    have hNt3Pv : X ^ p ∣ Nt2 ^ 3 * P.comp v - W.comp (X ^ 2) ^ 2 * Q := by
      rw [hPv_eq, ← hvelu_t2]
      have hid : Nt2 ^ 3 * (1 - 1715 * v ^ 4 + 33614 * v ^ 6) -
          (Nt2 ^ 3 - 1715 * X ^ 4 * Dt2 ^ 4 * Nt2 + 33614 * X ^ 6 * Dt2 ^ 6) =
          -1715 * Nt2 * ((v ^ 2 * Nt2) ^ 2 - (X ^ 2 * Dt2 ^ 2) ^ 2) +
          33614 * ((v ^ 2 * Nt2) ^ 3 - (X ^ 2 * Dt2 ^ 2) ^ 3) := by ring
      rw [hid]
      refine dvd_add ?_ ?_
      · exact dvd_mul_of_dvd_right (dvd_trans hv2N_p (sub_dvd_pow_sub_pow _ _ 2)) _
      · exact dvd_mul_of_dvd_right (dvd_trans hv2N_p (sub_dvd_pow_sub_pow _ _ 3)) _
    have hNt3_diff : X ^ p ∣ Nt2 ^ 3 * (P.comp v - (derivative v) ^ 2 * Q) := by
      have hid : Nt2 ^ 3 * (P.comp v - (derivative v) ^ 2 * Q) =
          (Nt2 ^ 3 * P.comp v - W.comp (X ^ 2) ^ 2 * Q) -
          Q * (Nt2 ^ 3 * (derivative v) ^ 2 - W.comp (X ^ 2) ^ 2) := by ring
      rw [hid]
      exact dvd_sub hNt3Pv (dvd_mul_of_dvd_right hsq _)
    have hNt3_0 : (Nt2 ^ 3).eval 0 ≠ 0 := by simp [hNt2_0]
    exact X_pow_dvd_of_mul_eval_ne_zero p _ _ hNt3_0 hNt3_diff
  -- Deduce X^p | f.comp v * v' - g where f = P^m, g = Q^m
  set f : (ZMod p)[X] := P ^ m
  set g : (ZMod p)[X] := Q ^ m
  have hfg : X ^ p ∣ f.comp v * derivative v - g := by
    have hsq_eq : X ^ p ∣ Q * ((f.comp v * derivative v) ^ 2 - g ^ 2) := by
      have h1 : Q * (f.comp v * derivative v) ^ 2 - (P.comp v) ^ p =
          (P.comp v) ^ (2 * m) * ((derivative v) ^ 2 * Q - P.comp v) := by
        have hp_eq : 2 * m + 1 = p := by omega
        have hPpow : (P.comp v) ^ p = (P.comp v) ^ (2 * m + 1) := congrArg ((P.comp v) ^ ·) hp_eq.symm
        rw [hPpow]
        simp only [f, pow_comp]; ring
      have h2 : Q * g ^ 2 = Q ^ p := by
        have hp_eq : 2 * m + 1 = p := by omega
        have hQpow : Q ^ p = Q ^ (2 * m + 1) := congrArg (Q ^ ·) hp_eq.symm
        rw [hQpow]
        simp only [g]; ring
      have hid : Q * ((f.comp v * derivative v) ^ 2 - g ^ 2) =
          (Q * (f.comp v * derivative v) ^ 2 - (P.comp v) ^ p) +
          ((P.comp v) ^ p - 1) - (Q ^ p - 1) := by linear_combination -h2
      rw [hid, h1]
      refine dvd_sub (dvd_add ?_ ?_) (X_pow_dvd_pow_p_sub_one hQ0)
      · exact dvd_mul_of_dvd_right (by simpa using dvd_neg.mpr hPv) _
      · exact X_pow_dvd_pow_p_sub_one (by simp [eval_comp, hv0, hP0])
    have hfac : Q * ((f.comp v * derivative v) ^ 2 - g ^ 2) =
        (Q * (f.comp v * derivative v + g)) * (f.comp v * derivative v - g) := by ring
    rw [hfac] at hsq_eq
    have hdv0 : (derivative v).eval 0 = 1 := by
      have hdv : derivative v = Dt2 * Nt2 ^ m + X * derivative (Dt2 * Nt2 ^ m) := by
        have hv' : v = X * (Dt2 * Nt2 ^ m) := by simp only [v]; ring
        rw [hv', derivative_mul, derivative_X, one_mul]
      simp [hdv, hDt2_0, hNt2_0]
    have hne : (Q * (f.comp v * derivative v + g)).eval 0 ≠ 0 := by
      simp only [eval_mul, eval_add, eval_comp, hv0, hQ0, hdv0, one_mul, mul_one, f, g, eval_pow,
        hP0, one_pow]
      intro h2
      have h2' : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination h2
      have h2d : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2'
      have := Nat.le_of_dvd (by decide) h2d
      omega
    exact X_pow_dvd_of_mul_eval_ne_zero p _ _ hne hsq_eq
  -- Extract coefficient of X^(p-1) from f.comp v * v' ≡ g (mod X^p)
  have hcoeff_eq : (f.comp v * derivative v).coeff (p - 1) = g.coeff (p - 1) :=
    coeff_sub_eq_zero_of_X_pow_dvd hfg (by omega)
  have hcoeff_lhs : (f.comp v * derivative v).coeff (p - 1) = f.coeff (p - 1) := by
    have hf_sum : f = ∑ k ∈ range (f.natDegree + 1), C (f.coeff k) * X ^ k :=
      Polynomial.as_sum_range_C_mul_X_pow f
    conv_lhs => rw [hf_sum]
    rw [Polynomial.sum_comp, sum_mul, finsetSum_coeff]
    have hterm : ∀ k ∈ range (f.natDegree + 1),
        ((C (f.coeff k) * X ^ k).comp v * derivative v).coeff (p - 1) =
        if k = p - 1 then f.coeff (p - 1) else 0 := by
      intro k _
      rw [mul_comp, C_comp, pow_comp, X_comp, mul_assoc, coeff_C_mul]
      by_cases hk_eq : k = p - 1
      · subst hk_eq
        simp only [ite_true]
        -- Show (v^(p-1) * v').coeff (p-1) = 1
        set u : (ZMod p)[X] := Dt2 * Nt2 ^ m
        have hv_eq : v = X * u := by simp only [v, u]; ring
        have hu0 : u.eval 0 = 1 := by simp [u, hDt2_0, hNt2_0]
        have hdv : derivative v = u + X * derivative u := by
          rw [hv_eq, derivative_mul, derivative_X, one_mul]
        have hvp : v ^ (p - 1) * derivative v = X ^ (p - 1) * (u ^ (p - 1) * (u + X * derivative u)) := by
          rw [hdv, hv_eq, mul_pow]; ring
        rw [hvp, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_eval_zero]
        simp [hu0]
      · simp only [hk_eq, ite_false]
        by_cases hk_lt : k < p - 1
        · have hk1_ne : ((k + 1 : ℕ) : ZMod p) ≠ 0 := by
            intro h0
            have hd : p ∣ k + 1 := (ZMod.natCast_eq_zero_iff (k + 1) p).mp h0
            have := Nat.le_of_dvd (Nat.succ_pos k) hd
            omega
          have hd_pow : derivative (v ^ (k + 1)) = C ((k + 1 : ℕ) : ZMod p) * (v ^ k * derivative v) := by
            rw [derivative_pow]
            simp only [Nat.add_sub_cancel, C_eq_natCast]
            ring
          have hzero : (derivative (v ^ (k + 1))).coeff (p - 1) = 0 := by
            rw [coeff_derivative]
            have hp0 : (((p - 1 : ℕ) : ZMod p) + 1) = 0 := by
              calc (((p - 1 : ℕ) : ZMod p) + 1)
                  = (((p - 1 + 1 : ℕ) : ZMod p)) := by push_cast; ring
                _ = (p : ZMod p) := by rw [Nat.sub_add_cancel (by omega)]
                _ = 0 := ZMod.natCast_self p
            rw [hp0, mul_zero]
          rw [hd_pow, coeff_C_mul] at hzero
          have hvk : (v ^ k * derivative v).coeff (p - 1) = 0 :=
            (mul_eq_zero.mp hzero).resolve_left hk1_ne
          rw [hvk, mul_zero]
        · have hk_ge : p ≤ k := by omega
          have hdvd : X ^ p ∣ v ^ k * derivative v :=
            dvd_mul_of_dvd_left (dvd_trans (pow_dvd_pow X hk_ge) (pow_dvd_pow_of_dvd hv_dvd k)) _
          rcases hdvd with ⟨q, hq⟩
          rw [hq, coeff_X_pow_mul', if_neg (by omega), mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · rw [Finset.mem_range, not_lt] at hmem
      exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
  have hfg_coeff : f.coeff (p - 1) = g.coeff (p - 1) := by
    rw [← hcoeff_lhs, hcoeff_eq]
  -- Compare f.coeff (2*m) and g.coeff (2*m) via Qs^m
  have hf_comp : f = (Qs ^ m).comp (C (-7 : ZMod p) * X ^ 2) := by
    simp only [f, P, pow_comp]
  have hg_comp : g = (Qs ^ m).comp (C (1 : ZMod p) * X ^ 2) := by
    simp only [g, Q, pow_comp, map_one, one_mul]
  rw [← h2m, hf_comp, hg_comp, coeff_comp_X_pow_mul_C, coeff_comp_X_pow_mul_C,
    one_pow, one_mul, neg_seven_pow_half hp, neg_one_mul] at hfg_coeff
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h2
    have h2d : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h2)
    have := Nat.le_of_dvd (by decide) h2d
    omega
  have h2mul : (2 : ZMod p) * (Qs ^ m).coeff m = 0 := by linear_combination -hfg_coeff
  exact (mul_eq_zero.mp h2mul).resolve_left h2ne

private lemma reflect_pow_eq {R : Type*} [CommRing R] (f : R[X]) (d : ℕ) (hd : f.natDegree ≤ d) :
    ∀ k : ℕ, (f ^ k).reflect (d * k) = (f.reflect d) ^ k
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, pow_succ, mul_add, mul_one]
    have hdegk : (f ^ k).natDegree ≤ d * k := by
      rw [mul_comm]
      exact le_trans natDegree_pow_le (Nat.mul_le_mul_left k hd)
    rw [reflect_mul (f ^ k) f hdegk hd, reflect_pow_eq f d hd k]

private lemma shiftedLegendre_coeff_mod_p {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (k : ℕ) (hk : k ≤ (p - 1) / 2) :
    (((-1 : ℤ) ^ k * ((p - 1) / 2 + k).choose ((p - 1) / 2) : ℤ) : ZMod p) =
      (((p - 1) / 2).choose k : ZMod p) := by
  set m := (p - 1) / 2
  have h2m1 : 2 * m + 1 = p := by
    have := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2)
    omega
  have hk_lt : k < p := by omega
  have hfac_ne : (k ! : ZMod p) ≠ 0 := by
    intro h0
    have hd : p ∣ k ! := (ZMod.natCast_eq_zero_iff (k !) p).mp h0
    have hle : p ≤ k := prime_dvd_factorial_le Fact.out hd
    omega
  apply mul_left_cancel₀ hfac_ne
  have h1 : k ! * (m + k).choose m = ∏ j ∈ range k, (m + 1 + j) := by
    have hch : (m + k).choose m = (m + k).choose k := by
      rw [← Nat.choose_symm_add, add_comm]
    rw [hch, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]
    rw [← Finset.prod_range_reflect]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    omega
  have h2 : k ! * m.choose k = ∏ j ∈ range k, (m - j) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]
  have hlhs : (k ! : ZMod p) * (((-1 : ℤ) ^ k * ((m + k).choose m : ℤ) : ℤ) : ZMod p) =
      (-1 : ZMod p) ^ k * ((k ! * (m + k).choose m : ℕ) : ZMod p) := by
    push_cast; ring
  rw [hlhs, h1, ← Nat.cast_mul, h2, Nat.cast_prod, Nat.cast_prod]
  rw [show (-1 : ZMod p) ^ k = ∏ _j ∈ range k, (-1 : ZMod p) by simp, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hsum : ((m + 1 + j : ℕ) : ZMod p) + ((m - j : ℕ) : ZMod p) = 0 := by
    rw [← Nat.cast_add]
    have heq : m + 1 + j + (m - j) = p := by omega
    rw [heq, ZMod.natCast_self]
  linear_combination -hsum

lemma shiftedLegendre_eval_x0_eq_zero {p : ℕ} [Fact p.Prime] (hp : OeisA3625.A p) :
    aeval (ZOmega.x0 : ZOmega (ZMod p)) (shiftedLegendre ((p - 1) / 2)) = 0 := by
  set m := (p - 1) / 2
  have hp2 : p ≠ 2 := A3625_ne_two hp
  have hp7 : p ≠ 7 := A3625_ne_seven hp
  have hp3 : 3 ≤ p := A3625_three_le hp
  have h2m : 2 * m = p - 1 := by
    have := Nat.odd_iff.mp (A3625_odd hp)
    omega
  -- Step 1: [X^(p-1)] (X^3 - 35*X - 98)^m = 0 in ZMod p
  set F : (ZMod p)[X] := X ^ 3 - 35 * X - 98
  have hF_deg : F.natDegree ≤ 3 := by
    have h1 : ((X : (ZMod p)[X]) ^ 3 - 35 * X).natDegree ≤ 3 := by
      refine le_trans (natDegree_sub_le _ _) (max_le (by simp) ?_)
      refine le_trans natDegree_mul_le ?_
      simp
    refine le_trans (natDegree_sub_le _ _) (max_le h1 (by simp))
  have hF_refl : F.reflect 3 = veluQs.map (Int.castRingHom (ZMod p)) := by
    ext k
    simp only [coeff_reflect, veluQs, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_ofNat, Polynomial.map_X, F]
    by_cases hk : k ≤ 3
    · rw [revAt_le hk]
      interval_cases k <;> simp [coeff_X, coeff_one]
    · rw [revAt_eq_self_of_lt (by omega)]
      have h98 : (98 : (ZMod p)[X]) = C 98 := rfl
      rw [h98]
      simp [coeff_X, coeff_one, coeff_X_pow, coeff_C, show k ≠ 0 by omega, show 1 ≠ k by omega,
        show k ≠ 2 by omega, show k ≠ 3 by omega]
  have hFm_coeff : (F ^ m).coeff (p - 1) = 0 := by
    have href := reflect_pow_eq F 3 hF_deg m
    have h0 := veluQs_pow_coeff_m_eq_zero hp
    rw [← hF_refl, ← href, coeff_reflect, revAt_le (by omega)] at h0
    have hsub : 3 * m - m = p - 1 := by omega
    rwa [hsub] at h0
  -- Step 2: Map to ZOmega (ZMod p) and substitute x = a + b * u
  let b : ZOmega (ZMod p) := 2 * ZOmega.omega - 1
  let a : ZOmega (ZMod p) := -ZOmega.omega - 3
  let x0 : ZOmega (ZMod p) := ZOmega.x0
  set Fω : (ZOmega (ZMod p))[X] := F.map ZOmega.of
  have hFω_eq : Fω = X ^ 3 - 35 * X - 98 := by
    simp [Fω, F]
  have hsubst : Fω.comp (C a + C b * X) = C (b ^ 3) * (X * (X - 1) * (X - C x0)) := by
    rw [hFω_eq]
    simp only [sub_comp, pow_comp, mul_comp, ofNat_comp, X_comp, Nat.cast_ofNat]
    have hlhs : (C a + C b * X) ^ 3 - 35 * (C a + C b * X) - 98 =
        C (a ^ 3 - 35 * a - 98) + C (3 * a ^ 2 * b - 35 * b) * X
          + C (3 * a * b ^ 2) * X ^ 2 + C (b ^ 3) * X ^ 3 := by
      simp only [map_sub, map_mul, map_pow, map_ofNat]
      ring
    have hrhs : C (b ^ 3) * (X * (X - 1) * (X - C x0)) =
        C 0 + C (b ^ 3 * x0) * X + C (b ^ 3 * -(1 + x0)) * X ^ 2 + C (b ^ 3) * X ^ 3 := by
      simp only [map_zero, map_mul, map_neg, map_add, map_one]
      ring
    rw [hlhs, hrhs]
    have hc0 : a ^ 3 - 35 * a - 98 = 0 := by
      apply ZOmega.ext <;> simp [a, ZOmega.omega, pow_succ, pow_zero] <;> ring
    have hc1 : 3 * a ^ 2 * b - 35 * b = b ^ 3 * x0 := by
      apply ZOmega.ext <;> simp [a, b, x0, ZOmega.omega, ZOmega.x0, pow_succ, pow_zero] <;> ring
    have hc2 : 3 * a * b ^ 2 = b ^ 3 * -(1 + x0) := by
      apply ZOmega.ext <;> simp [a, b, x0, ZOmega.omega, ZOmega.x0, pow_succ, pow_zero] <;> ring
    rw [hc0, hc1, hc2]
  -- Step 3: Raise to m and compare coeff (p - 1)
  have hpow_eq : (Fω ^ m).comp (C a + C b * X) =
      C (b ^ (3 * m)) * (X * (X - 1) * (X - C x0)) ^ m := by
    rw [pow_comp, hsubst, mul_pow, ← C_pow, ← pow_mul]
  -- LHS coeff (p - 1) = 0
  have hlhs_zero : ((Fω ^ m).comp (C a + C b * X)).coeff (p - 1) = 0 := by
    have hdeg : (Fω ^ m).natDegree ≤ 3 * m := by
      rw [mul_comm 3 m]
      exact le_trans natDegree_pow_le (Nat.mul_le_mul_left m (le_trans natDegree_map_le hF_deg))
    have hsum : Fω ^ m = ∑ k ∈ range (3 * m + 1), C ((Fω ^ m).coeff k) * X ^ k :=
      Polynomial.as_sum_range_C_mul_X_pow' (Fω ^ m) (n := 3 * m + 1) (by omega)
    conv_lhs => rw [hsum]
    rw [Polynomial.sum_comp, finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    rw [mul_comp, C_comp, pow_comp, X_comp, coeff_C_mul]
    by_cases hkeq : k = p - 1
    · subst hkeq
      have hFmω : (Fω ^ m).coeff (p - 1) = 0 := by
        rw [show Fω ^ m = (F ^ m).map ZOmega.of by simp [Fω], coeff_map, hFm_coeff, map_zero]
      rw [hFmω, zero_mul]
    · -- Show ((C a + C b * X) ^ k).coeff (p - 1) = 0 for k ≠ p - 1, k ≤ 3*m
      rw [add_pow, finsetSum_coeff]
      have hzero_inner : ∀ j ∈ range (k + 1),
          ((C a) ^ j * (C b * X) ^ (k - j) * (k.choose j : (ZOmega (ZMod p))[X])).coeff (p - 1) = 0 := by
        intro j hj
        rw [Finset.mem_range] at hj
        rw [mul_pow, ← C_pow, ← C_pow, ← C_eq_natCast]
        have hre : C (a ^ j) * (C (b ^ (k - j)) * X ^ (k - j)) * C (k.choose j : ZOmega (ZMod p)) =
            C (a ^ j * b ^ (k - j) * (k.choose j : ZOmega (ZMod p))) * X ^ (k - j) := by
          simp only [map_mul]; ring
        rw [hre, coeff_C_mul_X_pow]
        split_ifs with hkj
        · have hle : p - 1 ≤ k := by omega
          have hgt : p - 1 < k := by omega
          have hch_symm : k.choose j = k.choose (p - 1) := by
            rw [hkj]
            exact (Nat.choose_symm (by omega : j ≤ k)).symm
          rw [hch_symm]
          have hlucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := k) (k := p - 1)
          have hkp_eq : k = p + (k - p) := by omega
          have hmod_lt : k % p < p - 1 := by
            rw [hkp_eq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]; omega
          rw [Nat.mod_eq_of_lt (show p - 1 < p by omega),
            Nat.choose_eq_zero_of_lt hmod_lt, zero_mul] at hlucas
          have hdvd : p ∣ k.choose (p - 1) := Nat.dvd_of_mod_eq_zero hlucas
          have hcast0 : ((k.choose (p - 1) : ℕ) : ZOmega (ZMod p)) = 0 := by
            have : ((k.choose (p - 1) : ℕ) : ZMod p) = 0 :=
              (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
            apply ZOmega.ext <;> simp [this]
          rw [hcast0, mul_zero]
        · rfl
      rw [Finset.sum_eq_zero hzero_inner, mul_zero]
  -- RHS coeff (p - 1) = b^(3m) * (-1)^m * aeval x0 (shiftedLegendre m)
  have hrhs_val : ((X * (X - 1) * (X - C x0)) ^ m).coeff (p - 1) =
      (-1 : ZOmega (ZMod p)) ^ m * aeval x0 (shiftedLegendre m) := by
    have hsplit : (X * (X - 1) * (X - C x0)) ^ m =
        X ^ m * ((X - 1) ^ m * (X - C x0) ^ m) := by
      rw [mul_pow, mul_pow, mul_assoc]
    rw [hsplit, ← h2m, show 2 * m = m + m by omega, coeff_X_pow_mul, coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hterm1 : ∀ k ∈ range (m + 1),
        ((X - 1 : (ZOmega (ZMod p))[X]) ^ m).coeff k = (m.choose k : ZOmega (ZMod p)) * (-1 : ZOmega (ZMod p)) ^ (m - k) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [sub_eq_add_neg, add_pow, finsetSum_coeff]
      have h0 : ∀ j ∈ range (m + 1),
          (X ^ j * (-1 : (ZOmega (ZMod p))[X]) ^ (m - j) * (m.choose j : (ZOmega (ZMod p))[X])).coeff k =
          if j = k then (m.choose k : ZOmega (ZMod p)) * (-1 : ZOmega (ZMod p)) ^ (m - k) else 0 := by
        intro j _
        have hre : X ^ j * (-1 : (ZOmega (ZMod p))[X]) ^ (m - j) * (m.choose j : (ZOmega (ZMod p))[X]) =
            C ((m.choose j : ZOmega (ZMod p)) * (-1 : ZOmega (ZMod p)) ^ (m - j)) * X ^ j := by
          simp only [map_mul, map_pow, map_neg, map_one, map_natCast]; ring
        rw [hre, coeff_C_mul_X_pow]
        by_cases hjk : j = k
        · subst hjk; simp
        · simp [hjk, Ne.symm hjk]
      rw [Finset.sum_congr rfl h0, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hk)]
    have hterm2 : ∀ k ∈ range (m + 1),
        ((X - C x0) ^ m).coeff (m - k) = (m.choose k : ZOmega (ZMod p)) * (-x0) ^ k := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [sub_eq_add_neg, add_pow, finsetSum_coeff]
      have h0 : ∀ j ∈ range (m + 1),
          (X ^ j * (-C x0) ^ (m - j) * (m.choose j : (ZOmega (ZMod p))[X])).coeff (m - k) =
          if j = m - k then (m.choose (m - k) : ZOmega (ZMod p)) * (-x0) ^ (m - (m - k)) else 0 := by
        intro j _
        have hre : X ^ j * (-C x0) ^ (m - j) * (m.choose j : (ZOmega (ZMod p))[X]) =
            C ((m.choose j : ZOmega (ZMod p)) * (-x0) ^ (m - j)) * X ^ j := by
          simp only [map_mul, map_pow, map_neg, map_natCast]; ring
        rw [hre, coeff_C_mul_X_pow]
        by_cases hjk : j = m - k
        · subst hjk; simp
        · simp [hjk, Ne.symm hjk]
      rw [Finset.sum_congr rfl h0, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
      rw [Nat.choose_symm (by omega), Nat.sub_sub_self (by omega)]
    rw [Finset.sum_congr rfl (fun k hk => by rw [hterm1 k hk, hterm2 k hk])]
    -- Expand aeval x0 (shiftedLegendre m)
    rw [shiftedLegendre, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hle : k ≤ m := by omega
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast, aeval_X]
    have hch_p : (((-1 : ℤ) ^ k * ((m + k).choose m : ℤ) : ℤ) : ZMod p) =
        ((m.choose k : ℕ) : ZMod p) := by
      simpa [m] using shiftedLegendre_coeff_mod_p hp2 k hle
    have hch_R : (-1 : ZOmega (ZMod p)) ^ k * ((m + k).choose m : ZOmega (ZMod p)) =
        (m.choose k : ZOmega (ZMod p)) := by
      have hL : (-1 : ZOmega (ZMod p)) ^ k * ((m + k).choose m : ZOmega (ZMod p)) =
          ZOmega.of (((-1 : ℤ) ^ k * ((m + k).choose m : ℤ) : ℤ) : ZMod p) := by
        simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast,
          map_mul, map_pow, map_neg, map_one, map_natCast]
      rw [hL, hch_p]
      simp only [map_natCast]
    have hsign : (-1 : ZOmega (ZMod p)) ^ (m - k) * (-x0) ^ k = (-1 : ZOmega (ZMod p)) ^ m * x0 ^ k := by
      rw [show -x0 = (-1 : ZOmega (ZMod p)) * x0 by ring, mul_pow, ← mul_assoc, ← pow_add,
        Nat.sub_add_cancel hle]
    calc (m.choose k : ZOmega (ZMod p)) * (-1 : ZOmega (ZMod p)) ^ (m - k) * ((m.choose k : ZOmega (ZMod p)) * (-x0) ^ k)
        = (-1 : ZOmega (ZMod p)) ^ m * ((m.choose k : ZOmega (ZMod p)) * (m.choose k : ZOmega (ZMod p))) * x0 ^ k := by
          linear_combination (m.choose k : ZOmega (ZMod p)) ^ 2 * hsign
      _ = (-1 : ZOmega (ZMod p)) ^ m * (((-1 : ZOmega (ZMod p)) ^ k * (m.choose k : ZOmega (ZMod p)) * ((m + k).choose m : ZOmega (ZMod p))) * x0 ^ k) := by
          rw [← hch_R]; ring
  -- Combine LHS = 0 and RHS = b^(3m) * (-1)^m * aeval x0 (shiftedLegendre m)
  have hprod0 : b ^ (3 * m) * ((-1 : ZOmega (ZMod p)) ^ m * aeval x0 (shiftedLegendre m)) = 0 := by
    have := congr_arg (fun q => q.coeff (p - 1)) hpow_eq
    rw [hlhs_zero, coeff_C_mul, hrhs_val] at this
    exact this.symm
  -- Cancel b^(3m) and (-1)^m (both are units since b^2 = -7 and p ≠ 7)
  have h7_ne : (7 : ZMod p) ≠ 0 := by
    intro h7
    have hd : p ∣ 7 := (ZMod.natCast_eq_zero_iff 7 p).mp (by simpa using h7)
    have hp_eq := (Nat.prime_dvd_prime_iff_eq hp.1 (by decide)).mp hd
    exact hp7 hp_eq
  have hb_unit : IsUnit b := by
    refine IsUnit.of_mul_eq_one (b * ZOmega.of ((-7 : ZMod p)⁻¹)) ?_
    rw [← mul_assoc, ← pow_two, ZOmega.two_omega_sub_one_sq]
    apply ZOmega.ext
    · simp [mul_inv_cancel₀ h7_ne]
    · simp
  have hsign_unit : IsUnit ((-1 : ZOmega (ZMod p)) ^ m) := (isUnit_one.neg).pow m
  exact (hsign_unit.mul_right_eq_zero.mp ((hb_unit.pow (3 * m)).mul_right_eq_zero.mp hprod0))

/- ### Section 4: Clausen's polynomial identity for `(shiftedLegendre n)^2` in `ℤ[X]` -/

private lemma shiftedLegendre_ode (n : ℕ) :
    (X ^ 2 - X) * derivative (derivative (shiftedLegendre n))
      + (2 * X - 1) * derivative (shiftedLegendre n)
      - C ((n * (n + 1) : ℕ) : ℤ) * shiftedLegendre n = 0 := by
  ext k
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_zero]
  have h1 : ((X ^ 2 - X : ℤ[X]) * derivative (derivative (shiftedLegendre n))).coeff k =
      (if 2 ≤ k then ((k - 1 : ℕ) : ℤ) * k * (shiftedLegendre n).coeff k else 0) -
      (if 1 ≤ k then (k : ℤ) * (k + 1) * (shiftedLegendre n).coeff (k + 1) else 0) := by
    rw [sub_mul, coeff_sub, coeff_X_pow_mul',
      show (X : ℤ[X]) * derivative (derivative (shiftedLegendre n)) =
        X ^ 1 * derivative (derivative (shiftedLegendre n)) by simp,
      coeff_X_pow_mul']
    congr 1
    · split_ifs with hk
      · rw [coeff_derivative, coeff_derivative]
        have h1 : k - 2 + 1 = k - 1 := by omega
        have h2 : k - 2 + 1 + 1 = k := by omega
        rw [h2, h1]
        push_cast [Nat.cast_sub (by omega : 2 ≤ k), Nat.cast_sub (by omega : 1 ≤ k)]
        ring
      · rfl
    · split_ifs with hk
      · rw [coeff_derivative, coeff_derivative]
        have h1 : k - 1 + 1 = k := by omega
        have h2 : k - 1 + 1 + 1 = k + 1 := by omega
        rw [h2, h1]
        push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
        ring
      · rfl
  have h2 : ((2 * X - 1 : ℤ[X]) * derivative (shiftedLegendre n)).coeff k =
      (if 1 ≤ k then 2 * (k : ℤ) * (shiftedLegendre n).coeff k else 0) -
      ((k : ℤ) + 1) * (shiftedLegendre n).coeff (k + 1) := by
    rw [sub_mul, one_mul, coeff_sub, mul_assoc, coeff_ofNat_mul,
      show (X : ℤ[X]) * derivative (shiftedLegendre n) =
        X ^ 1 * derivative (shiftedLegendre n) by simp,
      coeff_X_pow_mul']
    congr 1
    · split_ifs with hk
      · rw [coeff_derivative]
        have h1 : k - 1 + 1 = k := by omega
        rw [h1]
        push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
        ring
      · simp
    · rw [coeff_derivative]; ring
  rw [h1, h2]
  have hsimpl : ((if 2 ≤ k then ((k - 1 : ℕ) : ℤ) * k * (shiftedLegendre n).coeff k else 0) -
        (if 1 ≤ k then (k : ℤ) * (k + 1) * (shiftedLegendre n).coeff (k + 1) else 0)) +
      ((if 1 ≤ k then 2 * (k : ℤ) * (shiftedLegendre n).coeff k else 0) -
        ((k : ℤ) + 1) * (shiftedLegendre n).coeff (k + 1)) -
      ((n * (n + 1) : ℕ) : ℤ) * (shiftedLegendre n).coeff k =
      ((k : ℤ) * (k + 1) - (n : ℤ) * (n + 1)) * (shiftedLegendre n).coeff k -
      ((k : ℤ) + 1) ^ 2 * (shiftedLegendre n).coeff (k + 1) := by
    rcases k with _ | _ | k <;> push_cast <;> ring
  rw [hsimpl, coeff_shiftedLegendre, coeff_shiftedLegendre]
  by_cases hkn : k < n
  · have hnat1 : (k + 1) * n.choose (k + 1) = (n - k) * n.choose k := by
      have hsub := Nat.choose_succ_right_eq n k
      linarith
    have hnat2 : (k + 1) * (n + (k + 1)).choose n = (n + k + 1) * (n + k).choose n := by
      have hc1 : (n + (k + 1)).choose n = (n + k + 1).choose (k + 1) := by
        rw [show n + (k + 1) = n + k + 1 by omega]
        exact Nat.choose_symm_of_eq_add (by omega : n + k + 1 = n + (k + 1))
      have hc2 : (n + k).choose n = (n + k).choose k :=
        Nat.choose_symm_of_eq_add (by omega : n + k = n + k)
      rw [hc1, hc2]
      linarith [Nat.add_one_mul_choose_eq (n + k) k]
    have hz1 : ((k : ℤ) + 1) * (n.choose (k + 1) : ℤ) = ((n : ℤ) - k) * (n.choose k : ℤ) := by
      have := congr_arg (Nat.cast (R := ℤ)) hnat1
      push_cast [Nat.cast_sub (le_of_lt hkn)] at this
      exact this
    have hz2 : ((k : ℤ) + 1) * ((n + (k + 1)).choose n : ℤ) =
        ((n : ℤ) + k + 1) * ((n + k).choose n : ℤ) := by
      have := congr_arg (Nat.cast (R := ℤ)) hnat2
      push_cast at this
      exact this
    have hmul := congr_arg₂ (· * ·) hz1 hz2
    rw [pow_succ]
    linear_combination (-1 : ℤ) ^ k * hmul
  · by_cases hkeq : k = n
    · subst hkeq
      rw [Nat.choose_eq_zero_of_lt (show k < k + 1 by omega)]
      simp
    · rw [Nat.choose_eq_zero_of_lt (show n < k by omega),
        Nat.choose_eq_zero_of_lt (show n < k + 1 by omega)]
      simp

private lemma symm_poly_eq_comp_z :
    ∀ (d : ℕ) (H : ℤ[X]), H.natDegree ≤ d → H.comp (1 - X) = H →
      ∃ G : ℤ[X], H = G.comp (X ^ 2 - X) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro H hdeg hsymm
    by_cases hH : H = C (H.eval 0)
    · refine ⟨C (H.eval 0), ?_⟩
      rw [C_comp]; exact hH
    · set H0 := H - C (H.eval 0)
      have hH0_0 : H0.eval 0 = 0 := by simp [H0]
      have hH0_1 : H0.eval 1 = 0 := by
        have h1 : H.eval 1 = H.eval 0 := by
          have := congr_arg (fun q => q.eval 0) hsymm
          simpa [eval_comp] using this
        simp [H0, h1]
      have hX : X ∣ H0 := by
        rw [X_dvd_iff, coeff_zero_eq_eval_zero]; exact hH0_0
      rcases hX with ⟨Q1, hQ1⟩
      have hQ1_1 : Q1.eval 1 = 0 := by
        have := congr_arg (fun q => q.eval 1) hQ1
        simpa [hH0_1] using this.symm
      have hX1 : X - 1 ∣ Q1 := by
        rw [show (X - 1 : ℤ[X]) = X - C 1 by simp, dvd_iff_isRoot, IsRoot.def]; exact hQ1_1
      rcases hX1 with ⟨Q, hQ⟩
      have hfac : H0 = (X ^ 2 - X) * Q := by
        rw [hQ1, hQ]; ring
      have hH0_ne : H0 ≠ 0 := sub_ne_zero.mpr hH
      have hQ_ne : Q ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hfac; exact hH0_ne hfac
      have hdeg_z : (X ^ 2 - X : ℤ[X]).natDegree = 2 := by
        compute_degree!
      have hlc_z : (X ^ 2 - X : ℤ[X]).leadingCoeff = 1 := by
        rw [leadingCoeff, hdeg_z]; simp [coeff_X]
      have hdeg_H0 : H0.natDegree = 2 + Q.natDegree := by
        rw [hfac, natDegree_mul (by intro h0; rw [h0] at hdeg_z; simp at hdeg_z) hQ_ne, hdeg_z]
      have hdeg_H0_le : H0.natDegree ≤ d := by
        refine le_trans (natDegree_sub_le _ _) (max_le hdeg ?_)
        simp
      have hQ_deg : Q.natDegree < d := by omega
      have hQ_symm : Q.comp (1 - X) = Q := by
        have h1 : H0.comp (1 - X) = H0 := by
          simp only [H0, sub_comp, C_comp, hsymm]
        have hz_symm : (X ^ 2 - X : ℤ[X]).comp (1 - X) = X ^ 2 - X := by
          simp only [sub_comp, pow_comp, X_comp]; ring
        rw [hfac, mul_comp, hz_symm] at h1
        exact mul_left_cancel₀ (by intro h0; rw [h0] at hdeg_z; simp at hdeg_z) h1
      rcases ih Q.natDegree hQ_deg Q le_rfl hQ_symm with ⟨G0, hG0⟩
      refine ⟨C (H.eval 0) + X * G0, ?_⟩
      simp only [add_comp, C_comp, mul_comp, X_comp, ← hG0, ← hfac, H0]
      ring

private lemma comp_z_eq_zero_iff (P : ℤ[X]) : P.comp (X ^ 2 - X) = 0 ↔ P = 0 := by
  constructor
  · intro h
    by_contra hne
    have hdeg_z : (X ^ 2 - X : ℤ[X]).natDegree = 2 := by compute_degree!
    have hdeg : (P.comp (X ^ 2 - X)).natDegree = P.natDegree * 2 := by
      rw [natDegree_comp, hdeg_z]
    have hlc_z : (X ^ 2 - X : ℤ[X]).leadingCoeff = 1 := by
      rw [leadingCoeff, hdeg_z]; simp [coeff_X]
    have hne' : P.comp (X ^ 2 - X) ≠ 0 := by
      intro h0
      have hlc : (P.comp (X ^ 2 - X)).leadingCoeff = P.leadingCoeff * 1 ^ P.natDegree := by
        rw [← hlc_z]
        exact leadingCoeff_comp (by rw [hdeg_z]; omega)
      rw [h0, leadingCoeff_zero, one_pow, mul_one] at hlc
      exact hne (leadingCoeff_eq_zero.mp hlc.symm)
    exact hne' h
  · intro h; simp [h]

private lemma clausen_poly_identity (n : ℕ) :
    (shiftedLegendre n) ^ 2 =
      (∑ k ∈ range (n + 1), C (((n + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2) * X ^ k).comp
        (X ^ 2 - X) := by
  set y : ℤ[X] := shiftedLegendre n
  set w : ℤ[X] := y ^ 2
  have hsymm : w.comp (1 - X) = w := by
    have h1 := neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq n
    have h2 : (y.comp (1 - X)) ^ 2 = ((-1 : ℤ[X]) ^ n * y.comp (1 - X)) ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
      have : ((-1 : ℤ[X]) ^ 2) = 1 := by ring
      rw [this, one_pow, one_mul]
    rw [h1] at h2
    simpa [w, pow_comp] using h2
  rcases symm_poly_eq_comp_z w.natDegree w le_rfl hsymm with ⟨G, hG⟩
  set z : ℤ[X] := X ^ 2 - X
  set dz : ℤ[X] := 2 * X - 1
  set c : ℤ[X] := C ((n * (n + 1) : ℕ) : ℤ)
  -- Step 1: Derive 3rd-order ODE for w = y^2 from y's ODE
  have hode_y : z * derivative (derivative y) + dz * derivative y = c * y := by
    linear_combination shiftedLegendre_ode n
  have hdz_eq : derivative z = dz := by
    simp only [z, dz, derivative_sub, derivative_X_pow, derivative_X, Nat.cast_ofNat, map_ofNat]
    ring
  have hddz_eq : derivative dz = 2 := by
    simp only [dz, derivative_sub, derivative_mul, derivative_X, derivative_ofNat, derivative_one]
    ring
  have hdz2 : dz ^ 2 = 1 + 4 * z := by simp only [dz, z]; ring
  have hw1 : derivative w = 2 * y * derivative y := by
    simp only [w, derivative_pow, Nat.cast_ofNat, map_ofNat]; ring
  have hw2 : derivative (derivative w) = 2 * (derivative y) ^ 2 + 2 * y * derivative (derivative y) := by
    rw [hw1, derivative_mul, derivative_mul, derivative_ofNat]; ring
  have haux : z * derivative (derivative w) + dz * derivative w - 2 * c * w =
      2 * z * (derivative y) ^ 2 := by
    rw [hw2, hw1]
    have : z * (2 * derivative y ^ 2 + 2 * y * derivative (derivative y)) + dz * (2 * y * derivative y)
        - 2 * c * y ^ 2 =
        2 * y * (z * derivative (derivative y) + dz * derivative y - c * y) +
        2 * z * derivative y ^ 2 := by ring
    rw [show w = y ^ 2 from rfl, this, hode_y]; ring
  have haux_d := congr_arg derivative haux
  have hode_w : z ^ 2 * derivative (derivative (derivative w)) +
      3 * z * dz * derivative (derivative w) +
      (dz ^ 2 + 2 * z - 4 * c * z) * derivative w - 2 * c * dz * w = 0 := by
    simp only [derivative_sub, derivative_add, derivative_mul, derivative_pow, derivative_ofNat,
      Nat.cast_ofNat, map_ofNat, hdz_eq, hddz_eq, show derivative c = 0 by simp [c]] at haux_d
    have hmul : z * (dz * derivative (derivative w) + z * derivative (derivative (derivative w)) +
        (2 * derivative w + dz * derivative (derivative w)) - 2 * c * derivative w) =
        z * (2 * dz * derivative y ^ 2 + 2 * z * (2 * derivative y * derivative (derivative y))) := by
      have := congr_arg (fun q => z * q) haux_d
      convert this using 1 <;> ring
    have hsub1 : z * (2 * z * (2 * derivative y * derivative (derivative y))) =
        4 * z * derivative y * (c * y - dz * derivative y) := by
      have : z * derivative (derivative y) = c * y - dz * derivative y := by
        linear_combination hode_y
      calc z * (2 * z * (2 * derivative y * derivative (derivative y)))
          = 4 * z * derivative y * (z * derivative (derivative y)) := by ring
        _ = 4 * z * derivative y * (c * y - dz * derivative y) := by rw [this]
    have hsub2 : 2 * z * derivative y ^ 2 =
        z * derivative (derivative w) + dz * derivative w - 2 * c * w := haux.symm
    linear_combination hmul + hsub1 - dz * hsub2 - 2 * c * z * hw1
  -- Step 2: Substitute w = G.comp z to get 3rd-order ODE for G
  have hGw1 : derivative w = dz * (derivative G).comp z := by
    rw [hG, derivative_comp, hdz_eq, mul_comm]
  have hGw2 : derivative (derivative w) =
      dz ^ 2 * (derivative (derivative G)).comp z + 2 * (derivative G).comp z := by
    rw [hGw1, derivative_mul, hddz_eq, derivative_comp, hdz_eq]; ring
  have hGw3 : derivative (derivative (derivative w)) =
      dz ^ 3 * (derivative (derivative (derivative G))).comp z +
      6 * dz * (derivative (derivative G)).comp z := by
    rw [hGw2, derivative_add, derivative_mul, derivative_mul, derivative_pow, hddz_eq,
      derivative_comp, derivative_comp, hdz_eq, derivative_ofNat, Nat.cast_ofNat, map_ofNat]; ring
  set Gode : ℤ[X] :=
    X ^ 2 * (1 + 4 * X) * derivative (derivative (derivative G)) +
    3 * X * (1 + 6 * X) * derivative (derivative G) +
    (1 + 12 * X - 4 * c * X) * derivative G - 2 * c * G
  have hGode_comp : dz * Gode.comp z = 0 := by
    have hcomp_eq : Gode.comp z =
        z ^ 2 * (1 + 4 * z) * (derivative (derivative (derivative G))).comp z +
        3 * z * (1 + 6 * z) * (derivative (derivative G)).comp z +
        (1 + 12 * z - 4 * c * z) * (derivative G).comp z - 2 * c * G.comp z := by
      simp only [Gode, c, sub_comp, add_comp, mul_comp, pow_comp, one_comp, ofNat_comp, C_comp,
        X_comp, Nat.cast_ofNat]
    rw [hcomp_eq]
    rw [hGw3, hGw2, hGw1, hG] at hode_w
    linear_combination hode_w -
      (z ^ 2 * dz * (derivative (derivative (derivative G))).comp z +
        3 * z * dz * (derivative (derivative G)).comp z +
        dz * (derivative G).comp z) * hdz2
  have hdz_ne : dz ≠ 0 := by
    intro h0
    have := congr_arg (fun q => q.eval 0) h0
    simp [dz] at this
  have hGode : Gode = 0 := (comp_z_eq_zero_iff Gode).mp ((mul_eq_zero.mp hGode_comp).resolve_left hdz_ne)
  -- Step 3: Extract coefficient recurrence for G
  have hGrec : ∀ k : ℕ, ((k : ℤ) + 1) ^ 3 * G.coeff (k + 1) =
      2 * (2 * (k : ℤ) + 1) * ((n : ℤ) - k) * ((n : ℤ) + k + 1) * G.coeff k := by
    intro k
    have hk0 := congr_arg (fun q => q.coeff k) hGode
    simp only [coeff_zero] at hk0
    have ht1 : (X ^ 2 * (1 + 4 * X) * derivative (derivative (derivative G))).coeff k =
        (if 2 ≤ k then ((k - 1 : ℕ) : ℤ) * k * (k + 1) * G.coeff (k + 1) else 0) +
        (if 3 ≤ k then 4 * ((k - 2 : ℕ) : ℤ) * (k - 1 : ℕ) * k * G.coeff k else 0) := by
      have : X ^ 2 * (1 + 4 * X) * derivative (derivative (derivative G)) =
          X ^ 2 * derivative (derivative (derivative G)) +
          4 * (X ^ 3 * derivative (derivative (derivative G))) := by ring
      rw [this, coeff_add, coeff_ofNat_mul, coeff_X_pow_mul', coeff_X_pow_mul']
      congr 1
      · split_ifs with hk
        · rw [coeff_derivative, coeff_derivative, coeff_derivative]
          have e1 : k - 2 + 1 = k - 1 := by omega
          have e2 : k - 2 + 1 + 1 = k := by omega
          have e3 : k - 2 + 1 + 1 + 1 = k + 1 := by omega
          rw [e3, e2, e1]
          push_cast [Nat.cast_sub (by omega : 2 ≤ k), Nat.cast_sub (by omega : 1 ≤ k)]
          ring
        · rfl
      · split_ifs with hk
        · rw [coeff_derivative, coeff_derivative, coeff_derivative]
          have e1 : k - 3 + 1 = k - 2 := by omega
          have e2 : k - 3 + 1 + 1 = k - 1 := by omega
          have e3 : k - 3 + 1 + 1 + 1 = k := by omega
          rw [e3, e2, e1]
          push_cast [Nat.cast_sub (by omega : 3 ≤ k), Nat.cast_sub (by omega : 2 ≤ k),
            Nat.cast_sub (by omega : 1 ≤ k)]
          ring
        · simp
    have ht2 : (3 * X * (1 + 6 * X) * derivative (derivative G)).coeff k =
        (if 1 ≤ k then 3 * (k : ℤ) * (k + 1) * G.coeff (k + 1) else 0) +
        (if 2 ≤ k then 18 * ((k - 1 : ℕ) : ℤ) * k * G.coeff k else 0) := by
      have : 3 * X * (1 + 6 * X) * derivative (derivative G) =
          3 * (X ^ 1 * derivative (derivative G)) +
          18 * (X ^ 2 * derivative (derivative G)) := by ring
      rw [this, coeff_add, coeff_ofNat_mul, coeff_ofNat_mul, coeff_X_pow_mul', coeff_X_pow_mul']
      congr 1
      · split_ifs with hk
        · rw [coeff_derivative, coeff_derivative]
          have e1 : k - 1 + 1 = k := by omega
          have e2 : k - 1 + 1 + 1 = k + 1 := by omega
          rw [e2, e1]
          push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
          ring
        · simp
      · split_ifs with hk
        · rw [coeff_derivative, coeff_derivative]
          have e1 : k - 2 + 1 = k - 1 := by omega
          have e2 : k - 2 + 1 + 1 = k := by omega
          rw [e2, e1]
          push_cast [Nat.cast_sub (by omega : 2 ≤ k), Nat.cast_sub (by omega : 1 ≤ k)]
          ring
        · simp
    have ht3 : ((1 + 12 * X - 4 * c * X) * derivative G).coeff k =
        ((k : ℤ) + 1) * G.coeff (k + 1) +
        (if 1 ≤ k then (12 - 4 * ((n * (n + 1) : ℕ) : ℤ)) * k * G.coeff k else 0) := by
      have : (1 + 12 * X - 4 * c * X) * derivative G =
          derivative G + C (12 - 4 * ((n * (n + 1) : ℕ) : ℤ)) * (X ^ 1 * derivative G) := by
        simp only [c, map_sub, map_mul, map_ofNat]; ring
      rw [this, coeff_add, coeff_derivative, coeff_C_mul, coeff_X_pow_mul']
      congr 1
      · ring
      · split_ifs with hk
        · rw [coeff_derivative]
          have e1 : k - 1 + 1 = k := by omega
          rw [e1]
          push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
          ring
        · simp
    have ht4 : (2 * c * G).coeff k = 2 * ((n * (n + 1) : ℕ) : ℤ) * G.coeff k := by
      have : 2 * c * G = C (2 * ((n * (n + 1) : ℕ) : ℤ)) * G := by
        simp only [c, map_mul, map_ofNat]
      rw [this, coeff_C_mul]
    simp only [Gode, coeff_sub, coeff_add] at hk0
    rw [ht1, ht2, ht3, ht4] at hk0
    rcases k with _ | _ | _ | k <;> push_cast at hk0 ⊢ <;> linear_combination hk0
  -- Step 4: Match coefficients of G against F(z) by induction on k
  set F : ℤ[X] :=
    ∑ k ∈ range (n + 1), C (((n + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2) * X ^ k
  have hF_coeff : ∀ k : ℕ, F.coeff k = ((n + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 := by
    intro k
    simp only [F, finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with hk
    · rfl
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have hGF : G = F := by
    ext k
    rw [hF_coeff]
    induction k with
    | zero =>
      have heval := congr_arg (fun q => q.eval 0) hG
      have hz0 : z.eval 0 = 0 := by simp [z]
      rw [eval_comp, hz0, show w = y ^ 2 from rfl, eval_pow, ← coeff_zero_eq_eval_zero,
        ← coeff_zero_eq_eval_zero, coeff_shiftedLegendre] at heval
      simpa using heval.symm
    | succ k ih =>
      have hk1_ne : ((k : ℤ) + 1) ^ 3 ≠ 0 := by positivity
      apply mul_left_cancel₀ hk1_ne
      rw [hGrec k, ih]
      by_cases hkn : k < n
      · have hch1 : (2 * k + 2) * (2 * k + 1) * (n + k + 1).choose (2 * k + 2) =
            (n + k + 1) * (n - k) * (n + k).choose (2 * k) := by
          have e1 := Nat.add_one_mul_choose_eq (n + k) (2 * k + 1)
          have e2 := Nat.choose_succ_right_eq (n + k) (2 * k)
          have hsub : n + k - 2 * k = n - k := by omega
          rw [hsub] at e2
          nlinarith
        have hch2 : (k + 1) * (2 * k + 2).choose (k + 1) = 2 * (2 * k + 1) * (2 * k).choose k := by
          have e1 := Nat.add_one_mul_choose_eq (2 * k + 1) k
          have e2 := Nat.choose_succ_right_eq (2 * k + 1) k
          have e3 := Nat.add_one_mul_choose_eq (2 * k) k
          have hsub : 2 * k + 1 - k = k + 1 := by omega
          rw [hsub] at e2
          have e4 : (2 * k + 1).choose k = (2 * k + 1).choose (k + 1) :=
            Nat.choose_symm_of_eq_add (by omega : 2 * k + 1 = k + (k + 1))
          nlinarith
        have hz1 : ((2 * (k : ℤ) + 2) * (2 * k + 1)) * ((n + (k + 1)).choose (2 * (k + 1)) : ℤ) =
            ((n : ℤ) + k + 1) * ((n : ℤ) - k) * ((n + k).choose (2 * k) : ℤ) := by
          have := congr_arg (Nat.cast (R := ℤ)) hch1
          rw [show n + (k + 1) = n + k + 1 by omega, show 2 * (k + 1) = 2 * k + 2 by omega]
          push_cast [Nat.cast_sub (le_of_lt hkn)] at this ⊢
          linear_combination this
        have hz2 : ((k : ℤ) + 1) * ((2 * (k + 1)).choose (k + 1) : ℤ) =
            2 * (2 * (k : ℤ) + 1) * ((2 * k).choose k : ℤ) := by
          have := congr_arg (Nat.cast (R := ℤ)) hch2
          rw [show 2 * (k + 1) = 2 * k + 2 by omega]
          push_cast at this ⊢
          exact this
        have h2k1_ne : (2 * (k : ℤ) + 1) ≠ 0 := by positivity
        apply mul_left_cancel₀ h2k1_ne
        have hsq2 : ((k : ℤ) + 1) ^ 2 * ((2 * (k + 1)).choose (k + 1) : ℤ) ^ 2 =
            4 * (2 * (k : ℤ) + 1) ^ 2 * ((2 * k).choose k : ℤ) ^ 2 := by
          linear_combination (((k : ℤ) + 1) * ((2 * (k + 1)).choose (k + 1) : ℤ) +
            2 * (2 * (k : ℤ) + 1) * ((2 * k).choose k : ℤ)) * hz2
        calc (2 * (k : ℤ) + 1) * (2 * (2 * (k : ℤ) + 1) * ((n : ℤ) - k) * ((n : ℤ) + k + 1) *
                (((n + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2))
            = 2 * (2 * (k : ℤ) + 1) ^ 2 * ((2 * k).choose k : ℤ) ^ 2 *
                (((n : ℤ) + k + 1) * ((n : ℤ) - k) * ((n + k).choose (2 * k) : ℤ)) := by ring
          _ = 2 * (2 * (k : ℤ) + 1) ^ 2 * ((2 * k).choose k : ℤ) ^ 2 *
                (((2 * (k : ℤ) + 2) * (2 * k + 1)) * ((n + (k + 1)).choose (2 * (k + 1)) : ℤ)) := by
              rw [← hz1]
          _ = (2 * (k : ℤ) + 1) * ((k : ℤ) + 1) * ((n + (k + 1)).choose (2 * (k + 1)) : ℤ) *
                (4 * (2 * (k : ℤ) + 1) ^ 2 * ((2 * k).choose k : ℤ) ^ 2) := by ring
          _ = (2 * (k : ℤ) + 1) * ((k : ℤ) + 1) * ((n + (k + 1)).choose (2 * (k + 1)) : ℤ) *
                (((k : ℤ) + 1) ^ 2 * ((2 * (k + 1)).choose (k + 1) : ℤ) ^ 2) := by rw [← hsq2]
          _ = (2 * (k : ℤ) + 1) * (((k : ℤ) + 1) ^ 3 *
                (((n + (k + 1)).choose (2 * (k + 1)) : ℤ) * ((2 * (k + 1)).choose (k + 1) : ℤ) ^ 2)) := by ring
      · by_cases hkeq : k = n
        · subst hkeq
          rw [Nat.choose_eq_zero_of_lt (show k + (k + 1) < 2 * (k + 1) by omega)]
          simp
        · rw [Nat.choose_eq_zero_of_lt (show n + k < 2 * k by omega),
            Nat.choose_eq_zero_of_lt (show n + (k + 1) < 2 * (k + 1) by omega)]
          simp
  rw [hG, hGF]

/- ### Section 5: Binomial supercongruences and `S_0`, `S_h` -/

private lemma clausen_term_prod_identity (n : ℕ) :
    ∀ k : ℕ, k ≤ n →
      (∏ j ∈ range k, ((2 * j + 1 : ℤ) ^ 2)) *
        (((n + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k) =
      (((2 * k).choose k : ℤ) ^ 3) *
        (∏ j ∈ range k, ((2 * j + 1 : ℤ) ^ 2 - (2 * (n : ℤ) + 1) ^ 2))
  | 0, _ => by simp
  | k + 1, hk => by
    have ih := clausen_term_prod_identity n k (by omega)
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have hch1 : (2 * k + 2) * (2 * k + 1) * (n + k + 1).choose (2 * k + 2) =
        (n + k + 1) * (n - k) * (n + k).choose (2 * k) := by
      have e1 := Nat.add_one_mul_choose_eq (n + k) (2 * k + 1)
      have e2 := Nat.choose_succ_right_eq (n + k) (2 * k)
      have hsub : n + k - 2 * k = n - k := by omega
      rw [hsub] at e2
      nlinarith
    have hch2 : (k + 1) * (2 * k + 2).choose (k + 1) = 2 * (2 * k + 1) * (2 * k).choose k := by
      have e1 := Nat.add_one_mul_choose_eq (2 * k + 1) k
      have e2 := Nat.choose_succ_right_eq (2 * k + 1) k
      have e3 := Nat.add_one_mul_choose_eq (2 * k) k
      have hsub : 2 * k + 1 - k = k + 1 := by omega
      rw [hsub] at e2
      have e4 : (2 * k + 1).choose k = (2 * k + 1).choose (k + 1) :=
        Nat.choose_symm_of_eq_add (by omega : 2 * k + 1 = k + (k + 1))
      nlinarith
    have hz1 : ((2 * (k : ℤ) + 2) * (2 * k + 1)) * ((n + (k + 1)).choose (2 * (k + 1)) : ℤ) =
        ((n : ℤ) + k + 1) * ((n : ℤ) - k) * ((n + k).choose (2 * k) : ℤ) := by
      have := congr_arg (Nat.cast (R := ℤ)) hch1
      rw [show n + (k + 1) = n + k + 1 by omega, show 2 * (k + 1) = 2 * k + 2 by omega]
      push_cast [Nat.cast_sub (by omega : k ≤ n)] at this ⊢
      linear_combination this
    have hz2 : ((k : ℤ) + 1) * ((2 * (k + 1)).choose (k + 1) : ℤ) =
        2 * (2 * (k : ℤ) + 1) * ((2 * k).choose k : ℤ) := by
      have := congr_arg (Nat.cast (R := ℤ)) hch2
      rw [show 2 * (k + 1) = 2 * k + 2 by omega]
      push_cast at this ⊢
      exact this
    have hne : ((k : ℤ) + 1) ^ 3 ≠ 0 := by positivity
    apply mul_left_cancel₀ hne
    have hpow : (-16 : ℤ) ^ (k + 1) = (-16 : ℤ) ^ k * (-16) := pow_succ _ _
    rw [hpow]
    have hdiff : (2 * (k : ℤ) + 1) ^ 2 - (2 * (n : ℤ) + 1) ^ 2 =
        -4 * ((n : ℤ) - k) * ((n : ℤ) + k + 1) := by ring
    rw [hdiff]
    have h2 : ((k : ℤ) + 1) ^ 2 * ((2 * (k + 1)).choose (k + 1) : ℤ) ^ 2 =
        4 * (2 * (k : ℤ) + 1) ^ 2 * ((2 * k).choose k : ℤ) ^ 2 := by
      linear_combination (((k : ℤ) + 1) * ((2 * (k + 1)).choose (k + 1) : ℤ) +
        2 * (2 * (k : ℤ) + 1) * ((2 * k).choose k : ℤ)) * hz2
    have h3 : ((k : ℤ) + 1) ^ 3 * ((2 * (k + 1)).choose (k + 1) : ℤ) ^ 3 =
        8 * (2 * (k : ℤ) + 1) ^ 3 * ((2 * k).choose k : ℤ) ^ 3 := by
      linear_combination (((k : ℤ) + 1) ^ 2 * ((2 * (k + 1)).choose (k + 1) : ℤ) ^ 2 +
        ((k : ℤ) + 1) * ((2 * (k + 1)).choose (k + 1) : ℤ) * (2 * (2 * (k : ℤ) + 1) * ((2 * k).choose k : ℤ)) +
        (2 * (2 * (k : ℤ) + 1) * ((2 * k).choose k : ℤ)) ^ 2) * hz2
    set P1 := ∏ j ∈ range k, ((2 * (j : ℤ) + 1) ^ 2)
    set P2 := ∏ j ∈ range k, ((2 * (j : ℤ) + 1) ^ 2 - (2 * (n : ℤ) + 1) ^ 2)
    linear_combination
      P1 * (2 * (k : ℤ) + 1) ^ 2 * ((n + (k + 1)).choose (2 * (k + 1)) : ℤ) * (-16 : ℤ) ^ k * (-16) * ((k : ℤ) + 1) * h2
      - 32 * P1 * (2 * (k : ℤ) + 1) ^ 3 * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k * hz1
      - 32 * (2 * (k : ℤ) + 1) ^ 3 * ((n : ℤ) + k + 1) * ((n : ℤ) - k) * ih
      + 4 * ((n : ℤ) - k) * ((n : ℤ) + k + 1) * P2 * h3

private lemma eval_x0_sq_eq_zero_mod_p2 {p : ℕ} [Fact p.Prime] {f : ℤ[X]}
    (h0 : aeval (ZOmega.x0 : ZOmega (ZMod p)) f = 0) :
    aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) (f ^ 2) = 0 := by
  set v : ZOmega ℤ := aeval ZOmega.x0 f
  have hmap_aeval : ∀ (m : ℕ),
      ZOmega.mapRingHom (Int.castRingHom (ZMod m)) (aeval (ZOmega.x0 : ZOmega ℤ) f) =
        aeval (ZOmega.x0 : ZOmega (ZMod m)) f := by
    intro m
    rw [aeval_def, aeval_def, Polynomial.hom_eval₂, ZOmega.mapRingHom_x0]
    congr 1
    ext x
    apply ZOmega.ext <;> simp [ZOmega.mapRingHom]
  have hcast_p : ZOmega.mapRingHom (Int.castRingHom (ZMod p)) v = 0 := by
    rw [hmap_aeval p]; exact h0
  have hre_dvd : (p : ℤ) ∣ v.re :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd v.re p).mp (congr_arg ZOmega.re hcast_p)
  have him_dvd : (p : ℤ) ∣ v.im :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd v.im p).mp (congr_arg ZOmega.im hcast_p)
  rcases hre_dvd with ⟨a, ha⟩
  rcases him_dvd with ⟨b, hb⟩
  have hv2 : aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) (f ^ 2) =
      ZOmega.mapRingHom (Int.castRingHom (ZMod (p ^ 2))) (v ^ 2) := by
    rw [map_pow, map_pow, hmap_aeval (p ^ 2)]
  rw [hv2]
  apply ZOmega.ext
  · change (((v ^ 2).re : ℤ) : ZMod (p ^ 2)) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨a ^ 2 - 2 * b ^ 2, ?_⟩
    simp only [pow_two, ZOmega.mul_re, ha, hb]; push_cast; ring
  · change (((v ^ 2).im : ℤ) : ZMod (p ^ 2)) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨2 * a * b + b ^ 2, ?_⟩
    simp only [pow_two, ZOmega.mul_im, ha, hb]; push_cast; ring

private lemma dvd_a_half {p : ℕ} [Fact p.Prime] (hp : OeisA3625.A p) :
    p ^ 2 ∣ OeisA79727.a ((p - 1) / 2) := by
  set m := (p - 1) / 2
  have hp2 : p ≠ 2 := A3625_ne_two hp
  have h2m1 : 2 * m + 1 = p := by
    have := Nat.odd_iff.mp (A3625_odd hp)
    omega
  have hsq0 : aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) ((shiftedLegendre m) ^ 2) = 0 :=
    eval_x0_sq_eq_zero_mod_p2 (shiftedLegendre_eval_x0_eq_zero hp)
  rw [clausen_poly_identity m, aeval_comp] at hsq0
  have hz_val : aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) (X ^ 2 - X : ℤ[X]) = (-16 : ZOmega (ZMod (p ^ 2))) := by
    simp only [map_sub, map_pow, aeval_X, ZOmega.neg_x0_mul_one_sub]
  rw [hz_val, map_sum] at hsq0
  have hsum_re : (∑ k ∈ range (m + 1),
      (((m + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k : ZMod (p ^ 2))) = 0 := by
    have hre := congr_arg ZOmega.re hsq0
    simp only [ZOmega.zero_re] at hre
    rw [← hre]
    have hre_sum : ∀ s : Finset ℕ, ∀ f : ℕ → ZOmega (ZMod (p ^ 2)), (∑ k ∈ s, f k).re = ∑ k ∈ s, (f k).re := by
      intro s f
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => simp [Finset.sum_insert ha, ih]
    rw [hre_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_mul, aeval_C, map_pow, aeval_X]
    have hpow : ((-16 : ZOmega (ZMod (p ^ 2))) ^ k) = ZOmega.of ((-16 : ZMod (p ^ 2)) ^ k) := by
      rw [map_pow]; congr 1; apply ZOmega.ext <;> simp
    rw [hpow]
    have hcast : (algebraMap ℤ (ZOmega (ZMod (p ^ 2)))
        (((m + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2)) =
        ZOmega.of (((m + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 : ZMod (p ^ 2)) := by
      apply ZOmega.ext <;> simp [eq_intCast]
    rw [hcast, ← map_mul, ZOmega.of_re]
    push_cast; ring
  have hterm_eq : ∀ k ∈ range (m + 1),
      (((m + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k : ZMod (p ^ 2)) =
      (((2 * k).choose k : ℕ) ^ 3 : ZMod (p ^ 2)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hprod := congr_arg (Int.castRingHom (ZMod (p ^ 2))) (clausen_term_prod_identity m k (by omega))
    simp only [map_mul, map_prod, map_pow, map_sub, map_add, map_one, map_ofNat, map_natCast,
      eq_intCast, Int.cast_neg, Int.cast_ofNat] at hprod
    have hprod_eq : (∏ j ∈ range k, ((2 * (j : ZMod (p ^ 2)) + 1) ^ 2 - (2 * (m : ZMod (p ^ 2)) + 1) ^ 2)) =
        ∏ j ∈ range k, ((2 * (j : ZMod (p ^ 2)) + 1) ^ 2) := by
      apply Finset.prod_congr rfl
      intro j _
      have hp0 : (2 * (m : ZMod (p ^ 2)) + 1) ^ 2 = 0 := by
        have : (2 * (m : ZMod (p ^ 2)) + 1) = (p : ZMod (p ^ 2)) := by
          rw [← h2m1]; push_cast; ring
        rw [this, ← Nat.cast_pow, ZMod.natCast_self]
      rw [hp0, sub_zero]
    rw [hprod_eq] at hprod
    have hunit : IsUnit (∏ j ∈ range k, ((2 * (j : ZMod (p ^ 2)) + 1) ^ 2)) := by
      rw [IsUnit.prod_iff]
      intro j hj
      rw [Finset.mem_range] at hj
      refine (ZMod.isUnit_iff_coprime (2 * j + 1) (p ^ 2)).mpr ?_ |> fun h => by
        simpa [Nat.cast_add, Nat.cast_mul] using h.pow 2
      exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun hd => by
        have := Nat.le_of_dvd (by omega) hd; omega)).symm.pow_right 2
    have hcancel := hunit.mul_left_cancel (by
      calc (∏ j ∈ range k, (2 * (j : ZMod (p ^ 2)) + 1) ^ 2) *
              (((m + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k : ZMod (p ^ 2))
          = (∏ j ∈ range k, (2 * (j : ZMod (p ^ 2)) + 1) ^ 2) *
              (((m + k).choose (2 * k) : ZMod (p ^ 2)) * ((2 * k).choose k : ZMod (p ^ 2)) ^ 2 * (-16 : ZMod (p ^ 2)) ^ k) := by
            push_cast; ring
        _ = ((2 * k).choose k : ZMod (p ^ 2)) ^ 3 * (∏ j ∈ range k, (2 * (j : ZMod (p ^ 2)) + 1) ^ 2) := hprod
        _ = (∏ j ∈ range k, (2 * (j : ZMod (p ^ 2)) + 1) ^ 2) * ((2 * k).choose k : ZMod (p ^ 2)) ^ 3 := mul_comm _ _)
    simpa [Nat.cast_pow] using hcancel
  rw [Finset.sum_congr rfl hterm_eq] at hsum_re
  rw [← ZMod.natCast_eq_zero_iff, OeisA79727.a, Nat.cast_sum]
  simp_rw [Nat.cast_pow]
  exact hsum_re

/-- Babbage's congruence: `C(p * a, p * b) ≡ C(a, b) (mod p^2)` for any prime `p`. -/
private lemma choose_mul_mod_p2 (p : ℕ) [Fact p.Prime] (a b : ℕ) :
    ((p * a).choose (p * b) : ZMod (p ^ 2)) = (a.choose b : ZMod (p ^ 2)) := by
  -- Define g(X) in ℤ[X] such that (1 + X)^p = 1 + X^p + p * g(X) and every nonzero term of g has degree in (0, p)
  have hpow : ∃ g : ℤ[X], (1 + X : ℤ[X]) ^ p = 1 + X ^ p + C (p : ℤ) * g ∧
      ∀ k : ℕ, p ∣ k → g.coeff k = 0 := by
    refine ⟨∑ j ∈ Finset.Ioo 0 p, C ((p.choose j / p : ℕ) : ℤ) * X ^ j, ?_, ?_⟩
    · rw [add_pow]
      have hsplit : range (p + 1) = insert 0 (insert p (Finset.Ioo 0 p)) := by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
        have hp_pos := (Fact.out : p.Prime).pos
        omega
      have h0_notin : (0 : ℕ) ∉ insert p (Finset.Ioo 0 p) := by
        simp [(Fact.out : p.Prime).ne_zero.symm]
      have hp_notin : p ∉ Finset.Ioo 0 p := by simp
      rw [hsplit, Finset.sum_insert h0_notin, Finset.sum_insert hp_notin]
      simp only [one_pow, mul_one, one_mul, pow_zero, Nat.choose_zero_right, Nat.choose_self,
        Nat.cast_one, Nat.sub_self, Nat.sub_zero, Finset.mul_sum]
      have hsum_eq : ∑ x ∈ Finset.Ioo 0 p, X ^ (p - x) * (p.choose x : ℤ[X]) =
          ∑ j ∈ Finset.Ioo 0 p, C (p : ℤ) * (C ((p.choose j / p : ℕ) : ℤ) * X ^ j) := by
        -- Reindex x ↦ p - x (or use choose_symm)
        refine Finset.sum_bij (fun x _ => p - x) ?_ ?_ ?_ ?_
        · intro x hx; rw [Finset.mem_Ioo] at hx ⊢; omega
        · intro x1 hx1 x2 hx2 h; rw [Finset.mem_Ioo] at hx1 hx2; omega
        · intro y hy
          rw [Finset.mem_Ioo] at hy
          exact ⟨p - y, Finset.mem_Ioo.mpr (by omega), by omega⟩
        · intro x hx
          rw [Finset.mem_Ioo] at hx
          have hch_eq : p.choose x = p.choose (p - x) := (Nat.choose_symm (le_of_lt hx.2)).symm
          have hdvd : p ∣ p.choose (p - x) :=
            prime_dvd_choose_self Fact.out (by omega) (by omega)
          rw [hch_eq, ← mul_assoc, ← C_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hdvd,
            C_eq_natCast, mul_comm]
      rw [hsum_eq]; ring
    · intro k hk
      simp only [finsetSum_coeff, coeff_C_mul_X_pow]
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_Ioo] at hj
      split_ifs with hjk
      · subst hjk
        have := Nat.le_of_dvd hj.1 hk
        omega
      · rfl
  rcases hpow with ⟨g, hg, hg0⟩
  set fmap := Int.castRingHom (ZMod (p ^ 2))
  set g_p : (ZMod (p ^ 2))[X] := g.map fmap
  have h1Xp : ((1 + X : (ZMod (p ^ 2))[X]) ^ p) = 1 + X ^ p + C (p : ZMod (p ^ 2)) * g_p := by
    have := congr_arg (Polynomial.map fmap) hg
    simpa [g_p, fmap] using this
  have h1Xpa : ((1 + X : (ZMod (p ^ 2))[X]) ^ (p * a)) =
      (1 + X ^ p) ^ a + C (p : ZMod (p ^ 2)) * (∑ i ∈ range a, (1 + X ^ p) ^ i * (1 + X ^ p) ^ (a - 1 - i) * g_p) := by
    rw [pow_mul, h1Xp]
    -- Expand (A + p * B)^a = A^a + p * (...) in ZMod (p^2)[X] since (p : ZMod (p^2))^2 = 0
    have hp2_zero : (C (p : ZMod (p ^ 2)) : (ZMod (p ^ 2))[X]) ^ 2 = 0 := by
      rw [← C_pow, ← Nat.cast_pow, ZMod.natCast_self, map_zero]
    induction a with
    | zero => simp
    | succ a ih =>
      rw [pow_succ _ a, ih, pow_succ _ a]
      have hmul0 : C (p : ZMod (p ^ 2)) *
          (∑ i ∈ range a, (1 + X ^ p) ^ i * (1 + X ^ p) ^ (a - 1 - i) * g_p) *
          (C (p : ZMod (p ^ 2)) * g_p) = 0 := by
        calc _ = (C (p : ZMod (p ^ 2)) : (ZMod (p ^ 2))[X]) ^ 2 *
            ((∑ i ∈ range a, (1 + X ^ p) ^ i * (1 + X ^ p) ^ (a - 1 - i) * g_p) * g_p) := by ring
          _ = 0 := by rw [hp2_zero, zero_mul]
      have hsub_idx : ∀ i, a + 1 - 1 - i = a - i := fun i => by omega
      simp_rw [hsub_idx]
      rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
      have hreidx : ∑ x ∈ range a, (1 + X ^ p : (ZMod (p ^ 2))[X]) ^ x * (1 + X ^ p) ^ (a - x) * g_p =
          (∑ i ∈ range a, (1 + X ^ p) ^ i * (1 + X ^ p) ^ (a - 1 - i) * g_p) * (1 + X ^ p) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        have heq : a - 1 - i + 1 = a - i := by omega
        calc (1 + X ^ p : (ZMod (p ^ 2))[X]) ^ i * (1 + X ^ p) ^ (a - i) * g_p
            = (1 + X ^ p) ^ i * ((1 + X ^ p) ^ (a - 1 - i) * (1 + X ^ p)) * g_p := by
              rw [← pow_succ, heq]
          _ = (1 + X ^ p) ^ i * (1 + X ^ p) ^ (a - 1 - i) * g_p * (1 + X ^ p) := by ring
      rw [hreidx]
      linear_combination hmul0
  have hcoeff := congr_arg (fun q => q.coeff (p * b)) h1Xpa
  have hlhs : ((1 + X : (ZMod (p ^ 2))[X]) ^ (p * a)).coeff (p * b) = ((p * a).choose (p * b) : ZMod (p ^ 2)) := by
    rw [add_comm, coeff_X_add_one_pow]
  have hrhs1 : ((1 + X ^ p : (ZMod (p ^ 2))[X]) ^ a).coeff (p * b) = (a.choose b : ZMod (p ^ 2)) := by
    rw [add_pow, finsetSum_coeff]
    have h0 : ∀ j ∈ range (a + 1),
        ((1 : (ZMod (p ^ 2))[X]) ^ j * (X ^ p) ^ (a - j) * (a.choose j : (ZMod (p ^ 2))[X])).coeff (p * b) =
        if j = a - b ∧ b ≤ a then (a.choose b : ZMod (p ^ 2)) else 0 := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [one_pow, one_mul, ← pow_mul, ← C_eq_natCast, mul_comm, coeff_C_mul_X_pow]
      have hp_pos := (Fact.out : p.Prime).pos
      split_ifs with h1 h2 h2
      · rw [h2.1, Nat.choose_symm h2.2]
      · exfalso
        have : a - j = b := Nat.eq_of_mul_eq_mul_left hp_pos h1.symm
        exact h2 ⟨by omega, by omega⟩
      · exfalso
        exact h1 (by rw [h2.1, Nat.sub_sub_self h2.2])
      · rfl
    rw [Finset.sum_congr rfl h0]
    by_cases hba : b ≤ a
    · simp only [hba, and_true, Finset.sum_ite_eq', Finset.mem_range, show a - b < a + 1 by omega, ite_true]
    · simp only [hba, and_false, ite_false, Finset.sum_const_zero]
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
  have hrhs2 : (∑ i ∈ range a, (1 + X ^ p) ^ i * (1 + X ^ p) ^ (a - 1 - i) * g_p).coeff (p * b) = 0 := by
    rw [finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro i _
    have h1 : ((1 + X ^ p : (ZMod (p ^ 2))[X]) ^ i * (1 + X ^ p) ^ (a - 1 - i)) =
        (1 + X ^ p) ^ (i + (a - 1 - i)) := (pow_add _ _ _).symm
    rw [h1, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases hpx : p ∣ p * b - k
    · have hg_zero : g_p.coeff (p * b - k) = 0 := by
        rw [coeff_map, hg0 (p * b - k) hpx, map_zero]
      rw [hg_zero, mul_zero]
    · have hpx1 : ¬ p ∣ k := by
        intro h1
        have : p ∣ k + (p * b - k) := by rw [Nat.add_sub_of_le (by omega)]; exact dvd_mul_right p b
        exact hpx ((Nat.dvd_add_right h1).mp this)
      have hc1 : ((1 + X ^ p : (ZMod (p ^ 2))[X]) ^ (i + (a - 1 - i))).coeff k = 0 := by
        rw [add_pow, finsetSum_coeff]
        apply Finset.sum_eq_zero
        intro j _
        rw [one_pow, one_mul, ← pow_mul, ← C_eq_natCast, mul_comm, coeff_C_mul_X_pow,
          if_neg (fun heq => hpx1 ⟨_, heq⟩)]
      rw [hc1, zero_mul]
  rw [hlhs, coeff_add, hrhs1, coeff_C_mul, hrhs2, mul_zero, add_zero] at hcoeff
  exact hcoeff

private lemma prod_add_p_mod_p2 (p : ℕ) [Fact p.Prime] (c n : ℕ) (hn : n < p) :
    (∏ j ∈ range n, ((p * c + (j + 1) : ℕ) : ZMod (p ^ 2))) =
      (n ! : ZMod (p ^ 2)) *
        (1 + (p : ZMod (p ^ 2)) * (c : ZMod (p ^ 2)) *
          ∑ j ∈ range n, ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹) := by
  have hp2_zero : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (by omega)
    rw [Finset.prod_range_succ, ih', Finset.sum_range_succ, Nat.factorial_succ]
    have hunit : IsUnit (((n + 1 : ℕ) : ZMod (p ^ 2))) := by
      refine (ZMod.isUnit_iff_coprime (n + 1) (p ^ 2)).mpr ?_
      exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun hd => by
        have := Nat.le_of_dvd (Nat.succ_pos n) hd; omega)).symm.pow_right 2
    have hmul_inv : ((n + 1 : ℕ) : ZMod (p ^ 2)) * ((n + 1 : ℕ) : ZMod (p ^ 2))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ hunit
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hmul_inv ⊢
    linear_combination
      (n ! : ZMod (p ^ 2)) * (c : ZMod (p ^ 2)) ^ 2 *
        (∑ j ∈ range n, (((j : ZMod (p ^ 2)) + 1))⁻¹) * hp2_zero
      - (n ! : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * (c : ZMod (p ^ 2)) * hmul_inv

private lemma choose_two_mul_block_mod_p2 (p : ℕ) [Fact p.Prime] (q r : ℕ) (hr : 2 * r < p) :
    ((2 * (p * q + r)).choose (p * q + r) : ZMod (p ^ 2)) =
      ((2 * q).choose q : ZMod (p ^ 2)) * ((2 * r).choose r : ZMod (p ^ 2)) *
        (1 + 2 * (p : ZMod (p ^ 2)) * (q : ZMod (p ^ 2)) *
          ((∑ j ∈ range (2 * r), ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹) -
           (∑ j ∈ range r, ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹))) := by
  -- Nat identity: C(2(pq+r), pq+r) * (∏_{j<r} (pq+j+1))^2 = C(2pq, pq) * ∏_{j<2r} (2pq+j+1)
  have hnat : (2 * (p * q + r)).choose (p * q + r) * (∏ j ∈ range r, (p * q + (j + 1))) ^ 2 =
      (2 * (p * q)).choose (p * q) * ∏ j ∈ range (2 * r), (p * (2 * q) + (j + 1)) := by
    have hprod_fact : ∀ (a k : ℕ), a ! * ∏ j ∈ range k, (a + (j + 1)) = (a + k)! := by
      intro a k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.prod_range_succ, ← mul_assoc, ih, ← add_assoc, Nat.factorial_succ, mul_comm]
    have h1 := Nat.choose_mul_factorial_mul_factorial (show p * q + r ≤ 2 * (p * q + r) by omega)
    have h2 := Nat.choose_mul_factorial_mul_factorial (show p * q ≤ 2 * (p * q) by omega)
    rw [show 2 * (p * q + r) - (p * q + r) = p * q + r by omega] at h1
    rw [show 2 * (p * q) - p * q = p * q by omega] at h2
    have hfac_ne : (p * q)! * (p * q)! ≠ 0 := by positivity
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hfac_ne)
    have hp1 := hprod_fact (p * q) r
    have hp2 := hprod_fact (2 * (p * q)) (2 * r)
    have hp2' : (2 * (p * q))! * ∏ j ∈ range (2 * r), (p * (2 * q) + (j + 1)) = (2 * (p * q + r))! := by
      have : (∏ j ∈ range (2 * r), (p * (2 * q) + (j + 1))) =
          ∏ j ∈ range (2 * r), (2 * (p * q) + (j + 1)) :=
        Finset.prod_congr rfl (fun j _ => by ring)
      rw [this, hp2]
      congr 1; omega
    calc (p * q)! * (p * q)! * ((2 * (p * q + r)).choose (p * q + r) * (∏ j ∈ range r, (p * q + (j + 1))) ^ 2)
        = (2 * (p * q + r)).choose (p * q + r) * ((p * q)! * ∏ j ∈ range r, (p * q + (j + 1))) *
            ((p * q)! * ∏ j ∈ range r, (p * q + (j + 1))) := by ring
      _ = (2 * (p * q + r))! := by rw [hp1]; exact h1
      _ = (2 * (p * q))! * ∏ j ∈ range (2 * r), (p * (2 * q) + (j + 1)) := hp2'.symm
      _ = (2 * (p * q)).choose (p * q) * (p * q)! * (p * q)! * ∏ j ∈ range (2 * r), (p * (2 * q) + (j + 1)) := by
          rw [h2]
      _ = (p * q)! * (p * q)! * ((2 * (p * q)).choose (p * q) * ∏ j ∈ range (2 * r), (p * (2 * q) + (j + 1))) := by
          ring
  have hcast := congr_arg (Nat.cast (R := ZMod (p ^ 2))) hnat
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_prod] at hcast
  rw [prod_add_p_mod_p2 p q r (by omega), prod_add_p_mod_p2 p (2 * q) (2 * r) hr,
    show 2 * (p * q) = p * (2 * q) by ring, choose_mul_mod_p2 p (2 * q) q] at hcast
  have h2rf : ((2 * r)! : ZMod (p ^ 2)) = ((2 * r).choose r : ZMod (p ^ 2)) * (r ! : ZMod (p ^ 2)) ^ 2 := by
    have h := Nat.choose_mul_factorial_mul_factorial (show r ≤ 2 * r by omega)
    rw [show 2 * r - r = r by omega] at h
    have := congr_arg (Nat.cast (R := ZMod (p ^ 2))) h
    push_cast at this; linear_combination -this
  rw [h2rf] at hcast
  have hr_unit : IsUnit ((r ! : ZMod (p ^ 2)) ^ 2) := by
    have hcop : Nat.Coprime (r !) p := by
      rw [Nat.coprime_comm, (Fact.out : p.Prime).coprime_iff_not_dvd]
      intro hd
      have := prime_dvd_factorial_le Fact.out hd
      omega
    exact ((ZMod.isUnit_iff_coprime (r !) (p ^ 2)).mpr (hcop.pow_right 2)).pow 2
  have hp2_zero : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  set H1 : ZMod (p ^ 2) := ∑ j ∈ range r, ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹
  set H2 : ZMod (p ^ 2) := ∑ j ∈ range (2 * r), ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹
  have h1_unit : IsUnit ((1 + (p : ZMod (p ^ 2)) * (q : ZMod (p ^ 2)) * H1) ^ 2) := by
    refine (IsUnit.of_mul_eq_one (1 - (p : ZMod (p ^ 2)) * q * H1) ?_).pow 2
    linear_combination -(q : ZMod (p ^ 2)) ^ 2 * H1 ^ 2 * hp2_zero
  apply (hr_unit.mul h1_unit).mul_right_cancel
  calc ((2 * (p * q + r)).choose (p * q + r) : ZMod (p ^ 2)) *
        ((r ! : ZMod (p ^ 2)) ^ 2 * (1 + (p : ZMod (p ^ 2)) * q * H1) ^ 2)
      = ((2 * (p * q + r)).choose (p * q + r) : ZMod (p ^ 2)) *
        ((r ! : ZMod (p ^ 2)) * (1 + (p : ZMod (p ^ 2)) * q * H1)) ^ 2 := by ring
    _ = ((2 * q).choose q : ZMod (p ^ 2)) *
        (((2 * r).choose r : ZMod (p ^ 2)) * (r ! : ZMod (p ^ 2)) ^ 2 *
          (1 + (p : ZMod (p ^ 2)) * ((2 * q : ℕ) : ZMod (p ^ 2)) * H2)) := hcast
    _ = ((2 * q).choose q : ZMod (p ^ 2)) * ((2 * r).choose r : ZMod (p ^ 2)) *
        (1 + 2 * (p : ZMod (p ^ 2)) * q * (H2 - H1)) *
        ((r ! : ZMod (p ^ 2)) ^ 2 * (1 + (p : ZMod (p ^ 2)) * q * H1) ^ 2) := by
      push_cast
      linear_combination
        -((2 * q).choose q : ZMod (p ^ 2)) * ((2 * r).choose r : ZMod (p ^ 2)) *
          (r ! : ZMod (p ^ 2)) ^ 2 * (q : ZMod (p ^ 2)) ^ 2 *
          (H1 ^ 2 + 4 * H1 * (H2 - H1) + 2 * (p : ZMod (p ^ 2)) * q * H1 ^ 2 * (H2 - H1)) * hp2_zero

private lemma choose_two_mul_block_cube_mod_p2 (p : ℕ) [Fact p.Prime] (q r : ℕ) (hr : 2 * r < p) :
    (((2 * (p * q + r)).choose (p * q + r) : ℕ) ^ 3 : ZMod (p ^ 2)) =
      ((2 * q).choose q : ZMod (p ^ 2)) ^ 3 * ((2 * r).choose r : ZMod (p ^ 2)) ^ 3 *
        (1 + 6 * (p : ZMod (p ^ 2)) * (q : ZMod (p ^ 2)) *
          ((∑ j ∈ range (2 * r), ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹) -
           (∑ j ∈ range r, ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹))) := by
  have h := choose_two_mul_block_mod_p2 p q r hr
  have hp2_zero : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  set d : ZMod (p ^ 2) :=
    (∑ j ∈ range (2 * r), ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹) -
    (∑ j ∈ range r, ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹)
  rw [h, mul_pow, mul_pow]
  have hcube : (1 + 2 * (p : ZMod (p ^ 2)) * q * d) ^ 3 = 1 + 6 * (p : ZMod (p ^ 2)) * q * d := by
    linear_combination (12 * (q : ZMod (p ^ 2)) ^ 2 * d ^ 2 +
      8 * (p : ZMod (p ^ 2)) * (q : ZMod (p ^ 2)) ^ 3 * d ^ 3) * hp2_zero
  rw [hcube]

private lemma choose_two_mul_dvd_p_of_gt_half (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (q r : ℕ) (hr1 : (p - 1) / 2 < r) (hr2 : r < p) :
    p ∣ (2 * (p * q + r)).choose (p * q + r) := by
  have hlucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (p := p) (n := 2 * (p * q + r)) (k := p * q + r)
  have h2r_ge : p ≤ 2 * r := by
    have := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2)
    omega
  have hmod1 : 2 * (p * q + r) % p = 2 * r - p := by
    have heq : 2 * (p * q + r) = p * (2 * q + 1) + (2 * r - p) := by
      have hlin : 2 * (p * q + r) + p = p * (2 * q + 1) + 2 * r := by ring
      omega
    rw [heq, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hmod2 : (p * q + r) % p = r := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr2]
  have hlt : 2 * r - p < r := by omega
  rw [hmod1, hmod2, Nat.choose_eq_zero_of_lt hlt, zero_mul] at hlucas
  exact Nat.dvd_of_mod_eq_zero hlucas

private lemma shiftedLegendre_add_p_eval_x0_eq_zero {p : ℕ} [Fact p.Prime] (hp : OeisA3625.A p) :
    aeval (ZOmega.x0 : ZOmega (ZMod p)) (shiftedLegendre (p + (p - 1) / 2)) = 0 := by
  set m := (p - 1) / 2
  have hp2 : p ≠ 2 := A3625_ne_two hp
  have h2m1 : 2 * m + 1 = p := by
    have := Nat.odd_iff.mp (A3625_odd hp)
    omega
  -- Show shiftedLegendre (p + m) ≡ (1 - 2 * X^p) * shiftedLegendre m in (ZMod p)[X]
  set fmap := Int.castRingHom (ZMod p)
  have hpoly : (shiftedLegendre (p + m)).map fmap =
      (1 - 2 * X ^ p) * (shiftedLegendre m).map fmap := by
    ext k
    rw [coeff_map, coeff_shiftedLegendre]
    rw [sub_mul, one_mul, coeff_sub, mul_assoc (2 : (ZMod p)[X]), coeff_ofNat_mul, coeff_X_pow_mul']
    have hch1 := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := p + m) (k := k)
    have hch2 := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := p + m + k) (k := p + m)
    have hpm_mod : (p + m) % p = m := by
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have hpm_div : (p + m) / p = 1 := by
      have hp_pos := (Fact.out : p.Prime).pos
      rw [show p + m = p * 1 + m by ring, Nat.mul_add_div hp_pos, Nat.div_eq_of_lt (by omega)]
    by_cases hkp : k < p
    · rw [if_neg (not_le.mpr hkp), mul_zero, sub_zero, coeff_map, coeff_shiftedLegendre]
      by_cases hkm : k ≤ m
      · have h1 : ((p + m).choose k : ZMod p) = (m.choose k : ZMod p) := by
          rw [ZMod.natCast_eq_natCast_iff]
          simpa [hpm_mod, hpm_div, Nat.mod_eq_of_lt hkp, Nat.div_eq_of_lt hkp] using hch1
        have h2 : ((p + m + k).choose (p + m) : ZMod p) = ((m + k).choose m : ZMod p) := by
          rw [ZMod.natCast_eq_natCast_iff]
          have hmod : (p + m + k) % p = m + k := by
            rw [show p + m + k = p + (m + k) by omega, Nat.add_mod_left,
              Nat.mod_eq_of_lt (by omega)]
          have hdiv : (p + m + k) / p = 1 := by
            have hp_pos := (Fact.out : p.Prime).pos
            rw [show p + m + k = p * 1 + (m + k) by omega, Nat.mul_add_div hp_pos,
              Nat.div_eq_of_lt (by omega)]
          simpa [hpm_mod, hpm_div, hmod, hdiv] using hch2
        simp only [fmap, eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
          Int.cast_natCast, h1, h2]
      · have h1 : ((p + m).choose k : ZMod p) = 0 := by
          rw [ZMod.natCast_eq_zero_iff]
          rw [hpm_mod, Nat.mod_eq_of_lt hkp, Nat.choose_eq_zero_of_lt (show m < k by omega), zero_mul] at hch1
          exact Nat.dvd_of_mod_eq_zero hch1
        have hm0 : (m.choose k : ZMod p) = 0 := by
          rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
        simp only [fmap, eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
          Int.cast_natCast, h1, hm0, mul_zero, zero_mul]
    · rw [if_pos (by omega), coeff_map, coeff_shiftedLegendre, coeff_map, coeff_shiftedLegendre]
      have hm_lt : m < k := by omega
      rw [Nat.choose_eq_zero_of_lt hm_lt]
      simp only [fmap, eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
        Int.cast_natCast, Nat.cast_zero, mul_zero, zero_mul]
      by_cases hk2 : k ≤ p + m
      · set r := k - p
        have hkr : k = p + r := by omega
        have hrm : r ≤ m := by omega
        have hk_mod : k % p = r := by
          rw [hkr, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        have hk_div : k / p = 1 := by
          have hp_pos := (Fact.out : p.Prime).pos
          rw [hkr, show p + r = p * 1 + r by omega, Nat.mul_add_div hp_pos,
            Nat.div_eq_of_lt (by omega)]
        have h1 : ((p + m).choose k : ZMod p) = (m.choose r : ZMod p) := by
          rw [ZMod.natCast_eq_natCast_iff]
          simpa [hpm_mod, hpm_div, hk_mod, hk_div] using hch1
        have h2 : ((p + m + k).choose (p + m) : ZMod p) = 2 * ((m + r).choose m : ZMod p) := by
          have hmod : (p + m + k) % p = m + r := by
            rw [show p + m + k = p * 2 + (m + r) by omega, Nat.mul_add_mod,
              Nat.mod_eq_of_lt (by omega)]
          have hdiv : (p + m + k) / p = 2 := by
            have hp_pos := (Fact.out : p.Prime).pos
            rw [show p + m + k = p * 2 + (m + r) by omega, Nat.mul_add_div hp_pos,
              Nat.div_eq_of_lt (by omega)]
          have h2' : (p + m + k).choose (p + m) ≡ (m + r).choose m * 2 [MOD p] := by
            simpa [hpm_mod, hpm_div, hmod, hdiv] using hch2
          have hcast := (ZMod.natCast_eq_natCast_iff _ _ p).mpr h2'
          push_cast at hcast; linear_combination hcast
        have hsign : (-1 : ZMod p) ^ k = -((-1 : ZMod p) ^ r) := by
          rw [hkr, pow_add, (A3625_odd hp).neg_one_pow]; ring
        rw [h1, h2, hsign]; ring
      · rw [Nat.choose_eq_zero_of_lt (by omega : p + m < k),
          Nat.choose_eq_zero_of_lt (by omega : m < k - p)]
        simp
  -- Evaluate hpoly at x0 : ZOmega (ZMod p)
  have heval_comm : ∀ q : ℤ[X],
      aeval (ZOmega.x0 : ZOmega (ZMod p)) q =
        eval₂ ZOmega.of (ZOmega.x0 : ZOmega (ZMod p)) (q.map fmap) := by
    intro q
    rw [aeval_def, eval₂_map]
    congr 1
    ext
    simp [fmap]
  rw [heval_comm, hpoly, eval₂_mul, ← heval_comm, shiftedLegendre_eval_x0_eq_zero hp, mul_zero]

private lemma sum_harmDiff_eq_zero_mod_p {p : ℕ} [Fact p.Prime] (hp : OeisA3625.A p) (hp5 : 5 ≤ p) :
    (p : ZMod (p ^ 2)) * (∑ r ∈ range ((p - 1) / 2 + 1),
      (((2 * r).choose r : ℕ) ^ 3 : ZMod (p ^ 2)) *
        ((∑ j ∈ range (2 * r), ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹) -
         (∑ j ∈ range r, ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹))) = 0 := by
  set m := (p - 1) / 2
  have hp2 : p ≠ 2 := A3625_ne_two hp
  have h2m1 : 2 * m + 1 = p := by
    have := Nat.odd_iff.mp (A3625_odd hp)
    omega
  have hsq0 : aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) ((shiftedLegendre (p + m)) ^ 2) = 0 :=
    eval_x0_sq_eq_zero_mod_p2 (shiftedLegendre_add_p_eval_x0_eq_zero hp)
  rw [clausen_poly_identity (p + m), aeval_comp] at hsq0
  have hz_val : aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) (X ^ 2 - X : ℤ[X]) = (-16 : ZOmega (ZMod (p ^ 2))) := by
    simp only [map_sub, map_pow, aeval_X, ZOmega.neg_x0_mul_one_sub]
  rw [hz_val, map_sum] at hsq0
  have hsum_re : (∑ k ∈ range (p + m + 1),
      ((((p + m) + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k : ZMod (p ^ 2))) = 0 := by
    have hre := congr_arg ZOmega.re hsq0
    simp only [ZOmega.zero_re] at hre
    rw [← hre]
    have hre_sum : ∀ s : Finset ℕ, ∀ f : ℕ → ZOmega (ZMod (p ^ 2)), (∑ k ∈ s, f k).re = ∑ k ∈ s, (f k).re := by
      intro s f
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => simp [Finset.sum_insert ha, ih]
    rw [hre_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_mul, aeval_C, map_pow, aeval_X]
    have hpow : ((-16 : ZOmega (ZMod (p ^ 2))) ^ k) = ZOmega.of ((-16 : ZMod (p ^ 2)) ^ k) := by
      rw [map_pow]; congr 1; apply ZOmega.ext <;> simp
    have hcast : (algebraMap ℤ (ZOmega (ZMod (p ^ 2)))
        ((((p + m) + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2)) =
        ZOmega.of ((((p + m) + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 : ZMod (p ^ 2)) := by
      apply ZOmega.ext <;> simp [eq_intCast]
    rw [hpow, hcast, ← map_mul, ZOmega.of_re]
    push_cast; ring
  -- Split range (p + m + 1) into [0..m], (m..p-1], [p..p+m]
  have hsplit1 : range (p + m + 1) = range p ∪ (range (m + 1)).image (fun r => p + r) := by
    ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_image]
    constructor
    · intro hk
      by_cases h : k < p
      · exact Or.inl h
      · exact Or.inr ⟨k - p, by omega, by omega⟩
    · rintro (h | ⟨r, hr, rfl⟩) <;> omega
  have hdisj1 : Disjoint (range p) ((range (m + 1)).image (fun r => p + r)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    rw [Finset.mem_range] at hk1
    rw [Finset.mem_image] at hk2
    rcases hk2 with ⟨r, _, rfl⟩
    omega
  rw [hsplit1, Finset.sum_union hdisj1, Finset.sum_image (fun a _ b _ h => by omega)] at hsum_re
  -- Part 1: sum over range p splits into [0..m] (which equals a m ≡ 0) and (m..p-1] (each ≡ 0 since p^3 | C(2k,k)^3)
  have hsplit2 : range p = range (m + 1) ∪ Finset.Ico (m + 1) p := by
    ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  have hdisj2 : Disjoint (range (m + 1)) (Finset.Ico (m + 1) p) := by
    rw [Finset.disjoint_left]; intro k h1 h2; rw [Finset.mem_range] at h1; rw [Finset.mem_Ico] at h2; omega
  rw [hsplit2, Finset.sum_union hdisj2] at hsum_re
  -- For k ≤ m, term = C(2k,k)^3 mod p^2
  have hpartA : (∑ k ∈ range (m + 1),
      ((((p + m) + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k : ZMod (p ^ 2))) = 0 := by
    have hterm : ∀ k ∈ range (m + 1),
        ((((p + m) + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k : ZMod (p ^ 2)) =
        (((2 * k).choose k : ℕ) ^ 3 : ZMod (p ^ 2)) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hprod := congr_arg (Int.castRingHom (ZMod (p ^ 2))) (clausen_term_prod_identity (p + m) k (by omega))
      simp only [map_mul, map_prod, map_pow, map_sub, map_add, map_one, map_ofNat, map_natCast,
        eq_intCast, Int.cast_neg, Int.cast_ofNat] at hprod
      have hprod_eq : (∏ j ∈ range k, ((2 * (j : ZMod (p ^ 2)) + 1) ^ 2 -
          (2 * ((p + m : ℕ) : ZMod (p ^ 2)) + 1) ^ 2)) =
          ∏ j ∈ range k, ((2 * (j : ZMod (p ^ 2)) + 1) ^ 2) := by
        apply Finset.prod_congr rfl
        intro j _
        have h3p : (2 * ((p + m : ℕ) : ZMod (p ^ 2)) + 1) ^ 2 = 0 := by
          have : (2 * ((p + m : ℕ) : ZMod (p ^ 2)) + 1) = 3 * (p : ZMod (p ^ 2)) := by
            have heq : 2 * (p + m) + 1 = 3 * p := by omega
            have := congr_arg (Nat.cast (R := ZMod (p ^ 2))) heq
            simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using this
          rw [this, mul_pow, ← Nat.cast_pow, ZMod.natCast_self, mul_zero]
        rw [h3p, sub_zero]
      rw [hprod_eq] at hprod
      have hunit : IsUnit (∏ j ∈ range k, ((2 * (j : ZMod (p ^ 2)) + 1) ^ 2)) := by
        rw [IsUnit.prod_iff]
        intro j hj
        rw [Finset.mem_range] at hj
        refine (ZMod.isUnit_iff_coprime (2 * j + 1) (p ^ 2)).mpr ?_ |> fun h => by
          simpa [Nat.cast_add, Nat.cast_mul] using h.pow 2
        exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun hd => by
          have := Nat.le_of_dvd (by omega) hd; omega)).symm.pow_right 2
      have hcancel := hunit.mul_left_cancel (by
        calc (∏ j ∈ range k, (2 * (j : ZMod (p ^ 2)) + 1) ^ 2) *
                ((((p + m) + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k : ZMod (p ^ 2))
            = (∏ j ∈ range k, (2 * (j : ZMod (p ^ 2)) + 1) ^ 2) *
                ((((p + m) + k).choose (2 * k) : ZMod (p ^ 2)) * ((2 * k).choose k : ZMod (p ^ 2)) ^ 2 * (-16 : ZMod (p ^ 2)) ^ k) := by
              push_cast; ring
          _ = ((2 * k).choose k : ZMod (p ^ 2)) ^ 3 * (∏ j ∈ range k, (2 * (j : ZMod (p ^ 2)) + 1) ^ 2) := hprod
          _ = (∏ j ∈ range k, (2 * (j : ZMod (p ^ 2)) + 1) ^ 2) * ((2 * k).choose k : ZMod (p ^ 2)) ^ 3 := mul_comm _ _)
      simpa [Nat.cast_pow] using hcancel
    rw [Finset.sum_congr rfl hterm]
    simp_rw [← Nat.cast_pow]
    rw [← Nat.cast_sum]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_a_half hp)
  -- Helper for k > m (in [m+1..p+m]): cancel the single j = m factor p^2 from clausen_term_prod_identity!
  have hgt_m : ∀ k : ℕ, m < k → k ≤ p + m →
      ((((p + m) + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k : ZMod (p ^ 2)) =
      -8 * (((2 * k).choose k : ℕ) ^ 3 : ZMod (p ^ 2)) := by
    intro k hkm hk_le
    have hprod := clausen_term_prod_identity (p + m) k hk_le
    have hm_mem : m ∈ range k := Finset.mem_range.mpr hkm
    rw [← Finset.mul_prod_erase _ _ hm_mem, ← Finset.mul_prod_erase _ _ hm_mem] at hprod
    have hfac1 : (2 * (m : ℤ) + 1) ^ 2 = (p : ℤ) ^ 2 := by
      have := congr_arg (Nat.cast (R := ℤ)) h2m1; push_cast at this; rw [this]
    have hfac2 : (2 * (m : ℤ) + 1) ^ 2 - (2 * ((p + m : ℕ) : ℤ) + 1) ^ 2 = (p : ℤ) ^ 2 * (-8) := by
      have e1 := congr_arg (Nat.cast (R := ℤ)) h2m1
      have e2 : (2 * ((p + m : ℕ) : ℤ) + 1) = 3 * (p : ℤ) := by push_cast at e1 ⊢; linarith
      push_cast at e1; rw [e1, e2]; ring
    rw [hfac2, hfac1] at hprod
    have hp2_ne : ((p : ℤ) ^ 2) ≠ 0 := by positivity
    have hcancel_z : (∏ j ∈ (range k).erase m, (2 * (j : ℤ) + 1) ^ 2) *
        (((p + m + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k) =
        (-8) * (((2 * k).choose k : ℤ) ^ 3) *
        (∏ j ∈ (range k).erase m, ((2 * (j : ℤ) + 1) ^ 2 - (2 * ((p + m : ℕ) : ℤ) + 1) ^ 2)) := by
      apply mul_left_cancel₀ hp2_ne
      linear_combination hprod
    have hcast := congr_arg (Int.castRingHom (ZMod (p ^ 2))) hcancel_z
    simp only [map_mul, map_prod, map_pow, map_sub, map_add, map_one, map_neg, map_ofNat,
      map_natCast] at hcast
    have hprod_eq : (∏ j ∈ (range k).erase m, ((2 * (j : ZMod (p ^ 2)) + 1) ^ 2 -
        (2 * ((p + m : ℕ) : ZMod (p ^ 2)) + 1) ^ 2)) =
        ∏ j ∈ (range k).erase m, ((2 * (j : ZMod (p ^ 2)) + 1) ^ 2) := by
      apply Finset.prod_congr rfl
      intro j _
      have h3p : (2 * ((p + m : ℕ) : ZMod (p ^ 2)) + 1) ^ 2 = 0 := by
        have : (2 * ((p + m : ℕ) : ZMod (p ^ 2)) + 1) = 3 * (p : ZMod (p ^ 2)) := by
          have heq : 2 * (p + m) + 1 = 3 * p := by omega
          have := congr_arg (Nat.cast (R := ZMod (p ^ 2))) heq
          simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using this
        rw [this, mul_pow, ← Nat.cast_pow, ZMod.natCast_self, mul_zero]
      rw [h3p, sub_zero]
    rw [hprod_eq] at hcast
    have hunit : IsUnit (∏ j ∈ (range k).erase m, ((2 * (j : ZMod (p ^ 2)) + 1) ^ 2)) := by
      rw [IsUnit.prod_iff]
      intro j hj
      rw [Finset.mem_erase, Finset.mem_range] at hj
      refine (ZMod.isUnit_iff_coprime (2 * j + 1) (p ^ 2)).mpr ?_ |> fun h => by
        simpa [Nat.cast_add, Nat.cast_mul] using h.pow 2
      exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun hd => by
        rcases hd with ⟨t, ht⟩
        -- 2*j + 1 < 2*(p + m) + 1 = 3*p, and j ≠ m so 2*j + 1 ≠ p, and 2*j + 1 is odd so ≠ 2*p!
        have h3p_lt : 2 * j + 1 < 3 * p := by omega
        have ht_lt : t < 3 := by nlinarith
        have ht_ne0 : t ≠ 0 := by intro h0; rw [h0] at ht; omega
        have ht_ne1 : t ≠ 1 := by intro h1; rw [h1] at ht; omega
        have ht_ne2 : t ≠ 2 := by intro h2; rw [h2] at ht; omega
        omega)).symm.pow_right 2
    have hcancel := hunit.mul_left_cancel (by
      calc (∏ j ∈ (range k).erase m, (2 * (j : ZMod (p ^ 2)) + 1) ^ 2) *
              ((((p + m) + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k : ZMod (p ^ 2))
          = (∏ j ∈ (range k).erase m, (2 * (j : ZMod (p ^ 2)) + 1) ^ 2) *
              (((p + m + k).choose (2 * k) : ZMod (p ^ 2)) * ((2 * k).choose k : ZMod (p ^ 2)) ^ 2 * (-16 : ZMod (p ^ 2)) ^ k) := by
            push_cast; ring
        _ = (-8) * ((2 * k).choose k : ZMod (p ^ 2)) ^ 3 *
              (∏ j ∈ (range k).erase m, (2 * (j : ZMod (p ^ 2)) + 1) ^ 2) := hcast
        _ = (∏ j ∈ (range k).erase m, (2 * (j : ZMod (p ^ 2)) + 1) ^ 2) *
              (-8 * ((2 * k).choose k : ZMod (p ^ 2)) ^ 3) := by ring)
    simpa [Nat.cast_pow] using hcancel
  -- Part 2: middle range Ico (m + 1) p vanishes since p | C(2k, k) => p^3 | C(2k, k)^3
  have hpartB : (∑ k ∈ Finset.Ico (m + 1) p,
      ((((p + m) + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k : ZMod (p ^ 2))) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [hgt_m k (by omega) (by omega)]
    have hd : p ∣ (2 * k).choose k := by
      simpa using choose_two_mul_dvd_p_of_gt_half p hp2 0 k (by omega) hk.2
    have hd2 : p ^ 2 ∣ ((2 * k).choose k) ^ 3 :=
      dvd_trans (pow_dvd_pow p (by decide : 2 ≤ 3)) (pow_dvd_pow_of_dvd hd 3)
    rw [← Nat.cast_pow, (ZMod.natCast_eq_zero_iff _ _).mpr hd2, mul_zero]
  -- Part 3: upper range k = p + r (0 ≤ r ≤ m)
  rw [hpartA, hpartB, add_zero, zero_add] at hsum_re
  have hpartC : ∀ r ∈ range (m + 1),
      ((((p + m) + (p + r)).choose (2 * (p + r)) : ℤ) *
        ((2 * (p + r)).choose (p + r) : ℤ) ^ 2 * (-16 : ℤ) ^ (p + r) : ZMod (p ^ 2)) =
      -64 * (((2 * r).choose r : ℕ) ^ 3 : ZMod (p ^ 2)) -
      384 * (p : ZMod (p ^ 2)) * (((2 * r).choose r : ℕ) ^ 3 : ZMod (p ^ 2)) *
        ((∑ j ∈ range (2 * r), ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹) -
         (∑ j ∈ range r, ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹)) := by
    intro r hr
    rw [Finset.mem_range] at hr
    rw [hgt_m (p + r) (by omega) (by omega)]
    have hblk := choose_two_mul_block_cube_mod_p2 p 1 r (by omega)
    rw [mul_one, show (2 : ℕ).choose 1 = 2 by decide] at hblk
    rw [hblk]
    push_cast; ring
  rw [Finset.sum_congr rfl hpartC, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum_re
  have hS0 : (∑ r ∈ range (m + 1), (((2 * r).choose r : ℕ) ^ 3 : ZMod (p ^ 2))) = 0 := by
    simp_rw [← Nat.cast_pow]
    rw [← Nat.cast_sum]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_a_half hp)
  rw [hS0, mul_zero, zero_sub, neg_eq_zero] at hsum_re
  have h384 : (384 : ZMod (p ^ 2)) *
      ((p : ZMod (p ^ 2)) * (∑ r ∈ range (m + 1),
        (((2 * r).choose r : ℕ) ^ 3 : ZMod (p ^ 2)) *
          ((∑ j ∈ range (2 * r), ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹) -
           (∑ j ∈ range r, ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹)))) = 0 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    convert hsum_re using 1
    apply Finset.sum_congr rfl
    intro r _; ring
  have h384_unit : IsUnit (384 : ZMod (p ^ 2)) := by
    refine (ZMod.isUnit_iff_coprime 384 (p ^ 2)).mpr ?_
    have hcop : Nat.Coprime 384 p := by
      rw [Nat.coprime_comm, (Fact.out : p.Prime).coprime_iff_not_dvd]
      intro hd
      have h384_eq : 384 = 2 ^ 7 * 3 := by decide
      rw [h384_eq] at hd
      rcases (Fact.out : p.Prime).dvd_mul.mp hd with h2 | h3
      · have := (Fact.out : p.Prime).dvd_of_dvd_pow h2
        have := Nat.le_of_dvd (by decide) this; omega
      · have := Nat.le_of_dvd (by decide) h3; omega
    exact hcop.pow_right 2
  exact h384_unit.mul_right_eq_zero.mp h384

/- ### Section 6: Block expansion for `p = 3` and `p ≥ 5`, and CRT for `conjecture4` -/

private lemma dvd_nine_a_three_mul_odd (t : ℕ) :
    9 ∣ OeisA79727.a (3 * t + 1) := by
  induction t with
  | zero =>
    change 9 ∣ OeisA79727.a 1
    decide
  | succ t ih =>
    have hsplit : OeisA79727.a (3 * (t + 1) + 1) =
        OeisA79727.a (3 * t + 1) +
        (2 * (3 * t + 2)).choose (3 * t + 2) ^ 3 +
        ((2 * (3 * t + 3)).choose (3 * t + 3) ^ 3 +
         (2 * (3 * t + 4)).choose (3 * t + 4) ^ 3) := by
      simp only [OeisA79727.a]
      rw [show 3 * (t + 1) + 1 + 1 = (3 * t + 1 + 1) + 3 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      ring
    rw [hsplit]
    refine dvd_add (dvd_add ih ?_) ?_
    · -- 9 ∣ C(6t+4, 3t+2)^3 because 3 ∣ C(6t+4, 3t+2)
      have h3p : Fact (Nat.Prime 3) := ⟨by decide⟩
      have hd3 : 3 ∣ (2 * (3 * t + 2)).choose (3 * t + 2) :=
        choose_two_mul_dvd_p_of_gt_half 3 (by decide) t 2 (by decide) (by decide)
      exact dvd_trans (by decide : 9 ∣ 3 ^ 3) (pow_dvd_pow_of_dvd hd3 3)
    · -- 9 ∣ C(6q, 3q)^3 + C(6q+2, 3q+1)^3 for q = t + 1
      set q := t + 1
      have hch : (3 * q + 1) * (6 * q + 2).choose (3 * q + 1) = 2 * (6 * q + 1) * (6 * q).choose (3 * q) := by
        have e1 := Nat.add_one_mul_choose_eq (6 * q + 1) (3 * q)
        have e2 := Nat.choose_succ_right_eq (6 * q + 1) (3 * q)
        have e3 := Nat.add_one_mul_choose_eq (6 * q) (3 * q)
        have hsub : 6 * q + 1 - 3 * q = 3 * q + 1 := by omega
        rw [hsub] at e2
        have e4 : (6 * q + 1).choose (3 * q) = (6 * q + 1).choose (3 * q + 1) :=
          Nat.choose_symm_of_eq_add (by omega : 6 * q + 1 = 3 * q + (3 * q + 1))
        nlinarith
      have hmul : (3 * q + 1) ^ 3 * ((2 * (3 * q)).choose (3 * q) ^ 3 +
          (2 * (3 * q + 1)).choose (3 * q + 1) ^ 3) =
          9 * ((6 * q).choose (3 * q) ^ 3 * (195 * q ^ 3 + 99 * q ^ 2 + 17 * q + 1)) := by
        have e1 : 2 * (3 * q) = 6 * q := by omega
        have e2 : 2 * (3 * q + 1) = 6 * q + 2 := by omega
        rw [e1, e2]
        have hch3 : (3 * q + 1) ^ 3 * (6 * q + 2).choose (3 * q + 1) ^ 3 =
            (2 * (6 * q + 1)) ^ 3 * (6 * q).choose (3 * q) ^ 3 := by
          calc (3 * q + 1) ^ 3 * (6 * q + 2).choose (3 * q + 1) ^ 3
              = ((3 * q + 1) * (6 * q + 2).choose (3 * q + 1)) ^ 3 := by ring
            _ = (2 * (6 * q + 1) * (6 * q).choose (3 * q)) ^ 3 := by rw [hch]
            _ = (2 * (6 * q + 1)) ^ 3 * (6 * q).choose (3 * q) ^ 3 := by ring
        calc (3 * q + 1) ^ 3 * ((6 * q).choose (3 * q) ^ 3 + (6 * q + 2).choose (3 * q + 1) ^ 3)
            = (3 * q + 1) ^ 3 * (6 * q).choose (3 * q) ^ 3 +
              (3 * q + 1) ^ 3 * (6 * q + 2).choose (3 * q + 1) ^ 3 := by ring
          _ = ((3 * q + 1) ^ 3 + (2 * (6 * q + 1)) ^ 3) * (6 * q).choose (3 * q) ^ 3 := by
              rw [hch3]; ring
          _ = 9 * ((6 * q).choose (3 * q) ^ 3 * (195 * q ^ 3 + 99 * q ^ 2 + 17 * q + 1)) := by ring
      have hcop : Nat.Coprime 9 ((3 * q + 1) ^ 3) := by
        have h3 : Nat.Coprime 3 (3 * q + 1) := by
          rw [(by decide : Nat.Prime 3).coprime_iff_not_dvd]; omega
        exact (h3.pow_left 2).pow_right 3
      have hdvd_mul : 9 ∣ (3 * q + 1) ^ 3 *
          ((2 * (3 * t + 3)).choose (3 * t + 3) ^ 3 + (2 * (3 * t + 4)).choose (3 * t + 4) ^ 3) := by
        rw [show 3 * t + 3 = 3 * q by omega, show 3 * t + 4 = 3 * q + 1 by omega, hmul]
        exact dvd_mul_right 9 _
      exact hcop.dvd_of_dvd_mul_left hdvd_mul

private lemma dvd_p2_a_p_mul_odd {p : ℕ} [Fact p.Prime] (hp : OeisA3625.A p) (t : ℕ) :
    p ^ 2 ∣ OeisA79727.a (p * t + (p - 1) / 2) := by
  by_cases hp3 : p = 3
  · subst hp3
    simpa using dvd_nine_a_three_mul_odd t
  · have hp5 : 5 ≤ p := by
      have h3 := A3625_three_le hp
      have h4 : p ≠ 4 := fun h => by rw [h] at hp; exact (by decide : ¬ Nat.Prime 4) hp.1
      omega
    set m := (p - 1) / 2
    have hp2 : p ≠ 2 := A3625_ne_two hp
    have h2m1 : 2 * m + 1 = p := by
      have := Nat.odd_iff.mp (A3625_odd hp)
      omega
    rw [← ZMod.natCast_eq_zero_iff, OeisA79727.a, Nat.cast_sum]
    -- Reindex range (p * t + m + 1) as blocks q ∈ [0..t-1] × r ∈ [0..p-1], plus q = t × r ∈ [0..m]
    have hsplit : (∑ k ∈ range (p * t + m + 1), (((2 * k).choose k : ℕ) ^ 3 : ZMod (p ^ 2))) =
        (∑ q ∈ range t, ∑ r ∈ range p, (((2 * (p * q + r)).choose (p * q + r) : ℕ) ^ 3 : ZMod (p ^ 2))) +
        (∑ r ∈ range (m + 1), (((2 * (p * t + r)).choose (p * t + r) : ℕ) ^ 3 : ZMod (p ^ 2))) := by
      have h1 : range (p * t + m + 1) =
          range (p * t) ∪ (range (m + 1)).image (fun r => p * t + r) := by
        ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_image]
        constructor
        · intro hk
          by_cases h : k < p * t
          · exact Or.inl h
          · exact Or.inr ⟨k - p * t, by omega, by omega⟩
        · rintro (h | ⟨r, hr, rfl⟩) <;> omega
      have hdisj : Disjoint (range (p * t)) ((range (m + 1)).image (fun r => p * t + r)) := by
        rw [Finset.disjoint_left]
        intro k h1 h2; rw [Finset.mem_range] at h1; rw [Finset.mem_image] at h2
        rcases h2 with ⟨r, _, rfl⟩; omega
      rw [h1, Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ h => by omega)]
      congr 1
      clear h1 hdisj
      induction t with
      | zero => simp
      | succ t ih =>
        rw [Finset.sum_range_succ, ← ih]
        have hpt : p * (t + 1) = p * t + p := by ring
        have h2 : range (p * (t + 1)) = range (p * t) ∪ (range p).image (fun r => p * t + r) := by
          rw [hpt]
          ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_image]
          constructor
          · intro hk
            by_cases h : k < p * t
            · exact Or.inl h
            · exact Or.inr ⟨k - p * t, by omega, by omega⟩
          · rintro (h | ⟨r, hr, rfl⟩) <;> omega
        have hd2 : Disjoint (range (p * t)) ((range p).image (fun r => p * t + r)) := by
          rw [Finset.disjoint_left]
          intro k h1 h2; rw [Finset.mem_range] at h1; rw [Finset.mem_image] at h2
          rcases h2 with ⟨r, _, rfl⟩; omega
        rw [h2, Finset.sum_union hd2, Finset.sum_image (fun a _ b _ h => by omega)]
    simp_rw [Nat.cast_pow]
    rw [hsplit]
    -- Show each half-block sum over r ∈ range (m + 1) vanishes mod p^2 for ANY q!
    have hhalf_zero : ∀ q : ℕ,
        (∑ r ∈ range (m + 1), (((2 * (p * q + r)).choose (p * q + r) : ℕ) ^ 3 : ZMod (p ^ 2))) = 0 := by
      intro q
      have hterm : ∀ r ∈ range (m + 1),
          (((2 * (p * q + r)).choose (p * q + r) : ℕ) ^ 3 : ZMod (p ^ 2)) =
          ((2 * q).choose q : ZMod (p ^ 2)) ^ 3 * (((2 * r).choose r : ℕ) ^ 3 : ZMod (p ^ 2)) +
          6 * (q : ZMod (p ^ 2)) * ((2 * q).choose q : ZMod (p ^ 2)) ^ 3 *
            ((p : ZMod (p ^ 2)) * (((2 * r).choose r : ℕ) ^ 3 : ZMod (p ^ 2)) *
              ((∑ j ∈ range (2 * r), ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹) -
               (∑ j ∈ range r, ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹))) := by
        intro r hr
        rw [Finset.mem_range] at hr
        rw [choose_two_mul_block_cube_mod_p2 p q r (by omega)]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have hS0 : (∑ r ∈ range (m + 1), (((2 * r).choose r : ℕ) ^ 3 : ZMod (p ^ 2))) = 0 := by
        simp_rw [← Nat.cast_pow]
        rw [← Nat.cast_sum]
        exact (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_a_half hp)
      have hSh : (∑ r ∈ range (m + 1),
          (p : ZMod (p ^ 2)) * (((2 * r).choose r : ℕ) ^ 3 : ZMod (p ^ 2)) *
            ((∑ j ∈ range (2 * r), ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹) -
             (∑ j ∈ range r, ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹))) = 0 := by
        have := sum_harmDiff_eq_zero_mod_p hp hp5
        rw [Finset.mul_sum] at this
        convert this using 1
        apply Finset.sum_congr rfl
        intro r _; ring
      rw [hS0, hSh, mul_zero, mul_zero, add_zero]
    rw [hhalf_zero t, add_zero]
    apply Finset.sum_eq_zero
    intro q _
    have hsplit_p : range p = range (m + 1) ∪ Finset.Ico (m + 1) p := by
      ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj_p : Disjoint (range (m + 1)) (Finset.Ico (m + 1) p) := by
      rw [Finset.disjoint_left]; intro k h1 h2; rw [Finset.mem_range] at h1; rw [Finset.mem_Ico] at h2; omega
    rw [hsplit_p, Finset.sum_union hdisj_p, hhalf_zero q, zero_add]
    apply Finset.sum_eq_zero
    intro r hr
    rw [Finset.mem_Ico] at hr
    have hd := choose_two_mul_dvd_p_of_gt_half p hp2 q r (by omega) hr.2
    have hd2 : p ^ 2 ∣ ((2 * (p * q + r)).choose (p * q + r)) ^ 3 :=
      dvd_trans (pow_dvd_pow p (by decide : 2 ≤ 3)) (pow_dvd_pow_of_dvd hd 3)
    rw [← Nat.cast_pow]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hd2

end OeisA79727Conjecture4

theorem OMA.solution : type_of% @OeisA79727.conjecture4 := by
  intro S hS
  set N := ∏ q ∈ S, q
  have hN_odd : Odd N := by
    refine Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one ?_
    intro q hq
    exact OeisA79727Conjecture4.A3625_odd (hS q hq)
  have h_each : ∀ p ∈ S, p ^ 2 ∣ OeisA79727.a ((N - 1) / 2) := by
    intro p hp
    have : Fact p.Prime := ⟨(hS p hp).1⟩
    have hp_dvd_N : p ∣ N := Finset.dvd_prod_of_mem _ hp
    rcases hp_dvd_N with ⟨K, hK⟩
    have hK_odd : Odd K := by
      rw [hK] at hN_odd
      exact (Nat.odd_mul.mp hN_odd).2
    rcases hK_odd with ⟨t, rfl⟩
    have hN_eq : N = 2 * (p * t) + p := by rw [hK]; ring
    have hidx : (N - 1) / 2 = p * t + (p - 1) / 2 := by
      have hp_odd : p % 2 = 1 := Nat.odd_iff.mp (OeisA79727Conjecture4.A3625_odd (hS p hp))
      have hp_pos := (hS p hp).1.pos
      omega
    rw [hidx]
    exact OeisA79727Conjecture4.dvd_p2_a_p_mul_odd (hS p hp) t
  -- Combine pairwise coprime prime-square divisors over S by Finset induction
  rw [← Finset.prod_pow]
  have hcombine : ∀ (T : Finset ℕ), (∀ p ∈ T, p.Prime) →
      (∀ p ∈ T, p ^ 2 ∣ OeisA79727.a ((N - 1) / 2)) →
      (∏ p ∈ T, p ^ 2) ∣ OeisA79727.a ((N - 1) / 2) := by
    intro T
    induction T using Finset.cons_induction with
    | empty => intro _ _; simp
    | cons a T ha ih =>
      intro hTp hTd
      rw [Finset.prod_cons]
      have ha_prime : a.Prime := hTp a (Finset.mem_cons_self a T)
      have ha_dvd : a ^ 2 ∣ OeisA79727.a ((N - 1) / 2) := hTd a (Finset.mem_cons_self a T)
      have hT_dvd : (∏ p ∈ T, p ^ 2) ∣ OeisA79727.a ((N - 1) / 2) :=
        ih (fun p hp => hTp p (Finset.mem_cons_of_mem hp))
          (fun p hp => hTd p (Finset.mem_cons_of_mem hp))
      have hcop : Nat.Coprime (a ^ 2) (∏ p ∈ T, p ^ 2) := by
        refine Nat.Coprime.prod_right fun p hp => ?_
        have hp_prime : p.Prime := hTp p (Finset.mem_cons_of_mem hp)
        have hne : a ≠ p := fun h => ha (h ▸ hp)
        exact ((Nat.coprime_primes ha_prime hp_prime).mpr hne).pow 2 2
      exact hcop.mul_dvd_of_dvd_of_dvd ha_dvd hT_dvd
  exact hcombine S (fun p hp => (hS p hp).1) h_each
