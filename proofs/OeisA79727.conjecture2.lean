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
# Proof of Peter Bala's Conjecture 2 for OEIS A079727

For every prime `p` with `p % 7 ∈ {3, 5, 6}` (OEIS A003625),
`a (p * (p - 1)) ≡ p ^ 2 [MOD p ^ 3]`, where `a n = ∑ k ≤ n, C(2k, k)^3`.
-/

open scoped BigOperators
open Polynomial Finset Nat

namespace OeisA79727Conjecture2

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

/- ### Section 6: Wronskian mod `p^2` and `aeval x0 (shiftedLegendre m2) = (-1)^m * p` -/

private lemma aeval_int_eq_eval_map {R : Type*} [CommRing R] (x : R) (f : ℤ[X]) :
    aeval x f = (Polynomial.map (Int.castRingHom R) f).eval x := by
  rw [aeval_def, eval_map]
  rfl

private def ZOmega.norm {R : Type*} [CommRing R] (z : ZOmega R) : R :=
  z.re ^ 2 + z.re * z.im + 2 * z.im ^ 2

private lemma ZOmega.mul_conj_eq_norm {R : Type*} [CommRing R] (z : ZOmega R) :
    z * ⟨z.re + z.im, -z.im⟩ = ZOmega.of (ZOmega.norm z) := by
  apply ZOmega.ext <;>
    simp only [ZOmega.mul_re, ZOmega.mul_im, ZOmega.of_re, ZOmega.of_im, ZOmega.norm] <;> ring

private lemma ZOmega.norm_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (z : ZOmega R) :
    ZOmega.norm (ZOmega.mapRingHom f z) = f (ZOmega.norm z) := by
  change f z.re ^ 2 + f z.re * f z.im + 2 * f z.im ^ 2 = f (z.re ^ 2 + z.re * z.im + 2 * z.im ^ 2)
  simp only [map_add, map_mul, map_pow, map_ofNat]

private lemma ZOmega.norm_ne_zero_of_ne_zero {p : ℕ} [Fact p.Prime] (hp : OeisA3625.A p)
    {z : ZOmega (ZMod p)} (hz : z ≠ 0) : ZOmega.norm z ≠ 0 := by
  intro hnorm
  have hp2 : p ≠ 2 := A3625_ne_two hp
  have hp7 : p ≠ 7 := A3625_ne_seven hp
  have h2m : 2 * ((p - 1) / 2) = p - 1 := by
    have := Nat.odd_iff.mp (A3625_odd hp)
    omega
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h2
    have h2d : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h2)
    have := Nat.le_of_dvd (by decide) h2d
    have := A3625_three_le hp
    omega
  have h7ne : (7 : ZMod p) ≠ 0 := by
    intro h7
    have h7d : p ∣ 7 := (ZMod.natCast_eq_zero_iff 7 p).mp (by simpa using h7)
    have hle := Nat.le_of_dvd (by decide) h7d
    have hp_pr := hp.1
    interval_cases p <;> simp_all [OeisA3625.A]
  have hsq : (2 * z.re + z.im) ^ 2 = (-7 : ZMod p) * z.im ^ 2 := by
    have : 4 * (z.re ^ 2 + z.re * z.im + 2 * z.im ^ 2) = 0 := by
      rw [show z.re ^ 2 + z.re * z.im + 2 * z.im ^ 2 = ZOmega.norm z from rfl, hnorm, mul_zero]
    linear_combination this
  by_cases him : z.im = 0
  · rw [him] at hsq
    simp only [add_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at hsq
    have h2re : 2 * z.re = 0 := mul_self_eq_zero.mp (by rwa [← pow_two])
    have hre : z.re = 0 := (mul_eq_zero.mp h2re).resolve_left h2ne
    exact hz (ZOmega.ext hre him)
  · set t : ZMod p := (2 * z.re + z.im) * z.im⁻¹
    have ht2 : t ^ 2 = -7 := by
      have hmul : t ^ 2 * z.im ^ 2 = (-7 : ZMod p) * z.im ^ 2 := by
        calc t ^ 2 * z.im ^ 2 = (2 * z.re + z.im) ^ 2 * (z.im⁻¹ * z.im) ^ 2 := by ring
          _ = (2 * z.re + z.im) ^ 2 := by rw [inv_mul_cancel₀ him, one_pow, mul_one]
          _ = (-7 : ZMod p) * z.im ^ 2 := hsq
      exact mul_right_cancel₀ (pow_ne_zero 2 him) hmul
    have htne : t ≠ 0 := by
      intro ht0
      rw [ht0, zero_pow (by decide : 2 ≠ 0)] at ht2
      exact h7ne (by linear_combination ht2)
    have hpow1 : (-7 : ZMod p) ^ ((p - 1) / 2) = 1 := by
      rw [← ht2, ← pow_mul, h2m]
      exact ZMod.pow_card_sub_one_eq_one htne
    have hpow_neg1 : (-7 : ZMod p) ^ ((p - 1) / 2) = -1 := neg_seven_pow_half hp
    have h1eq : (1 : ZMod p) = -1 := hpow1.symm.trans hpow_neg1
    exact h2ne (by linear_combination h1eq)

private lemma ZOmega.isUnit_mod_p2_of_ne_zero_mod_p {p : ℕ} [Fact p.Prime] (hp : OeisA3625.A p)
    {z : ZOmega (ZMod (p ^ 2))}
    (hz : ZOmega.mapRingHom (ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)) z ≠ 0) :
    IsUnit z := by
  set n : ZMod (p ^ 2) := ZOmega.norm z
  have hn_mod : ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p) n ≠ 0 := by
    rw [← ZOmega.norm_map]
    exact ZOmega.norm_ne_zero_of_ne_zero hp hz
  have hndvd : ¬ p ∣ n.val := by
    intro hd
    apply hn_mod
    have h1 : (n.val : ZMod (p ^ 2)) = n := ZMod.natCast_zmod_val n
    rw [← h1, map_natCast, ZMod.natCast_eq_zero_iff]
    exact hd
  have hcop : Nat.Coprime n.val (p ^ 2) :=
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hndvd).symm.pow_right 2
  have hn_unit : IsUnit n := by
    have hu := (ZMod.isUnit_iff_coprime n.val (p ^ 2)).mpr hcop
    rwa [ZMod.natCast_zmod_val] at hu
  rcases hn_unit with ⟨u, hu⟩
  refine IsUnit.of_mul_eq_one (⟨z.re + z.im, -z.im⟩ * ZOmega.of (↑(u⁻¹) : ZMod (p ^ 2))) ?_
  rw [← mul_assoc, ZOmega.mul_conj_eq_norm]
  change ZOmega.of n * ZOmega.of (↑(u⁻¹) : ZMod (p ^ 2)) = 1
  rw [← map_mul, ← hu, Units.mul_inv, map_one]

private lemma ZOmega.add_pow_p {p : ℕ} [Fact p.Prime] (x y : ZOmega (ZMod p)) :
    (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow]
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hsplit : ∑ k ∈ range (p + 1), x ^ k * y ^ (p - k) * (p.choose k : ZOmega (ZMod p)) =
      y ^ p + x ^ p +
      ∑ k ∈ Finset.Ioo 0 p, x ^ k * y ^ (p - k) * (p.choose k : ZOmega (ZMod p)) := by
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one]
    have hrange : range p = insert 0 (Finset.Ioo 0 p) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
      omega
    rw [hrange, Finset.sum_insert (by simp), pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right,
      Nat.cast_one, mul_one]
    ring
  rw [hsplit]
  have hmid : ∑ k ∈ Finset.Ioo 0 p, x ^ k * y ^ (p - k) * (p.choose k : ZOmega (ZMod p)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ioo] at hk
    have hd : p ∣ p.choose k := prime_dvd_choose_self (Fact.out : p.Prime) hk.1 hk.2
    have h0 : (p.choose k : ZOmega (ZMod p)) = 0 := by
      rw [show (p.choose k : ZOmega (ZMod p)) = ZOmega.of ((p.choose k : ℕ) : ZMod p) by simp]
      rw [(ZMod.natCast_eq_zero_iff _ _).mpr hd, map_zero]
    rw [h0, mul_zero]
  rw [hmid, add_zero, add_comm]

private lemma ZOmega.x0_pow_p_eq_one_sub {p : ℕ} [Fact p.Prime] (hp : OeisA3625.A p) :
    (ZOmega.x0 : ZOmega (ZMod p)) ^ p = 1 - ZOmega.x0 := by
  set m := (p - 1) / 2
  have hp_odd : Odd p := A3625_odd hp
  have h2m1 : 2 * m + 1 = p := by
    have := Nat.odd_iff.mp hp_odd
    omega
  have hof_pow : ∀ a : ZMod p, (ZOmega.of a) ^ p = ZOmega.of a := by
    intro a
    rw [← map_pow, ZMod.pow_card]
  have hneg1_pow : (-1 : ZOmega (ZMod p)) ^ p = -1 := hp_odd.neg_one_pow
  -- Compute (2 * omega - 1) ^ p in two ways
  have hway1 : (2 * (ZOmega.omega : ZOmega (ZMod p)) - 1) ^ p =
      -(2 * (ZOmega.omega : ZOmega (ZMod p)) - 1) := by
    have hpow_split : (2 * (ZOmega.omega : ZOmega (ZMod p)) - 1) ^ p =
        ((2 * (ZOmega.omega : ZOmega (ZMod p)) - 1) ^ 2) ^ m * (2 * ZOmega.omega - 1) := by
      rw [← pow_mul, ← pow_succ, h2m1]
    rw [hpow_split, ZOmega.two_omega_sub_one_sq]
    have h7 : (-7 : ZOmega (ZMod p)) ^ m = -1 := by
      have h7of : (-7 : ZOmega (ZMod p)) = ZOmega.of (-7 : ZMod p) := by
        rw [map_neg, map_ofNat]
      rw [h7of, ← map_pow, neg_seven_pow_half hp, map_neg, map_one]
    rw [h7]; ring
  have hway2 : (2 * (ZOmega.omega : ZOmega (ZMod p)) - 1) ^ p =
      2 * (ZOmega.omega : ZOmega (ZMod p)) ^ p - 1 := by
    rw [sub_eq_add_neg, ZOmega.add_pow_p, mul_pow, hneg1_pow]
    have h2p : (2 : ZOmega (ZMod p)) ^ p = 2 := by
      have h2of : (2 : ZOmega (ZMod p)) = ZOmega.of (2 : ZMod p) := (map_ofNat ZOmega.of 2).symm
      rw [h2of, hof_pow]
    rw [h2p]; ring
  have h2om : (2 : ZOmega (ZMod p)) * ((ZOmega.omega : ZOmega (ZMod p)) ^ p - (1 - ZOmega.omega)) = 0 := by
    linear_combination hway2.symm.trans hway1
  have h2unit : IsUnit (2 : ZOmega (ZMod p)) := by
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h2
      have h2d : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h2)
      have := Nat.le_of_dvd (by decide) h2d
      have := A3625_three_le hp
      omega
    refine IsUnit.of_mul_eq_one (ZOmega.of (2 : ZMod p)⁻¹) ?_
    have h2of : (2 : ZOmega (ZMod p)) = ZOmega.of (2 : ZMod p) := (map_ofNat ZOmega.of 2).symm
    rw [h2of, ← map_mul, mul_inv_cancel₀ h2ne, map_one]
  have hom_pow : (ZOmega.omega : ZOmega (ZMod p)) ^ p = 1 - ZOmega.omega := by
    have := (h2unit.mul_right_eq_zero).mp h2om
    linear_combination this
  have hx0_eq : (ZOmega.x0 : ZOmega (ZMod p)) = 2 + (-3) * ZOmega.omega := by
    apply ZOmega.ext <;> simp [ZOmega.x0, ZOmega.omega]
  rw [hx0_eq, ZOmega.add_pow_p, mul_pow, hom_pow]
  have h2p : (2 : ZOmega (ZMod p)) ^ p = 2 := by
    have h2of : (2 : ZOmega (ZMod p)) = ZOmega.of (2 : ZMod p) := (map_ofNat ZOmega.of 2).symm
    rw [h2of, hof_pow]
  have h3p : (-3 : ZOmega (ZMod p)) ^ p = -3 := by
    have h3of : (-3 : ZOmega (ZMod p)) = ZOmega.of (-3 : ZMod p) := by rw [map_neg, map_ofNat]
    rw [h3of, hof_pow]
  rw [h2p, h3p]
  ring

private lemma shiftedLegendre_deriv_comp_one_sub (n : ℕ) :
    (X * (1 - X) * derivative (shiftedLegendre n)).comp (1 - X) =
      -((-1 : ℤ[X]) ^ n) * (X * (1 - X) * derivative (shiftedLegendre n)) := by
  have h1 : (-1 : ℤ[X]) ^ n * (shiftedLegendre n).comp (1 - X) = shiftedLegendre n :=
    neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq n
  have hd := congr_arg derivative h1
  have hd_const : derivative ((-1 : ℤ[X]) ^ n) = 0 := by
    rw [show (-1 : ℤ[X]) ^ n = C ((-1 : ℤ) ^ n) by simp, derivative_C]
  rw [derivative_mul, hd_const, zero_mul, zero_add, derivative_comp] at hd
  have hd_sub : derivative (1 - X : ℤ[X]) = -1 := by
    simp only [derivative_sub, derivative_one, derivative_X, zero_sub]
  rw [hd_sub] at hd
  -- hd : (-1)^n * ((derivative (shiftedLegendre n)).comp (1 - X) * (-1)) = derivative (shiftedLegendre n)
  have hcomp_deriv : (derivative (shiftedLegendre n)).comp (1 - X) =
      -((-1 : ℤ[X]) ^ n) * derivative (shiftedLegendre n) := by
    have hmul := congr_arg (fun q => -((-1 : ℤ[X]) ^ n) * q) hd
    have hsq : (-1 : ℤ[X]) ^ n * (-1 : ℤ[X]) ^ n = 1 := by
      rw [← mul_pow]; norm_num
    calc (derivative (shiftedLegendre n)).comp (1 - X)
        = ((-1 : ℤ[X]) ^ n * (-1 : ℤ[X]) ^ n) * (derivative (shiftedLegendre n)).comp (1 - X) := by
          rw [hsq, one_mul]
      _ = -((-1 : ℤ[X]) ^ n) * ((-1 : ℤ[X]) ^ n * (-1 * (derivative (shiftedLegendre n)).comp (1 - X))) := by
          ring
      _ = -((-1 : ℤ[X]) ^ n) * derivative (shiftedLegendre n) := by
          linear_combination hmul
  simp only [mul_comp, sub_comp, one_comp, X_comp, hcomp_deriv]
  ring

private lemma shiftedLegendre_deriv_x0_ne_zero {p : ℕ} [Fact p.Prime] (hp : OeisA3625.A p) :
    aeval (ZOmega.x0 : ZOmega (ZMod p)) (derivative (shiftedLegendre ((p - 1) / 2))) ≠ 0 := by
  set m := (p - 1) / 2
  set x0 : ZOmega (ZMod p) := ZOmega.x0
  set f : (ZOmega (ZMod p))[X] := Polynomial.map (Int.castRingHom (ZOmega (ZMod p))) (shiftedLegendre m)
  have hp_pr : p.Prime := Fact.out
  have hp3 : 3 ≤ p := A3625_three_le hp
  have hp2 : p ≠ 2 := A3625_ne_two hp
  have h2m : 2 * m = p - 1 := by
    have := Nat.odd_iff.mp (A3625_odd hp)
    omega
  intro hd0
  have hf0 : f.eval x0 = 0 := by
    rw [← aeval_int_eq_eval_map]
    exact shiftedLegendre_eval_x0_eq_zero hp
  have hfd0 : (derivative f).eval x0 = 0 := by
    rw [show derivative f = Polynomial.map (Int.castRingHom (ZOmega (ZMod p))) (derivative (shiftedLegendre m)) by
      simp only [f, derivative_map]]
    rw [← aeval_int_eq_eval_map]
    exact hd0
  have hode : (X ^ 2 - X) * derivative (derivative f) + (2 * X - 1) * derivative f -
      C ((m * (m + 1) : ℕ) : ZOmega (ZMod p)) * f = 0 := by
    have h0 := congr_arg (Polynomial.map (Int.castRingHom (ZOmega (ZMod p)))) (shiftedLegendre_ode m)
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_one, Polynomial.map_ofNat,
      Polynomial.map_zero, ← derivative_map] at h0
    rw [Polynomial.map_C, map_natCast] at h0
    exact h0
  set L1 : (ZOmega (ZMod p))[X] := X - C x0
  have hL1_monic : L1.Monic := monic_X_sub_C x0
  have hdL1 : derivative L1 = 1 := by
    simp only [L1, derivative_sub, derivative_X, derivative_C, sub_zero]
  have hunit_of_nat : ∀ k : ℕ, 0 < k → k < p → IsUnit (k : ZOmega (ZMod p)) := by
    intro k hk0 hkp
    have hkne : (k : ZMod p) ≠ 0 := by
      intro h0
      have hd : p ∣ k := (ZMod.natCast_eq_zero_iff k p).mp h0
      have := Nat.le_of_dvd hk0 hd
      omega
    refine IsUnit.of_mul_eq_one (ZOmega.of (k : ZMod p)⁻¹) ?_
    have : (k : ZOmega (ZMod p)) = ZOmega.of (k : ZMod p) := by simp
    rw [this, ← map_mul, mul_inv_cancel₀ hkne, map_one]
  have h16_unit : IsUnit (x0 ^ 2 - x0) := by
    rw [show x0 ^ 2 - x0 = -16 from ZOmega.neg_x0_mul_one_sub]
    have h2u := hunit_of_nat 2 (by decide) (by omega)
    have h16eq : (-16 : ZOmega (ZMod p)) = (-1) * (2 : ZOmega (ZMod p)) ^ 4 := by ring
    rw [h16eq]
    exact (IsUnit.of_mul_eq_one (-1 : ZOmega (ZMod p)) (by ring)).mul (h2u.pow 4)
  -- Show by induction that L1 ^ k ∣ f for all k ≤ m + 1
  have hdvd : ∀ k : ℕ, k ≤ m + 1 → L1 ^ k ∣ f := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rcases k with _ | _ | k
      · -- k = 0, goal: L1 ^ 1 ∣ f
        simpa [pow_one, L1] using dvd_iff_isRoot.mpr hf0
      · -- k = 1, goal: L1 ^ 2 ∣ f
        rcases ih (by omega) with ⟨Q, hQ⟩
        rw [pow_one] at hQ
        have hQd := congr_arg derivative hQ
        rw [derivative_mul, hdL1, one_mul] at hQd
        have hQ0 : Q.eval x0 = 0 := by
          have := congr_arg (eval x0) hQd
          simp only [hfd0, eval_add, eval_mul, L1, eval_sub, eval_X, eval_C, sub_self,
            zero_mul, add_zero] at this
          exact this.symm
        rcases dvd_iff_isRoot.mpr hQ0 with ⟨R, hR⟩
        exact ⟨R, by rw [hQ, hR]; ring⟩
      · -- k + 2 ≥ 2, goal: L1 ^ (k + 3) ∣ f
        rcases ih (by omega) with ⟨Q, hQ⟩
        set n := k + 2
        have hn_le : n ≤ m := by omega
        have hd1 : derivative f =
            C (n : ZOmega (ZMod p)) * L1 ^ (k + 1) * Q + L1 ^ (k + 2) * derivative Q := by
          rw [hQ, derivative_mul, derivative_pow, hdL1, mul_one]
          have : (k + 2 : ℕ) - 1 = k + 1 := rfl
          rw [this]
        have hd2 : derivative (derivative f) =
            C ((n * (k + 1) : ℕ) : ZOmega (ZMod p)) * L1 ^ k * Q +
            C ((2 * n : ℕ) : ZOmega (ZMod p)) * L1 ^ (k + 1) * derivative Q +
            L1 ^ (k + 2) * derivative (derivative Q) := by
          rw [hd1, derivative_add, derivative_mul, derivative_mul, derivative_mul,
            derivative_C, zero_mul, zero_add, derivative_pow, derivative_pow, hdL1, mul_one, mul_one]
          have h1 : (k + 1 : ℕ) - 1 = k := rfl
          have h2 : (k + 2 : ℕ) - 1 = k + 1 := rfl
          rw [h1, h2]
          simp only [n, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, map_mul, map_add, map_ofNat]
          ring
        have hfact : L1 ^ k *
            ((X ^ 2 - X) * C ((n * (k + 1) : ℕ) : ZOmega (ZMod p)) * Q +
             L1 * ((X ^ 2 - X) * C ((2 * n : ℕ) : ZOmega (ZMod p)) * derivative Q +
                   (X ^ 2 - X) * L1 * derivative (derivative Q) +
                   (2 * X - 1) * C (n : ZOmega (ZMod p)) * Q +
                   (2 * X - 1) * L1 * derivative Q -
                   C ((m * (m + 1) : ℕ) : ZOmega (ZMod p)) * L1 * Q)) = 0 := by
          rw [← hode, hd2, hd1, hQ]
          ring
        have hrem0 : (X ^ 2 - X) * C ((n * (k + 1) : ℕ) : ZOmega (ZMod p)) * Q +
             L1 * ((X ^ 2 - X) * C ((2 * n : ℕ) : ZOmega (ZMod p)) * derivative Q +
                   (X ^ 2 - X) * L1 * derivative (derivative Q) +
                   (2 * X - 1) * C (n : ZOmega (ZMod p)) * Q +
                   (2 * X - 1) * L1 * derivative Q -
                   C ((m * (m + 1) : ℕ) : ZOmega (ZMod p)) * L1 * Q) = 0 := by
          set rem := (X ^ 2 - X) * C ((n * (k + 1) : ℕ) : ZOmega (ZMod p)) * Q +
             L1 * ((X ^ 2 - X) * C ((2 * n : ℕ) : ZOmega (ZMod p)) * derivative Q +
                   (X ^ 2 - X) * L1 * derivative (derivative Q) +
                   (2 * X - 1) * C (n : ZOmega (ZMod p)) * Q +
                   (2 * X - 1) * L1 * derivative Q -
                   C ((m * (m + 1) : ℕ) : ZOmega (ZMod p)) * L1 * Q)
          by_contra hne
          have hm : (L1 ^ k).Monic := hL1_monic.pow k
          have hlc : (L1 ^ k).leadingCoeff * rem.leadingCoeff ≠ 0 := by
            rw [hm.leadingCoeff, one_mul]
            exact leadingCoeff_ne_zero.mpr hne
          have := leadingCoeff_mul' hlc
          rw [show L1 ^ k * rem = 0 from hfact, leadingCoeff_zero] at this
          exact hlc this.symm
        have heval := congr_arg (eval x0) hrem0
        simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_C, eval_zero,
          L1, sub_self, zero_mul, add_zero] at heval
        have hnu : IsUnit ((n * (k + 1) : ℕ) : ZOmega (ZMod p)) := by
          rw [Nat.cast_mul]
          exact (hunit_of_nat n (by omega) (by omega)).mul (hunit_of_nat (k + 1) (by omega) (by omega))
        have hQ0 : Q.eval x0 = 0 := (h16_unit.mul hnu).mul_right_eq_zero.mp heval
        rcases dvd_iff_isRoot.mpr hQ0 with ⟨R, hR⟩
        exact ⟨R, by rw [hQ, hR]; ring⟩
  rcases hdvd (m + 1) (le_refl _) with ⟨Q, hQ⟩
  have hf_ne : f ≠ 0 := by
    intro hf_z
    have hc0 : f.coeff 0 = 0 := by rw [hf_z, coeff_zero]
    simp only [f, coeff_map, coeff_shiftedLegendre] at hc0
    simp only [add_zero, Nat.choose_zero_right, Nat.choose_self, pow_zero, mul_one,
      Nat.cast_one, Int.cast_one, eq_intCast] at hc0
    have h10 : (1 : ZMod p) = 0 := by
      have := congr_arg ZOmega.re hc0
      simp at this
    exact (one_ne_zero : (1 : ZMod p) ≠ 0) h10
  have hQ_ne : Q ≠ 0 := by
    intro hQz
    rw [hQz, mul_zero] at hQ
    exact hf_ne hQ
  have : Nontrivial (ZOmega (ZMod p)) :=
    ⟨⟨1, 0, fun h => (one_ne_zero : (1 : ZMod p) ≠ 0) (by simpa using congr_arg ZOmega.re h)⟩⟩
  have hdeg_ge : m + 1 ≤ f.natDegree := by
    have hm : (L1 ^ (m + 1)).Monic := hL1_monic.pow (m + 1)
    have hlc : (L1 ^ (m + 1)).leadingCoeff * Q.leadingCoeff ≠ 0 := by
      rw [hm.leadingCoeff, one_mul]
      exact leadingCoeff_ne_zero.mpr hQ_ne
    rw [hQ, natDegree_mul' hlc, hL1_monic.natDegree_pow, natDegree_X_sub_C]
    omega
  have hdeg_le : f.natDegree ≤ m := by
    exact le_trans natDegree_map_le (by rw [natDegree_shiftedLegendre])
  omega

private lemma poly_comp_X_pow_p_eq_pow_p {p : ℕ} [Fact p.Prime] (f : (ZMod p)[X]) :
    f.comp (X ^ p) = f ^ p := by
  induction f using Polynomial.induction_on' with
  | add g h ihg ihh =>
    rw [add_comp, ihg, ihh, add_pow_char]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp, mul_pow, ← C_pow,
      ZMod.pow_card, ← pow_mul, ← pow_mul, mul_comm p n]

private lemma coeff_comp_X_pow {R : Type*} [CommRing R] {p : ℕ} (hp : 0 < p) (f : R[X]) (k : ℕ) :
    (f.comp (X ^ p)).coeff (p * k) = f.coeff k := by
  induction f using Polynomial.induction_on' with
  | add g h ihg ihh =>
    rw [add_comp, coeff_add, coeff_add, ihg, ihh]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp, ← pow_mul,
      coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    by_cases hnk : k = n
    · subst hnk; simp
    · have hne : p * k ≠ p * n := fun h => hnk (Nat.eq_of_mul_eq_mul_left hp h)
      simp [hnk, hne]

private lemma coeff_comp_X_pow_of_not_dvd {R : Type*} [CommRing R] {p : ℕ} (f : R[X])
    {k : ℕ} (hd : ¬ p ∣ k) : (f.comp (X ^ p)).coeff k = 0 := by
  induction f using Polynomial.induction_on' with
  | add g h ihg ihh =>
    rw [add_comp, coeff_add, ihg, ihh, add_zero]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp, ← pow_mul,
      coeff_C_mul_X_pow, if_neg]
    intro heq
    exact hd ⟨n, heq⟩

private lemma coeff_comp_X_pow_mul_of_deg_lt {R : Type*} [CommRing R] {p : ℕ} (hp : 0 < p)
    (A B : R[X]) (hB : ∀ j, p ≤ j → B.coeff j = 0) (q r : ℕ) (hr : r < p) :
    (A.comp (X ^ p) * B).coeff (p * q + r) = A.coeff q * B.coeff r := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hterm : ∀ i ∈ range (p * q + r + 1),
      (A.comp (X ^ p)).coeff i * B.coeff (p * q + r - i) =
      if i = p * q then A.coeff q * B.coeff r else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases heq : i = p * q
    · subst heq
      rw [if_pos rfl, Nat.add_sub_cancel_left, coeff_comp_X_pow hp]
    · rw [if_neg heq]
      by_cases hd : p ∣ i
      · rcases hd with ⟨t, rfl⟩
        have hlt : t < q := by
          have : t ≠ q := fun h => heq (by rw [h])
          by_contra hge
          have hge' : q + 1 ≤ t := by omega
          have : p * (q + 1) ≤ p * t := Nat.mul_le_mul_left p hge'
          have : p * q + p ≤ p * t := by linarith
          omega
        have hbig : p ≤ p * q + r - p * t := by
          have : p * (t + 1) ≤ p * q := Nat.mul_le_mul_left p (by omega)
          have : p * t + p ≤ p * q := by linarith
          omega
        rw [hB _ hbig, mul_zero]
      · rw [coeff_comp_X_pow_of_not_dvd A hd, zero_mul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]

private lemma shiftedLegendre_m2_mod_p {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Polynomial.map (Int.castRingHom (ZMod p)) (shiftedLegendre ((p ^ 2 - 1) / 2)) =
      (Polynomial.map (Int.castRingHom (ZMod p)) (shiftedLegendre ((p - 1) / 2))).comp (X ^ p) *
      Polynomial.map (Int.castRingHom (ZMod p)) (shiftedLegendre ((p - 1) / 2)) := by
  set m := (p - 1) / 2
  set m2 := (p ^ 2 - 1) / 2
  have hp_pr : p.Prime := Fact.out
  have hp_odd : Odd p := hp_pr.odd_of_ne_two hp2
  have hp_pos : 0 < p := hp_pr.pos
  have h2m1 : 2 * m + 1 = p := by
    have := Nat.odd_iff.mp hp_odd
    omega
  have hm2_eq : m2 = p * m + m := by
    have h2m2 : 2 * (p * m + m) + 1 = p ^ 2 := by nlinarith
    have hsq : 1 ≤ p ^ 2 := by nlinarith
    omega
  have hm_lt : m < p := by omega
  set Lm_p : (ZMod p)[X] := Polynomial.map (Int.castRingHom (ZMod p)) (shiftedLegendre m)
  have hB : ∀ j, p ≤ j → Lm_p.coeff j = 0 := by
    intro j hj
    rw [coeff_map, coeff_shiftedLegendre]
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  ext k
  set q := k / p
  set r := k % p
  have hk_eq : k = p * q + r := (Nat.div_add_mod k p).symm
  have hr_lt : r < p := Nat.mod_lt k hp_pos
  rw [hk_eq, coeff_comp_X_pow_mul_of_deg_lt hp_pos Lm_p Lm_p hB q r hr_lt]
  simp only [Lm_p, coeff_map, coeff_shiftedLegendre, eq_intCast, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast]
  have hluc1 : ((m2.choose (p * q + r) : ℕ) : ZMod p) =
      ((m.choose r : ℕ) : ZMod p) * ((m.choose q : ℕ) : ZMod p) := by
    have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := m2) (k := p * q + r)
    have hmod_m2 : m2 % p = m := by rw [hm2_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt hm_lt]
    have hdiv_m2 : m2 / p = m := by rw [hm2_eq, Nat.mul_add_div hp_pos, Nat.div_eq_of_lt hm_lt, add_zero]
    have hmod_k : (p * q + r) % p = r := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr_lt]
    have hdiv_k : (p * q + r) / p = q := by rw [Nat.mul_add_div hp_pos, Nat.div_eq_of_lt hr_lt, add_zero]
    rw [hmod_m2, hdiv_m2, hmod_k, hdiv_k] at hl
    exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ p).mpr hl
  by_cases hrm : r ≤ m
  · have hmr_lt : m + r < p := by omega
    have hluc2 : (((m2 + (p * q + r)).choose m2 : ℕ) : ZMod p) =
        (((m + r).choose m : ℕ) : ZMod p) * (((m + q).choose m : ℕ) : ZMod p) := by
      have hsum : m2 + (p * q + r) = p * (m + q) + (m + r) := by rw [hm2_eq]; ring
      have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat
        (p := p) (n := m2 + (p * q + r)) (k := m2)
      have hmod1 : (m2 + (p * q + r)) % p = m + r := by
        rw [hsum, Nat.mul_add_mod, Nat.mod_eq_of_lt hmr_lt]
      have hdiv1 : (m2 + (p * q + r)) / p = m + q := by
        rw [hsum, Nat.mul_add_div hp_pos, Nat.div_eq_of_lt hmr_lt, add_zero]
      have hmod2 : m2 % p = m := by rw [hm2_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt hm_lt]
      have hdiv2 : m2 / p = m := by rw [hm2_eq, Nat.mul_add_div hp_pos, Nat.div_eq_of_lt hm_lt, add_zero]
      rw [hmod1, hdiv1, hmod2, hdiv2] at hl
      exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ p).mpr hl
    have hsign : (-1 : ZMod p) ^ (p * q + r) = (-1 : ZMod p) ^ q * (-1 : ZMod p) ^ r := by
      rw [pow_add, pow_mul, hp_odd.neg_one_pow]
    rw [hluc1, hluc2, hsign]
    ring
  · have hzero : m.choose r = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hluc1, hzero, Nat.cast_zero, zero_mul]
    ring

private lemma wronskian_mod_p2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    let m := (p - 1) / 2
    let m2 := (p ^ 2 - 1) / 2
    let Lm := shiftedLegendre m
    let Lm2 := shiftedLegendre m2
    let H := X * (1 - X) * (Lm * derivative Lm2 - derivative Lm * Lm2)
    let g := X * (1 - X) * derivative Lm
    Polynomial.map (Int.castRingHom (ZMod (p ^ 2))) H =
      C (p : ZMod (p ^ 2)) * (Polynomial.map (Int.castRingHom (ZMod (p ^ 2))) g).comp (X ^ p) := by
  intro m m2 Lm Lm2 H g
  have hp_pr : p.Prime := Fact.out
  have hp_pos : 0 < p := hp_pr.pos
  have hp3 : 3 ≤ p := by have := hp_pr.two_le; omega
  have hp_odd : Odd p := hp_pr.odd_of_ne_two hp2
  have h2m1 : 2 * m + 1 = p := by
    have := Nat.odd_iff.mp hp_odd
    omega
  have h2m2 : 2 * m2 + 1 = p ^ 2 := by
    have hsq : 1 ≤ p ^ 2 := by nlinarith
    have h2 : 2 * (p * m + m) + 1 = p ^ 2 := by nlinarith
    omega
  have hm2_diff : m2 * (m2 + 1) - m * (m + 1) = p ^ 2 * (m * (m + 1)) := by
    have h1 : 4 * (m * (m + 1)) + 1 = p ^ 2 := by nlinarith
    have h2 : 4 * (m2 * (m2 + 1)) + 1 = p ^ 4 := by nlinarith
    exact Nat.sub_eq_of_eq_add (by nlinarith)
  have hdH : derivative H = -C ((p ^ 2 * (m * (m + 1)) : ℕ) : ℤ) * (Lm * Lm2) := by
    have hode1 := shiftedLegendre_ode m
    have hode2 := shiftedLegendre_ode m2
    have hcalc : derivative H =
        -(Lm * ((X ^ 2 - X) * derivative (derivative Lm2) + (2 * X - 1) * derivative Lm2) -
          Lm2 * ((X ^ 2 - X) * derivative (derivative Lm) + (2 * X - 1) * derivative Lm)) := by
      simp only [H, derivative_mul, derivative_sub, derivative_one, derivative_X]
      ring
    rw [hcalc]
    have h1 : (X ^ 2 - X) * derivative (derivative Lm) + (2 * X - 1) * derivative Lm =
        C ((m * (m + 1) : ℕ) : ℤ) * Lm := by linear_combination hode1
    have h2 : (X ^ 2 - X) * derivative (derivative Lm2) + (2 * X - 1) * derivative Lm2 =
        C ((m2 * (m2 + 1) : ℕ) : ℤ) * Lm2 := by linear_combination hode2
    rw [h1, h2]
    have hsub : ((m2 * (m2 + 1) : ℕ) : ℤ) - ((m * (m + 1) : ℕ) : ℤ) =
        ((p ^ 2 * (m * (m + 1)) : ℕ) : ℤ) := by
      have hle : m * (m + 1) ≤ m2 * (m2 + 1) := by nlinarith
      rw [← Nat.cast_sub hle, hm2_diff]
    have hCsub : C ((m2 * (m2 + 1) : ℕ) : ℤ) - C ((m * (m + 1) : ℕ) : ℤ) =
        C ((p ^ 2 * (m * (m + 1)) : ℕ) : ℤ) := by rw [← map_sub, hsub]
    linear_combination -(Lm * Lm2) * hCsub
  have hdg : derivative g = -C ((m * (m + 1) : ℕ) : ℤ) * Lm := by
    have hode1 := shiftedLegendre_ode m
    have hcalc : derivative g =
        -((X ^ 2 - X) * derivative (derivative Lm) + (2 * X - 1) * derivative Lm) := by
      simp only [g, derivative_mul, derivative_sub, derivative_one, derivative_X]
      ring
    rw [hcalc]
    linear_combination -hode1
  -- Compute ((Lm * Lm2).coeff (j * p - 1) : ZMod p) = (Lm.coeff (j - 1) : ZMod p) for j ≥ 1
  have hprod_coeff : ∀ j : ℕ, 1 ≤ j →
      (((Lm * Lm2).coeff (j * p - 1) : ℤ) : ZMod p) = ((Lm.coeff (j - 1) : ℤ) : ZMod p) := by
    intro j hj
    set Lm_p : (ZMod p)[X] := Polynomial.map (Int.castRingHom (ZMod p)) Lm
    have hmap_prod : Polynomial.map (Int.castRingHom (ZMod p)) (Lm * Lm2) =
        Lm_p.comp (X ^ p) * Lm_p ^ 2 := by
      rw [Polynomial.map_mul, shiftedLegendre_m2_mod_p hp2]
      ring
    have hdeg2 : ∀ i, p ≤ i → (Lm_p ^ 2).coeff i = 0 := by
      intro i hi
      apply coeff_eq_zero_of_natDegree_lt
      have h1 : Lm_p.natDegree ≤ m :=
        le_trans natDegree_map_le (by rw [natDegree_shiftedLegendre])
      have h2 : (Lm_p ^ 2).natDegree ≤ 2 * Lm_p.natDegree := natDegree_pow_le
      omega
    have hidx : j * p - 1 = p * (j - 1) + (p - 1) := by
      have : j * p = p * (j - 1) + p := by
        calc j * p = (j - 1 + 1) * p := by rw [Nat.sub_add_cancel hj]
          _ = p * (j - 1) + p := by ring
      omega
    have hcoeff_lhs : (((Lm * Lm2).coeff (j * p - 1) : ℤ) : ZMod p) =
        (Lm_p.comp (X ^ p) * Lm_p ^ 2).coeff (p * (j - 1) + (p - 1)) := by
      rw [← hidx, ← hmap_prod, coeff_map]; rfl
    rw [hcoeff_lhs, coeff_comp_X_pow_mul_of_deg_lt hp_pos Lm_p (Lm_p ^ 2) hdeg2 (j - 1) (p - 1) (by omega)]
    -- Now show (Lm_p ^ 2).coeff (p - 1) = 1
    have hlead : (Lm_p ^ 2).coeff (p - 1) = 1 := by
      have h2m : p - 1 = m + m := by omega
      rw [h2m, sq, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      have hdeg1 : ∀ i, m < i → Lm_p.coeff i = 0 := by
        intro i hi
        apply coeff_eq_zero_of_natDegree_lt
        have h1 : Lm_p.natDegree ≤ m :=
          le_trans natDegree_map_le (by rw [natDegree_shiftedLegendre])
        omega
      have hterm : ∀ i ∈ range (m + m + 1),
          Lm_p.coeff i * Lm_p.coeff (m + m - i) = if i = m then (Lm_p.coeff m) ^ 2 else 0 := by
        intro i _
        by_cases him : i = m
        · subst him; simp [sq]
        · rw [if_neg him]
          by_cases hgt : m < i
          · rw [hdeg1 i hgt, zero_mul]
          · rw [hdeg1 (m + m - i) (by omega), mul_zero]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
      have hcm : Lm_p.coeff m = (-1 : ZMod p) ^ m * ((m + m).choose m : ZMod p) := by
        simp only [Lm_p, Lm, coeff_map, coeff_shiftedLegendre, Nat.choose_self, Nat.cast_one,
          mul_one, eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
      have hch := shiftedLegendre_coeff_mod_p hp2 m (le_refl m)
      have hcm_eq : Lm_p.coeff m = 1 := by
        rw [hcm]
        simpa [m, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast] using hch
      rw [hcm_eq, one_pow]
    rw [hlead, mul_one]
    simp [Lm_p]
  -- Degree bounds on H and g
  have hdeg_g : g.natDegree ≤ m + 1 := by
    have h2 : (X * (1 - X) : ℤ[X]).natDegree ≤ 2 := by
      calc (X * (1 - X) : ℤ[X]).natDegree ≤ X.natDegree + (1 - X : ℤ[X]).natDegree := natDegree_mul_le
        _ ≤ 1 + 1 := by
          have : (1 - X : ℤ[X]).natDegree ≤ max (1 : ℤ[X]).natDegree X.natDegree := natDegree_sub_le _ _
          simp only [natDegree_one, natDegree_X] at this ⊢
          omega
        _ = 2 := rfl
    have hLm_d : (derivative Lm).natDegree ≤ m - 1 := by
      have := natDegree_derivative_le Lm
      have hLm : Lm.natDegree = m := natDegree_shiftedLegendre m
      omega
    have hm1 : 1 ≤ m := by omega
    calc g.natDegree ≤ (X * (1 - X) : ℤ[X]).natDegree + (derivative Lm).natDegree := natDegree_mul_le
      _ ≤ 2 + (m - 1) := by omega
      _ = m + 1 := by omega
  have hdeg_H : H.natDegree ≤ (m + 1) * p := by
    have hm1 : 1 ≤ m := by omega
    have hm2_1 : 1 ≤ m2 := by nlinarith
    have hLm : Lm.natDegree = m := natDegree_shiftedLegendre m
    have hLm2 : Lm2.natDegree = m2 := natDegree_shiftedLegendre m2
    have hW1 : (Lm * derivative Lm2).natDegree ≤ m + m2 - 1 := by
      have hd : (derivative Lm2).natDegree ≤ m2 - 1 := by
        have := natDegree_derivative_le Lm2; omega
      calc (Lm * derivative Lm2).natDegree ≤ Lm.natDegree + (derivative Lm2).natDegree := natDegree_mul_le
        _ ≤ m + (m2 - 1) := by omega
        _ = m + m2 - 1 := by omega
    have hW2 : (derivative Lm * Lm2).natDegree ≤ m + m2 - 1 := by
      have hd : (derivative Lm).natDegree ≤ m - 1 := by
        have := natDegree_derivative_le Lm; omega
      calc (derivative Lm * Lm2).natDegree ≤ (derivative Lm).natDegree + Lm2.natDegree := natDegree_mul_le
        _ ≤ (m - 1) + m2 := by omega
        _ = m + m2 - 1 := by omega
    have hW : (Lm * derivative Lm2 - derivative Lm * Lm2).natDegree ≤ m + m2 - 1 :=
      le_trans (natDegree_sub_le _ _) (max_le hW1 hW2)
    have hX1X : (X * (1 - X) : ℤ[X]).natDegree ≤ 2 := by
      calc (X * (1 - X) : ℤ[X]).natDegree ≤ X.natDegree + (1 - X : ℤ[X]).natDegree := natDegree_mul_le
        _ ≤ 1 + 1 := by
          have : (1 - X : ℤ[X]).natDegree ≤ max (1 : ℤ[X]).natDegree X.natDegree := natDegree_sub_le _ _
          simp only [natDegree_one, natDegree_X] at this ⊢
          omega
        _ = 2 := rfl
    have hm2_eq : m2 = p * m + m := by
      have : 2 * (p * m + m) + 1 = p ^ 2 := by nlinarith
      omega
    have h2eq : 2 + (m + m2 - 1) = (m + 1) * p := by
      have : 2 + (m + m2 - 1) = m + m2 + 1 := by omega
      rw [this]; nlinarith
    calc H.natDegree ≤ (X * (1 - X) : ℤ[X]).natDegree +
          (Lm * derivative Lm2 - derivative Lm * Lm2).natDegree := natDegree_mul_le
      _ ≤ 2 + (m + m2 - 1) := by omega
      _ = (m + 1) * p := h2eq
  -- Compare coefficients for every k : ℕ
  ext k
  rw [coeff_map, coeff_C_mul]
  rcases k with _ | k'
  · -- k = 0
    have hH0 : H.coeff 0 = 0 := by
      have : H = X * ((1 - X) * (Lm * derivative Lm2 - derivative Lm * Lm2)) := by simp only [H]; ring
      rw [this, coeff_X_mul_zero]
    have hg0 : g.coeff 0 = 0 := by
      have : g = X * ((1 - X) * derivative Lm) := by simp only [g]; ring
      rw [this, coeff_X_mul_zero]
    have hcomp0 : ((Polynomial.map (Int.castRingHom (ZMod (p ^ 2))) g).comp (X ^ p)).coeff 0 = 0 := by
      have := coeff_comp_X_pow hp_pos (Polynomial.map (Int.castRingHom (ZMod (p ^ 2))) g) 0
      simpa [hg0] using this
    rw [hH0, hcomp0, map_zero, mul_zero]
  · set k := k' + 1
    by_cases hd : p ∣ k
    · rcases hd with ⟨j, hj_eq⟩
      have hj1 : 1 ≤ j := by
        by_contra h0
        have : j = 0 := by omega
        subst this; simp at hj_eq
      have hcomp_k : ((Polynomial.map (Int.castRingHom (ZMod (p ^ 2))) g).comp (X ^ p)).coeff k =
          (g.coeff j : ZMod (p ^ 2)) := by
        have h := coeff_comp_X_pow hp_pos (Polynomial.map (Int.castRingHom (ZMod (p ^ 2))) g) j
        rw [← hj_eq, coeff_map] at h
        exact h
      rw [hcomp_k]
      by_cases hj_le : j ≤ m + 1
      · -- 1 ≤ j ≤ m + 1 < p, so j is a unit mod p^2!
        have hH_coeff : (k : ℤ) * H.coeff k =
            -(((p ^ 2 * (m * (m + 1)) : ℕ) : ℤ)) * (Lm * Lm2).coeff (k - 1) := by
          have := congr_arg (fun q => q.coeff k') hdH
          rw [coeff_derivative, neg_mul, coeff_neg, coeff_C_mul] at this
          have hk_sub : k - 1 = k' := Nat.add_sub_cancel k' 1
          rw [hk_sub]
          change ((k' + 1 : ℕ) : ℤ) * H.coeff (k' + 1) = _
          push_cast at this ⊢
          linear_combination this
        have hg_coeff : (j : ℤ) * g.coeff j = -(((m * (m + 1) : ℕ) : ℤ)) * Lm.coeff (j - 1) := by
          have := congr_arg (fun q => q.coeff (j - 1)) hdg
          rw [coeff_derivative, neg_mul, coeff_neg, coeff_C_mul, Nat.sub_add_cancel hj1] at this
          have hj_eq_z : ((j - 1 : ℕ) : ℤ) + 1 = (j : ℤ) := by
            have := Nat.sub_add_cancel hj1
            exact_mod_cast this
          rw [hj_eq_z] at this
          linear_combination this
        have hcancel_p : (j : ℤ) * H.coeff k =
            -(p : ℤ) * ((m * (m + 1) : ℕ) : ℤ) * (Lm * Lm2).coeff (j * p - 1) := by
          have hp_ne : (p : ℤ) ≠ 0 := by positivity
          apply mul_left_cancel₀ hp_ne
          have hkj : (k : ℤ) = (p : ℤ) * (j : ℤ) := by exact_mod_cast hj_eq
          have hkm1 : k - 1 = j * p - 1 := by rw [hj_eq, mul_comm]
          rw [hkj, hkm1] at hH_coeff
          push_cast at hH_coeff ⊢
          linear_combination hH_coeff
        have hdiff_z : (j : ℤ) * (H.coeff k - (p : ℤ) * g.coeff j) =
            -(p : ℤ) * ((m * (m + 1) : ℕ) : ℤ) * ((Lm * Lm2).coeff (j * p - 1) - Lm.coeff (j - 1)) := by
          linear_combination hcancel_p - (p : ℤ) * hg_coeff
        have hp_dvd_diff : (p : ℤ) ∣ (Lm * Lm2).coeff (j * p - 1) - Lm.coeff (j - 1) := by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, hprod_coeff j hj1, sub_self]
        rcases hp_dvd_diff with ⟨t, ht⟩
        have hmod0 : (j : ZMod (p ^ 2)) * ((H.coeff k : ZMod (p ^ 2)) - (p : ZMod (p ^ 2)) * (g.coeff j : ZMod (p ^ 2))) = 0 := by
          have hc := congr_arg (Int.castRingHom (ZMod (p ^ 2))) hdiff_z
          rw [ht] at hc
          simp only [map_mul, map_sub, map_neg, map_natCast, eq_intCast] at hc
          rw [hc]
          have hp2z : ((p : ZMod (p ^ 2)) ^ 2) = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
          linear_combination -(((m * (m + 1) : ℕ) : ZMod (p ^ 2)) * (t : ZMod (p ^ 2))) * hp2z
        have hj_unit : IsUnit (j : ZMod (p ^ 2)) := by
          refine (ZMod.isUnit_iff_coprime j (p ^ 2)).mpr ?_
          exact (hp_pr.coprime_iff_not_dvd.mpr (fun hd' => by
            have := Nat.le_of_dvd (by omega) hd'; omega)).symm.pow_right 2
        have hsub0 : (H.coeff k : ZMod (p ^ 2)) - (p : ZMod (p ^ 2)) * (g.coeff j : ZMod (p ^ 2)) = 0 :=
          hj_unit.mul_right_eq_zero.mp hmod0
        exact sub_eq_zero.mp hsub0
      · -- j > m + 1: both coefficients are 0 by degree bounds!
        have hH0 : H.coeff k = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          have h1 : (m + 1) * p < j * p := Nat.mul_lt_mul_of_pos_right (by omega) hp_pos
          have h2 : (m + 1) * p < k := by rw [hj_eq]; nlinarith
          omega
        have hg0 : g.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
        rw [hH0, hg0, map_zero, Int.cast_zero, mul_zero]
    · -- ¬ p ∣ k: both coefficients are 0 mod p^2!
      have hcomp0 : ((Polynomial.map (Int.castRingHom (ZMod (p ^ 2))) g).comp (X ^ p)).coeff k = 0 :=
        coeff_comp_X_pow_of_not_dvd _ hd
      rw [hcomp0, mul_zero]
      have hH_coeff : (k : ℤ) * H.coeff k =
          -(((p ^ 2 * (m * (m + 1)) : ℕ) : ℤ)) * (Lm * Lm2).coeff (k - 1) := by
        have := congr_arg (fun q => q.coeff k') hdH
        rw [coeff_derivative, neg_mul, coeff_neg, coeff_C_mul] at this
        have hk_sub : k - 1 = k' := Nat.add_sub_cancel k' 1
        rw [hk_sub]
        change ((k' + 1 : ℕ) : ℤ) * H.coeff (k' + 1) = _
        push_cast at this ⊢
        linear_combination this
      have hmod0 : (k : ZMod (p ^ 2)) * (H.coeff k : ZMod (p ^ 2)) = 0 := by
        have hc := congr_arg (Int.castRingHom (ZMod (p ^ 2))) hH_coeff
        simp only [map_mul, map_neg, map_natCast, eq_intCast] at hc
        rw [hc]
        have hp2z : ((p : ZMod (p ^ 2)) ^ 2) = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
        push_cast
        rw [hp2z]; ring
      have hk_unit : IsUnit (k : ZMod (p ^ 2)) := by
        refine (ZMod.isUnit_iff_coprime k (p ^ 2)).mpr ?_
        exact (hp_pr.coprime_iff_not_dvd.mpr hd).symm.pow_right 2
      have hres := hk_unit.mul_right_eq_zero.mp hmod0
      simpa only [eq_intCast] using hres

private lemma shiftedLegendre_m2_eval_x0_mod_p2 {p : ℕ} [Fact p.Prime] (hp : OeisA3625.A p) :
    aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) (shiftedLegendre ((p ^ 2 - 1) / 2)) =
      (-1 : ZOmega (ZMod (p ^ 2))) ^ ((p - 1) / 2) * (p : ZOmega (ZMod (p ^ 2))) := by
  set m := (p - 1) / 2
  set m2 := (p ^ 2 - 1) / 2
  set Lm := shiftedLegendre m
  set Lm2 := shiftedLegendre m2
  set g := X * (1 - X) * derivative Lm
  have hp2 : p ≠ 2 := A3625_ne_two hp
  have hp_pr : p.Prime := Fact.out
  set proj : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)
  set zproj : ZOmega (ZMod (p ^ 2)) →+* ZOmega (ZMod p) := ZOmega.mapRingHom proj
  have hzproj_x0 : zproj (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) = (ZOmega.x0 : ZOmega (ZMod p)) :=
    ZOmega.mapRingHom_x0 proj
  have hzproj_aeval : ∀ f : ℤ[X],
      zproj (aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) f) = aeval (ZOmega.x0 : ZOmega (ZMod p)) f := by
    intro f
    rw [aeval_def, aeval_def, Polynomial.hom_eval₂, hzproj_x0]
    congr 1
    ext
    simp
  -- 1. Evaluate Wronskian mod p^2 at x0
  have hW := wronskian_mod_p2 (p := p) hp2
  have hW_x0 := congr_arg (eval₂ ZOmega.of (ZOmega.x0 : ZOmega (ZMod (p ^ 2)))) hW
  have heval_map : ∀ f : ℤ[X],
      eval₂ ZOmega.of (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) (Polynomial.map (Int.castRingHom (ZMod (p ^ 2))) f) =
      aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) f := by
    intro f
    rw [eval₂_map, aeval_def]
    congr 1
    ext
    simp
  have hW_lhs : eval₂ ZOmega.of (ZOmega.x0 : ZOmega (ZMod (p ^ 2)))
      (Polynomial.map (Int.castRingHom (ZMod (p ^ 2)))
        (X * (1 - X : ℤ[X]) * (Lm * derivative Lm2 - derivative Lm * Lm2))) =
      aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) (X * (1 - X : ℤ[X])) *
        (aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) Lm *
          aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) (derivative Lm2)) -
      aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) g *
        aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) Lm2 := by
    rw [heval_map]
    simp only [g, map_mul, map_sub]
    ring
  have hW_rhs : eval₂ ZOmega.of (ZOmega.x0 : ZOmega (ZMod (p ^ 2)))
      (C (p : ZMod (p ^ 2)) * (Polynomial.map (Int.castRingHom (ZMod (p ^ 2))) g).comp (X ^ p)) =
      (p : ZOmega (ZMod (p ^ 2))) *
        eval₂ ZOmega.of ((ZOmega.x0 : ZOmega (ZMod (p ^ 2))) ^ p)
          (Polynomial.map (Int.castRingHom (ZMod (p ^ 2))) g) := by
    rw [eval₂_mul, eval₂_C, eval₂_comp, eval₂_pow, eval₂_X]
    simp
  rw [hW_lhs, hW_rhs] at hW_x0
  -- 2. Show Lm(x0) * Lm2'(x0) = 0 in ZOmega (ZMod (p^2))
  have hmul_p_zero : ∀ u v : ZOmega (ZMod (p ^ 2)), zproj u = 0 → zproj v = 0 → u * v = 0 := by
    intro u v hu hv
    have hd_re : ∀ w : ZOmega (ZMod (p ^ 2)), zproj w = 0 → (p : ℕ) ∣ w.re.val ∧ (p : ℕ) ∣ w.im.val := by
      intro w hw
      have hre : proj w.re = 0 := congr_arg ZOmega.re hw
      have him : proj w.im = 0 := congr_arg ZOmega.im hw
      constructor
      · rw [← ZMod.natCast_zmod_val w.re, map_natCast, ZMod.natCast_eq_zero_iff] at hre
        exact hre
      · rw [← ZMod.natCast_zmod_val w.im, map_natCast, ZMod.natCast_eq_zero_iff] at him
        exact him
    rcases hd_re u hu with ⟨⟨a1, ha1⟩, ⟨a2, ha2⟩⟩
    rcases hd_re v hv with ⟨⟨b1, hb1⟩, ⟨b2, hb2⟩⟩
    have hu_eq : u = (p : ZOmega (ZMod (p ^ 2))) * ⟨(a1 : ZMod (p ^ 2)), (a2 : ZMod (p ^ 2))⟩ := by
      apply ZOmega.ext
      · simp only [ZOmega.mul_re, ZOmega.natCast_re, ZOmega.natCast_im, mul_zero, zero_mul, sub_zero]
        rw [← Nat.cast_mul, ← ha1, ZMod.natCast_zmod_val]
      · simp only [ZOmega.mul_im, ZOmega.natCast_re, ZOmega.natCast_im, zero_mul, add_zero]
        rw [← Nat.cast_mul, ← ha2, ZMod.natCast_zmod_val]
    have hv_eq : v = (p : ZOmega (ZMod (p ^ 2))) * ⟨(b1 : ZMod (p ^ 2)), (b2 : ZMod (p ^ 2))⟩ := by
      apply ZOmega.ext
      · simp only [ZOmega.mul_re, ZOmega.natCast_re, ZOmega.natCast_im, mul_zero, zero_mul, sub_zero]
        rw [← Nat.cast_mul, ← hb1, ZMod.natCast_zmod_val]
      · simp only [ZOmega.mul_im, ZOmega.natCast_re, ZOmega.natCast_im, zero_mul, add_zero]
        rw [← Nat.cast_mul, ← hb2, ZMod.natCast_zmod_val]
    rw [hu_eq, hv_eq]
    have hp2z : (p : ZOmega (ZMod (p ^ 2))) ^ 2 = 0 := by
      rw [← Nat.cast_pow, ← map_natCast ZOmega.of (p ^ 2), ZMod.natCast_self, map_zero]
    linear_combination (⟨(a1 : ZMod (p ^ 2)), (a2 : ZMod (p ^ 2))⟩ *
      ⟨(b1 : ZMod (p ^ 2)), (b2 : ZMod (p ^ 2))⟩) * hp2z
  have hLm_p0 : zproj (aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) Lm) = 0 := by
    rw [hzproj_aeval]
    exact shiftedLegendre_eval_x0_eq_zero hp
  have hLm2d_p0 : zproj (aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) (derivative Lm2)) = 0 := by
    rw [hzproj_aeval, aeval_int_eq_eval_map]
    have hmap_eq : Polynomial.map (Int.castRingHom (ZOmega (ZMod p))) (derivative Lm2) =
        Polynomial.map ZOmega.of (derivative (Polynomial.map (Int.castRingHom (ZMod p)) Lm2)) := by
      rw [derivative_map, Polynomial.map_map]
      congr 1
      ext; simp
    rw [hmap_eq, shiftedLegendre_m2_mod_p hp2, poly_comp_X_pow_p_eq_pow_p]
    set Lm_p : (ZMod p)[X] := Polynomial.map (Int.castRingHom (ZMod p)) Lm
    have hd_pow : derivative (Lm_p ^ p) = 0 := by
      rw [derivative_pow, ZMod.natCast_self, map_zero, zero_mul, zero_mul]
    rw [derivative_mul, hd_pow, zero_mul, zero_add, Polynomial.map_mul, Polynomial.map_pow,
      eval_mul, eval_pow]
    have hLm_eval0 : (Polynomial.map ZOmega.of Lm_p).eval (ZOmega.x0 : ZOmega (ZMod p)) = 0 := by
      rw [Polynomial.map_map]
      have : ZOmega.of.comp (Int.castRingHom (ZMod p)) = Int.castRingHom (ZOmega (ZMod p)) := by
        ext; simp
      rw [this, ← aeval_int_eq_eval_map]
      exact shiftedLegendre_eval_x0_eq_zero hp
    rw [hLm_eval0, zero_pow hp_pr.ne_zero, zero_mul]
  have hterm1_zero : aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) Lm *
      aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) (derivative Lm2) = 0 :=
    hmul_p_zero _ _ hLm_p0 hLm2d_p0
  rw [hterm1_zero, mul_zero, zero_sub] at hW_x0
  -- 3. Show p * g(x0^p) = p * (-(-1)^m * g(x0)) in ZOmega (ZMod (p^2))
  have hp_mul_eq : ∀ u v : ZOmega (ZMod (p ^ 2)), zproj u = zproj v →
      (p : ZOmega (ZMod (p ^ 2))) * u = (p : ZOmega (ZMod (p ^ 2))) * v := by
    intro u v huv
    have hsub : zproj (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have hp0 : zproj (p : ZOmega (ZMod (p ^ 2))) = 0 := by
      rw [map_natCast, ← map_natCast ZOmega.of p, ZMod.natCast_self, map_zero]
    have := hmul_p_zero (p : ZOmega (ZMod (p ^ 2))) (u - v) hp0 hsub
    linear_combination this
  have hgp_eq : zproj (eval₂ ZOmega.of ((ZOmega.x0 : ZOmega (ZMod (p ^ 2))) ^ p)
        (Polynomial.map (Int.castRingHom (ZMod (p ^ 2))) g)) =
      zproj (-((-1 : ZOmega (ZMod (p ^ 2))) ^ m) * aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) g) := by
    have hlhs : zproj (eval₂ ZOmega.of ((ZOmega.x0 : ZOmega (ZMod (p ^ 2))) ^ p)
          (Polynomial.map (Int.castRingHom (ZMod (p ^ 2))) g)) =
        aeval ((ZOmega.x0 : ZOmega (ZMod p)) ^ p) g := by
      rw [eval₂_map, Polynomial.hom_eval₂, map_pow, hzproj_x0, aeval_def]
      congr 1
      ext; simp
    rw [hlhs, ZOmega.x0_pow_p_eq_one_sub hp]
    have h1sub : aeval (1 - (ZOmega.x0 : ZOmega (ZMod p))) g =
        aeval (ZOmega.x0 : ZOmega (ZMod p)) (g.comp (1 - X)) := by
      rw [aeval_comp]
      simp only [map_sub, map_one, aeval_X]
    rw [h1sub, shiftedLegendre_deriv_comp_one_sub m]
    simp only [g, Lm, map_mul, map_neg, map_pow, map_one, hzproj_aeval]
  rw [hp_mul_eq _ _ hgp_eq] at hW_x0
  -- 4. Cancel the unit g(x0) in ZOmega (ZMod (p^2))
  have hg_unit : IsUnit (aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) g) := by
    apply ZOmega.isUnit_mod_p2_of_ne_zero_mod_p hp
    rw [hzproj_aeval]
    simp only [g, map_mul, map_sub, map_one, aeval_X, ZOmega.x0_mul_one_sub]
    intro h0
    have h16_unit : IsUnit (16 : ZOmega (ZMod p)) := by
      have h2ne : (2 : ZMod p) ≠ 0 := by
        intro h2
        have h2d : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h2)
        have := Nat.le_of_dvd (by decide) h2d
        have := A3625_three_le hp
        omega
      have h2u : IsUnit (2 : ZOmega (ZMod p)) := by
        refine IsUnit.of_mul_eq_one (ZOmega.of (2 : ZMod p)⁻¹) ?_
        have h2of : (2 : ZOmega (ZMod p)) = ZOmega.of (2 : ZMod p) := (map_ofNat ZOmega.of 2).symm
        rw [h2of, ← map_mul, mul_inv_cancel₀ h2ne, map_one]
      have : (16 : ZOmega (ZMod p)) = (2 : ZOmega (ZMod p)) ^ 4 := by ring
      rw [this]
      exact h2u.pow 4
    exact shiftedLegendre_deriv_x0_ne_zero hp (h16_unit.mul_right_eq_zero.mp h0)
  have hdiff0 : aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) g *
      (aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 2))) Lm2 -
        (-1 : ZOmega (ZMod (p ^ 2))) ^ m * (p : ZOmega (ZMod (p ^ 2)))) = 0 := by
    linear_combination -hW_x0
  exact sub_eq_zero.mp (hg_unit.mul_right_eq_zero.mp hdiff0)

private lemma shiftedLegendre_m2_eval_x0_sq_mod_p3 {p : ℕ} [Fact p.Prime] (hp : OeisA3625.A p) :
    aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 3))) ((shiftedLegendre ((p ^ 2 - 1) / 2)) ^ 2) =
      (p : ZOmega (ZMod (p ^ 3))) ^ 2 := by
  set m := (p - 1) / 2
  set m2 := (p ^ 2 - 1) / 2
  set z : ZOmega ℤ := aeval (ZOmega.x0 : ZOmega ℤ) (shiftedLegendre m2)
  have hcast : ∀ N : ℕ, ZOmega.mapRingHom (Int.castRingHom (ZMod N)) z =
      aeval (ZOmega.x0 : ZOmega (ZMod N)) (shiftedLegendre m2) := by
    intro N
    simp only [z, aeval_def]
    rw [Polynomial.hom_eval₂, ZOmega.mapRingHom_x0]
    congr 1; ext; simp
  have hmod2 : ZOmega.mapRingHom (Int.castRingHom (ZMod (p ^ 2))) z =
      (-1 : ZOmega (ZMod (p ^ 2))) ^ m * (p : ZOmega (ZMod (p ^ 2))) := by
    rw [hcast]
    exact shiftedLegendre_m2_eval_x0_mod_p2 hp
  have hof_rhs : (-1 : ZOmega (ZMod (p ^ 2))) ^ m * (p : ZOmega (ZMod (p ^ 2))) =
      ZOmega.of (((-1 : ℤ) ^ m * (p : ℤ) : ℤ) : ZMod (p ^ 2)) := by
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast,
      map_mul, map_pow, map_neg, map_one, map_natCast]
  have hdvd_re : ((p ^ 2 : ℕ) : ℤ) ∣ z.re - (-1 : ℤ) ^ m * (p : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hre := congr_arg ZOmega.re hmod2
    rw [hof_rhs, ZOmega.of_re] at hre
    simpa [ZOmega.mapRingHom, sub_eq_zero] using hre
  have hdvd_im : ((p ^ 2 : ℕ) : ℤ) ∣ z.im := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have him := congr_arg ZOmega.im hmod2
    rw [hof_rhs, ZOmega.of_im] at him
    simpa [ZOmega.mapRingHom] using him
  rcases hdvd_re with ⟨a, ha⟩
  rcases hdvd_im with ⟨b, hb⟩
  have hz_eq : z = ZOmega.of ((-1 : ℤ) ^ m * (p : ℤ)) + ZOmega.of ((p ^ 2 : ℕ) : ℤ) * ⟨a, b⟩ := by
    apply ZOmega.ext
    · simp only [ZOmega.add_re, ZOmega.of_re, ZOmega.mul_re, ZOmega.of_im]
      linarith
    · simp only [ZOmega.add_im, ZOmega.of_im, ZOmega.mul_im, ZOmega.of_re, zero_mul, add_zero, zero_add]
      linarith
  have hz2 : z ^ 2 = ZOmega.of ((p : ℤ) ^ 2) +
      ZOmega.of ((p ^ 3 : ℕ) : ℤ) * (ZOmega.of (2 * (-1 : ℤ) ^ m) * ⟨a, b⟩ + ZOmega.of (p : ℤ) * ⟨a, b⟩ ^ 2) := by
    rw [hz_eq]
    have hsq1 : (ZOmega.of ((-1 : ℤ) ^ m * (p : ℤ))) ^ 2 = ZOmega.of ((p : ℤ) ^ 2) := by
      rw [← map_pow, mul_pow, ← pow_mul, mul_comm m 2, pow_mul]
      norm_num
    have hp3_1 : ZOmega.of ((-1 : ℤ) ^ m * (p : ℤ)) * ZOmega.of ((p ^ 2 : ℕ) : ℤ) * 2 =
        ZOmega.of ((p ^ 3 : ℕ) : ℤ) * ZOmega.of (2 * (-1 : ℤ) ^ m) := by
      rw [← map_mul, ← map_mul]
      have : (2 : ZOmega ℤ) = ZOmega.of 2 := (map_ofNat ZOmega.of 2).symm
      rw [this, ← map_mul]
      congr 1; push_cast; ring
    have hp3_2 : (ZOmega.of ((p ^ 2 : ℕ) : ℤ)) ^ 2 =
        ZOmega.of ((p ^ 3 : ℕ) : ℤ) * ZOmega.of (p : ℤ) := by
      rw [← map_pow, ← map_mul]
      congr 1; push_cast; ring
    linear_combination hsq1 + hp3_1 * ⟨a, b⟩ + hp3_2 * ⟨a, b⟩ ^ 2
  rw [map_pow, ← hcast (p ^ 3), ← map_pow, hz2]
  simp only [map_add, map_mul]
  have hmap_of : ∀ r : ℤ,
      ZOmega.mapRingHom (Int.castRingHom (ZMod (p ^ 3))) (ZOmega.of r) =
      ZOmega.of (r : ZMod (p ^ 3)) := fun r => by
    apply ZOmega.ext
    · rfl
    · simp [ZOmega.mapRingHom]
  have hp3_zero : ZOmega.mapRingHom (Int.castRingHom (ZMod (p ^ 3))) (ZOmega.of ((p ^ 3 : ℕ) : ℤ)) = 0 := by
    rw [hmap_of, Int.cast_natCast, ZMod.natCast_self, map_zero]
  have hp2_eq : ZOmega.mapRingHom (Int.castRingHom (ZMod (p ^ 3))) (ZOmega.of ((p : ℤ) ^ 2)) =
      (p : ZOmega (ZMod (p ^ 3))) ^ 2 := by
    rw [hmap_of, Int.cast_pow, Int.cast_natCast, map_pow, map_natCast]
  rw [hp3_zero, zero_mul, add_zero, hp2_eq]

/- ### Section 7: Clausen mod `p^3`, truncation, and proof of Conjecture 2 -/

private lemma prod_sub_p2_mod_p3 {p : ℕ} (q : ℕ) (f : ℕ → ZMod (p ^ 3)) :
    ∃ c : ZMod (p ^ 3), (∏ i ∈ range q, (f i - (p : ZMod (p ^ 3)) ^ 2)) =
      (∏ i ∈ range q, f i) + (p : ZMod (p ^ 3)) ^ 2 * c := by
  induction q with
  | zero => exact ⟨0, by simp⟩
  | succ q ih =>
    rcases ih with ⟨c, hc⟩
    rw [Finset.prod_range_succ, hc, Finset.prod_range_succ]
    exact ⟨c * f q - (∏ i ∈ range q, f i) - (p : ZMod (p ^ 3)) ^ 2 * c, by ring⟩

private lemma a_m2_mod_p3 {p : ℕ} [Fact p.Prime] (hp : OeisA3625.A p) :
    OeisA79727.a ((p ^ 2 - 1) / 2) ≡ p ^ 2 [MOD p ^ 3] := by
  set m := (p - 1) / 2
  set m2 := (p ^ 2 - 1) / 2
  have hp_pr : p.Prime := Fact.out
  have hp_pos : 0 < p := hp_pr.pos
  have hp2 : p ≠ 2 := A3625_ne_two hp
  have hp_odd : Odd p := A3625_odd hp
  have h2m1 : 2 * m + 1 = p := by
    have := Nat.odd_iff.mp hp_odd
    omega
  have hm2_eq : m2 = p * m + m := by
    have h2 : 2 * (p * m + m) + 1 = p ^ 2 := by nlinarith
    have hsq : 1 ≤ p ^ 2 := by nlinarith
    omega
  have h2m2 : 2 * m2 + 1 = p ^ 2 := by nlinarith
  -- Step 1: Clausen at m2, x0 in ZOmega (ZMod (p^3))
  have hcl := shiftedLegendre_m2_eval_x0_sq_mod_p3 hp
  rw [clausen_poly_identity m2, aeval_comp] at hcl
  have hz_val : aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 3))) (X ^ 2 - X : ℤ[X]) =
      (-16 : ZOmega (ZMod (p ^ 3))) := by
    simp only [map_sub, map_pow, aeval_X, ZOmega.neg_x0_mul_one_sub]
  rw [hz_val, map_sum] at hcl
  have hsum_re : (∑ k ∈ range (m2 + 1),
      (((m2 + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k : ZMod (p ^ 3))) =
      (p : ZMod (p ^ 3)) ^ 2 := by
    have hre := congr_arg ZOmega.re hcl
    have hrhs : ((p : ZOmega (ZMod (p ^ 3))) ^ 2).re = (p : ZMod (p ^ 3)) ^ 2 := by
      simp [pow_two]
    rw [hrhs] at hre
    rw [← hre]
    have hre_sum : ∀ s : Finset ℕ, ∀ f : ℕ → ZOmega (ZMod (p ^ 3)),
        (∑ k ∈ s, f k).re = ∑ k ∈ s, (f k).re := by
      intro s f
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ZOmega.add_re, ih]
    rw [hre_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_mul, map_pow, aeval_C, aeval_X, eq_intCast]
    have hof : ((((m2 + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 : ℤ) : ZOmega (ZMod (p ^ 3))) *
          (-16 : ZOmega (ZMod (p ^ 3))) ^ k =
        ZOmega.of ((((m2 + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k : ZMod (p ^ 3))) := by
      simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_neg, Int.cast_ofNat,
        map_mul, map_pow, map_natCast, map_neg, map_ofNat]
    rw [hof, ZOmega.of_re]
  -- Step 2: Reindex range (m2 + 1) into blocks of size p (up to (m + 1) * p), noting terms with r > m vanish!
  have hterm_gt_zero : ∀ q r : ℕ, q ≤ m → m < r → r < p →
      ((((m2 + (p * q + r)).choose (2 * (p * q + r)) : ℤ) *
          ((2 * (p * q + r)).choose (p * q + r) : ℤ) ^ 2 * (-16 : ℤ) ^ (p * q + r) : ZMod (p ^ 3)) = 0) ∧
      ((((2 * (p * q + r)).choose (p * q + r) : ℕ) : ZMod (p ^ 3)) ^ 3 = 0) := by
    intro q r hqm hrm hrp
    have hd1 : p ∣ (2 * (p * q + r)).choose (p * q + r) :=
      choose_two_mul_dvd_p_of_gt_half p hp2 q r hrm hrp
    have hcube0 : (((2 * (p * q + r)).choose (p * q + r) : ℕ) : ZMod (p ^ 3)) ^ 3 = 0 := by
      rcases hd1 with ⟨t, ht⟩
      rw [ht, Nat.cast_mul, mul_pow, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]
    have hd2 : p ∣ (m2 + (p * q + r)).choose (2 * (p * q + r)) := by
      by_cases hlt : m2 + (p * q + r) < 2 * (p * q + r)
      · rw [Nat.choose_eq_zero_of_lt hlt]; exact dvd_zero p
      · have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat
          (p := p) (n := m2 + (p * q + r)) (k := 2 * (p * q + r))
        have hn_eq : m2 + (p * q + r) = p * (m + q + 1) + (m + r - p) := by
          have : m2 + (p * q + r) + p = p * (m + q + 1) + (m + r) := by rw [hm2_eq]; ring
          omega
        have hk_eq : 2 * (p * q + r) = p * (2 * q + 1) + (2 * r - p) := by
          have : 2 * (p * q + r) + p = p * (2 * q + 1) + 2 * r := by ring
          omega
        have hmod1 : (m2 + (p * q + r)) % p = m + r - p := by
          rw [hn_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
        have hmod2 : (2 * (p * q + r)) % p = 2 * r - p := by
          rw [hk_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
        have hlt_r : m + r - p < 2 * r - p := by omega
        rw [hmod1, hmod2, Nat.choose_eq_zero_of_lt hlt_r, zero_mul] at hl
        exact Nat.dvd_of_mod_eq_zero hl
    refine ⟨?_, hcube0⟩
    rcases hd1 with ⟨t1, ht1⟩
    rcases hd2 with ⟨t2, ht2⟩
    have hd3 : p ^ 3 ∣ (m2 + (p * q + r)).choose (2 * (p * q + r)) *
        ((2 * (p * q + r)).choose (p * q + r)) ^ 2 := by
      rw [ht1, ht2]
      exact ⟨t2 * t1 ^ 2, by ring⟩
    rcases hd3 with ⟨t3, ht3⟩
    have hzero2 : (((m2 + (p * q + r)).choose (2 * (p * q + r)) : ℤ) *
          ((2 * (p * q + r)).choose (p * q + r) : ℤ) ^ 2 : ZMod (p ^ 3)) = 0 := by
      have hnat : ((((m2 + (p * q + r)).choose (2 * (p * q + r)) *
          ((2 * (p * q + r)).choose (p * q + r)) ^ 2 : ℕ) : ZMod (p ^ 3))) = 0 := by
        rw [ht3, Nat.cast_mul, ZMod.natCast_self, zero_mul]
      simpa only [Nat.cast_mul, Nat.cast_pow, Int.cast_natCast] using hnat
    rw [hzero2, zero_mul]
  -- Step 3: For each block q ≤ m and r ≤ m, relate clausenTerm to C(2k,k)^3 via clausen_term_prod_identity
  have hblock_eq : ∀ q ∈ range (m + 1),
      (∑ r ∈ range (m + 1),
        (((m2 + (p * q + r)).choose (2 * (p * q + r)) : ℤ) *
          ((2 * (p * q + r)).choose (p * q + r) : ℤ) ^ 2 * (-16 : ℤ) ^ (p * q + r) : ZMod (p ^ 3))) =
      (∑ r ∈ range (m + 1), (((2 * (p * q + r)).choose (p * q + r) : ℕ) : ZMod (p ^ 3)) ^ 3) := by
    intro q hq
    rw [Finset.mem_range] at hq
    set Mq : ZMod (p ^ 3) := ∏ i ∈ range q, ((2 * (i : ZMod (p ^ 3)) + 1) ^ 2)
    have hMq_unit : IsUnit Mq := by
      rw [IsUnit.prod_iff]
      intro i hi
      rw [Finset.mem_range] at hi
      refine (ZMod.isUnit_iff_coprime (2 * i + 1) (p ^ 3)).mpr ?_ |> fun h => by
        simpa [Nat.cast_add, Nat.cast_mul] using h.pow 2
      exact (hp_pr.coprime_iff_not_dvd.mpr (fun hd => by
        have := Nat.le_of_dvd (by omega) hd; omega)).symm.pow_right 3
    have hterm_rel : ∀ r ∈ range (m + 1),
        Mq * (((m2 + (p * q + r)).choose (2 * (p * q + r)) : ℤ) *
          ((2 * (p * q + r)).choose (p * q + r) : ℤ) ^ 2 * (-16 : ℤ) ^ (p * q + r) : ZMod (p ^ 3)) =
        (∏ i ∈ range q, ((2 * (i : ZMod (p ^ 3)) + 1) ^ 2 - (p : ZMod (p ^ 3)) ^ 2)) *
          (((2 * (p * q + r)).choose (p * q + r) : ℕ) : ZMod (p ^ 3)) ^ 3 := by
      intro r hr
      rw [Finset.mem_range] at hr
      set k := p * q + r
      have hk_le_m2 : k ≤ m2 := by
        have : p * q ≤ p * m := Nat.mul_le_mul_left p (by omega)
        dsimp only [k]
        omega
      have hprod := clausen_term_prod_identity m2 k hk_le_m2
      -- Split range k into S = image (fun i => i * p + m) (range q) and T = range k \ S
      set S : Finset ℕ := (range q).image (fun i => i * p + m)
      have hS_sub : S ⊆ range k := by
        intro j hj
        rw [Finset.mem_image] at hj
        rcases hj with ⟨i, hi, rfl⟩
        rw [Finset.mem_range] at hi ⊢
        have : (i + 1) * p ≤ q * p := Nat.mul_le_mul_right p (by omega)
        dsimp only [k]
        nlinarith
      have hS_inj : Set.InjOn (fun i => i * p + m) (range q : Set ℕ) := by
        intro a _ b _ hab
        dsimp only at hab
        have : a * p = b * p := by omega
        exact Nat.eq_of_mul_eq_mul_right hp_pos this
      have hsplit_L : (∏ j ∈ range k, ((2 * (j : ℤ) + 1) ^ 2)) =
          (p : ℤ) ^ (2 * q) * (∏ i ∈ range q, ((2 * (i : ℤ) + 1) ^ 2)) *
          (∏ j ∈ range k \ S, ((2 * (j : ℤ) + 1) ^ 2)) := by
        rw [← Finset.prod_sdiff hS_sub, Finset.prod_image hS_inj]
        have hS_prod : (∏ i ∈ range q, ((2 * ((i * p + m : ℕ) : ℤ) + 1) ^ 2)) =
            (p : ℤ) ^ (2 * q) * (∏ i ∈ range q, ((2 * (i : ℤ) + 1) ^ 2)) := by
          have hterm : ∀ i ∈ range q, ((2 * ((i * p + m : ℕ) : ℤ) + 1) ^ 2) =
              (p : ℤ) ^ 2 * ((2 * (i : ℤ) + 1) ^ 2) := by
            intro i _
            have hlin : (2 * ((i * p + m : ℕ) : ℤ) + 1) = (p : ℤ) * (2 * (i : ℤ) + 1) := by
              have : 2 * (i * p + m) + 1 = p * (2 * i + 1) := by nlinarith
              exact_mod_cast this
            rw [hlin, mul_pow]
          rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const,
            Finset.card_range, ← pow_mul]
        rw [hS_prod]; ring
      have hsplit_R : (∏ j ∈ range k, ((2 * (j : ℤ) + 1) ^ 2 - (2 * (m2 : ℤ) + 1) ^ 2)) =
          (p : ℤ) ^ (2 * q) * (∏ i ∈ range q, ((2 * (i : ℤ) + 1) ^ 2 - (p : ℤ) ^ 2)) *
          (∏ j ∈ range k \ S, ((2 * (j : ℤ) + 1) ^ 2 - (p : ℤ) ^ 4)) := by
        rw [← Finset.prod_sdiff hS_sub, Finset.prod_image hS_inj]
        have h2m2z : (2 * (m2 : ℤ) + 1) = (p : ℤ) ^ 2 := by exact_mod_cast h2m2
        have hS_prod : (∏ i ∈ range q, ((2 * ((i * p + m : ℕ) : ℤ) + 1) ^ 2 - (2 * (m2 : ℤ) + 1) ^ 2)) =
            (p : ℤ) ^ (2 * q) * (∏ i ∈ range q, ((2 * (i : ℤ) + 1) ^ 2 - (p : ℤ) ^ 2)) := by
          have hterm : ∀ i ∈ range q, ((2 * ((i * p + m : ℕ) : ℤ) + 1) ^ 2 - (2 * (m2 : ℤ) + 1) ^ 2) =
              (p : ℤ) ^ 2 * ((2 * (i : ℤ) + 1) ^ 2 - (p : ℤ) ^ 2) := by
            intro i _
            have hlin : (2 * ((i * p + m : ℕ) : ℤ) + 1) = (p : ℤ) * (2 * (i : ℤ) + 1) := by
              have : 2 * (i * p + m) + 1 = p * (2 * i + 1) := by nlinarith
              exact_mod_cast this
            rw [hlin, h2m2z]; ring
          rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const,
            Finset.card_range, ← pow_mul]
        have hT_prod : (∏ j ∈ range k \ S, ((2 * (j : ℤ) + 1) ^ 2 - (2 * (m2 : ℤ) + 1) ^ 2)) =
            (∏ j ∈ range k \ S, ((2 * (j : ℤ) + 1) ^ 2 - (p : ℤ) ^ 4)) := by
          apply Finset.prod_congr rfl
          intro j _
          rw [h2m2z]; ring
        rw [hS_prod, hT_prod]; ring
      rw [hsplit_L, hsplit_R] at hprod
      have hp2q_ne : ((p : ℤ) ^ (2 * q)) ≠ 0 := by positivity
      have hcancel_z : (∏ j ∈ range k \ S, ((2 * (j : ℤ) + 1) ^ 2)) *
            ((∏ i ∈ range q, ((2 * (i : ℤ) + 1) ^ 2)) *
              (((m2 + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k)) =
          (∏ j ∈ range k \ S, ((2 * (j : ℤ) + 1) ^ 2 - (p : ℤ) ^ 4)) *
            ((∏ i ∈ range q, ((2 * (i : ℤ) + 1) ^ 2 - (p : ℤ) ^ 2)) * ((2 * k).choose k : ℤ) ^ 3) := by
        apply mul_left_cancel₀ hp2q_ne
        linear_combination hprod
      have hcast := congr_arg (Int.castRingHom (ZMod (p ^ 3))) hcancel_z
      simp only [map_mul, map_prod, map_pow, map_sub, map_add, map_one, map_neg, map_ofNat,
        map_natCast] at hcast
      have hT_eq : (∏ j ∈ range k \ S, ((2 * (j : ZMod (p ^ 3)) + 1) ^ 2 - (p : ZMod (p ^ 3)) ^ 4)) =
          (∏ j ∈ range k \ S, ((2 * (j : ZMod (p ^ 3)) + 1) ^ 2)) := by
        apply Finset.prod_congr rfl
        intro j _
        have hp4z : (p : ZMod (p ^ 3)) ^ 4 = 0 := by
          rw [show (p : ZMod (p ^ 3)) ^ 4 = ((p ^ 3 : ℕ) : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) by
            push_cast; ring, ZMod.natCast_self, zero_mul]
        rw [hp4z, sub_zero]
      rw [hT_eq] at hcast
      have hT_unit : IsUnit (∏ j ∈ range k \ S, ((2 * (j : ZMod (p ^ 3)) + 1) ^ 2)) := by
        rw [IsUnit.prod_iff]
        intro j hj
        rw [Finset.mem_sdiff, Finset.mem_range] at hj
        refine (ZMod.isUnit_iff_coprime (2 * j + 1) (p ^ 3)).mpr ?_ |> fun h => by
          simpa [Nat.cast_add, Nat.cast_mul] using h.pow 2
        refine (hp_pr.coprime_iff_not_dvd.mpr (fun hd => ?_)).symm.pow_right 3
        rcases hd with ⟨t, ht⟩
        -- 2*j + 1 = p * t is odd, so t is odd: t = 2*i + 1
        have ht_odd : Odd t := by
          by_contra hev
          rw [Nat.not_odd_iff_even] at hev
          rcases hev with ⟨s, hs⟩
          rw [hs] at ht
          have : 2 * j + 1 = 2 * (p * s) := by linarith
          omega
        rcases ht_odd with ⟨i, rfl⟩
        have hj_eq : j = i * p + m := by nlinarith
        have hi_lt : i < q := by
          have : i * p + m < p * q + r := by omega
          by_contra hge
          have : q * p ≤ i * p := Nat.mul_le_mul_right p (by omega)
          nlinarith
        exact hj.2 (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi_lt, hj_eq.symm⟩)
      have hres := hT_unit.mul_left_cancel hcast
      simpa only [Mq, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_neg, Int.cast_ofNat] using hres
    -- Sum hterm_rel over r ∈ range (m + 1)
    have hsum_rel : Mq * (∑ r ∈ range (m + 1),
          (((m2 + (p * q + r)).choose (2 * (p * q + r)) : ℤ) *
            ((2 * (p * q + r)).choose (p * q + r) : ℤ) ^ 2 * (-16 : ℤ) ^ (p * q + r) : ZMod (p ^ 3))) =
        (∏ i ∈ range q, ((2 * (i : ZMod (p ^ 3)) + 1) ^ 2 - (p : ZMod (p ^ 3)) ^ 2)) *
          (∑ r ∈ range (m + 1), (((2 * (p * q + r)).choose (p * q + r) : ℕ) : ZMod (p ^ 3)) ^ 3) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl hterm_rel
    -- Show ∑ r ∈ range (m + 1), C(2*(p*q+r), p*q+r)^3 is divisible by p
    have hdvd_p_sum : p ∣ ∑ r ∈ range (m + 1), ((2 * (p * q + r)).choose (p * q + r)) ^ 3 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
      have hluc : ∀ r ∈ range (m + 1),
          ((((2 * (p * q + r)).choose (p * q + r)) ^ 3 : ℕ) : ZMod p) =
          (((2 * q).choose q : ℕ) : ZMod p) ^ 3 * (((2 * r).choose r : ℕ) : ZMod p) ^ 3 := by
        intro r hr
        rw [Finset.mem_range] at hr
        have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat
          (p := p) (n := 2 * (p * q + r)) (k := p * q + r)
        have h2r_lt : 2 * r < p := by omega
        have hr_lt : r < p := by omega
        have hn : 2 * (p * q + r) = p * (2 * q) + 2 * r := by ring
        have hmod1 : 2 * (p * q + r) % p = 2 * r := by
          rw [hn, Nat.mul_add_mod, Nat.mod_eq_of_lt h2r_lt]
        have hdiv1 : 2 * (p * q + r) / p = 2 * q := by
          rw [hn, Nat.mul_add_div hp_pos, Nat.div_eq_of_lt h2r_lt, add_zero]
        have hmod2 : (p * q + r) % p = r := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr_lt]
        have hdiv2 : (p * q + r) / p = q := by
          rw [Nat.mul_add_div hp_pos, Nat.div_eq_of_lt hr_lt, add_zero]
        rw [hmod1, hdiv1, hmod2, hdiv2] at hl
        have hmod : (((2 * (p * q + r)).choose (p * q + r) : ℕ) : ZMod p) =
            (((2 * r).choose r : ℕ) : ZMod p) * (((2 * q).choose q : ℕ) : ZMod p) := by
          exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ p).mpr hl
        rw [Nat.cast_pow, hmod, mul_pow, mul_comm]
      rw [Finset.sum_congr rfl hluc, ← Finset.mul_sum]
      have ha_dvd : p ∣ OeisA79727.a m := dvd_trans (dvd_pow_self p (by decide : 2 ≠ 0)) (dvd_a_half hp)
      have ha0 : (∑ r ∈ range (m + 1), (((2 * r).choose r : ℕ) : ZMod p) ^ 3) = 0 := by
        have := (ZMod.natCast_eq_zero_iff (OeisA79727.a m) p).mpr ha_dvd
        simpa [OeisA79727.a, Nat.cast_sum, Nat.cast_pow] using this
      rw [ha0, mul_zero]
    rcases prod_sub_p2_mod_p3 (p := p) q (fun i => (2 * (i : ZMod (p ^ 3)) + 1) ^ 2) with ⟨c, hc⟩
    rw [hc] at hsum_rel
    rcases hdvd_p_sum with ⟨s, hs⟩
    have hsum_p : (∑ r ∈ range (m + 1), (((2 * (p * q + r)).choose (p * q + r) : ℕ) : ZMod (p ^ 3)) ^ 3) =
        (p : ZMod (p ^ 3)) * (s : ZMod (p ^ 3)) := by
      have := congr_arg (Nat.cast (R := ZMod (p ^ 3))) hs
      simpa only [Nat.cast_sum, Nat.cast_pow, Nat.cast_mul] using this
    have herr_zero : (p : ZMod (p ^ 3)) ^ 2 * c *
        (∑ r ∈ range (m + 1), (((2 * (p * q + r)).choose (p * q + r) : ℕ) : ZMod (p ^ 3)) ^ 3) = 0 := by
      rw [hsum_p]
      have : (p : ZMod (p ^ 3)) ^ 2 * c * ((p : ZMod (p ^ 3)) * (s : ZMod (p ^ 3))) =
          ((p ^ 3 : ℕ) : ZMod (p ^ 3)) * (c * (s : ZMod (p ^ 3))) := by
        push_cast; ring
      rw [this, ZMod.natCast_self, zero_mul]
    rw [add_mul, herr_zero, add_zero] at hsum_rel
    exact hMq_unit.mul_left_cancel hsum_rel
  -- Step 4: Combine blocks to equate ∑_{k ≤ m2} clausenTerm = ∑_{k ≤ m2} C(2k, k)^3 in ZMod (p^3)
  have hsum_split : ∀ F : ℕ → ZMod (p ^ 3),
      (∀ q r, q ≤ m → m < r → r < p → F (p * q + r) = 0) →
      (∑ k ∈ range (m2 + 1), F k) = ∑ q ∈ range (m + 1), ∑ r ∈ range (m + 1), F (p * q + r) := by
    intro F hF0
    -- Extend range (m2 + 1) to range ((m + 1) * p) by adding zeros for q = m, m < r < p
    have hext : (∑ k ∈ range (m2 + 1), F k) = ∑ k ∈ range (p * (m + 1)), F k := by
      have hsub : range (m2 + 1) ⊆ range (p * (m + 1)) := by
        intro k hk
        rw [Finset.mem_range] at hk ⊢
        nlinarith
      rw [← Finset.sum_subset hsub]
      intro k hk hnot
      rw [Finset.mem_range] at hk hnot
      set r := k - p * m
      have hpm : p * (m + 1) = p * m + p := by ring
      have hk_eq : k = p * m + r := by omega
      rw [hk_eq]
      exact hF0 m r (le_refl m) (by omega) (by omega)
    rw [hext]
    -- Reindex range (p * (m + 1)) via (q, r) ↦ p * q + r
    have hblocks : (∑ k ∈ range (p * (m + 1)), F k) =
        ∑ q ∈ range (m + 1), ∑ r ∈ range p, F (p * q + r) := by
      clear hext hF0
      induction (m + 1) with
      | zero => simp
      | succ n ih =>
        rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    rw [hblocks]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mem_range] at hq
    have hsub : range (m + 1) ⊆ range p := by
      intro r hr
      rw [Finset.mem_range] at hr ⊢
      omega
    rw [← Finset.sum_subset hsub]
    intro r hr hnot
    rw [Finset.mem_range] at hr hnot
    exact hF0 q r (by omega) (by omega) hr
  have hlhs_eq := hsum_split
    (fun k => (((m2 + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k : ZMod (p ^ 3)))
    (fun q r hq hr1 hr2 => (hterm_gt_zero q r hq hr1 hr2).1)
  have hrhs_eq := hsum_split
    (fun k => (((2 * k).choose k : ℕ) : ZMod (p ^ 3)) ^ 3)
    (fun q r hq hr1 hr2 => (hterm_gt_zero q r hq hr1 hr2).2)
  have ha_eq : ((OeisA79727.a m2 : ℕ) : ZMod (p ^ 3)) = ((p ^ 2 : ℕ) : ZMod (p ^ 3)) := by
    rw [OeisA79727.a, Nat.cast_sum, Nat.cast_pow]
    simp_rw [Nat.cast_pow]
    rw [hrhs_eq, ← Finset.sum_congr rfl hblock_eq, ← hlhs_eq, hsum_re]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp ha_eq

private lemma choose_two_mul_dvd_p_of_range {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (k : ℕ) (hk1 : (p ^ 2 - 1) / 2 < k) (hk2 : k < p ^ 2) :
    p ∣ (2 * k).choose k := by
  set m := (p - 1) / 2
  have hp_pr : p.Prime := Fact.out
  have hp_pos : 0 < p := hp_pr.pos
  have hp_odd : Odd p := hp_pr.odd_of_ne_two hp2
  have h2m1 : 2 * m + 1 = p := by
    have := Nat.odd_iff.mp hp_odd
    omega
  have hm2_eq : (p ^ 2 - 1) / 2 = p * m + m := by
    have h2 : 2 * (p * m + m) + 1 = p ^ 2 := by nlinarith
    have hsq : 1 ≤ p ^ 2 := by nlinarith
    omega
  set q := k / p
  set r := k % p
  have hk_eq : k = p * q + r := (Nat.div_add_mod k p).symm
  have hr_lt : r < p := Nat.mod_lt k hp_pos
  have hq_lt : q < p := by
    by_contra hge
    have : p * p ≤ p * q := Nat.mul_le_mul_left p (by omega)
    nlinarith
  by_cases hrm : m < r
  · rw [hk_eq]
    exact choose_two_mul_dvd_p_of_gt_half p hp2 q r hrm hr_lt
  · have hqm : m < q := by
      by_contra hqle
      have : p * q ≤ p * m := Nat.mul_le_mul_left p (by omega)
      omega
    have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := 2 * k) (k := k)
    have h2r_lt : 2 * r < p := by omega
    have h2k : 2 * k = p * (2 * q) + 2 * r := by rw [hk_eq]; ring
    have hdiv_2k : 2 * k / p = 2 * q := by
      rw [h2k, Nat.mul_add_div hp_pos, Nat.div_eq_of_lt h2r_lt, add_zero]
    rw [hdiv_2k] at hl
    have hq_dvd : p ∣ (2 * q).choose q := by
      have := choose_two_mul_dvd_p_of_gt_half p hp2 0 q hqm hq_lt
      simpa using this
    rw [← ZMod.natCast_eq_zero_iff]
    have hmod : (((2 * k).choose k : ℕ) : ZMod p) =
        ((((2 * k) % p).choose (k % p) : ℕ) : ZMod p) * (((2 * q).choose q : ℕ) : ZMod p) := by
      exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ p).mpr hl
    rw [hmod, (ZMod.natCast_eq_zero_iff _ p).mpr hq_dvd, mul_zero]

private lemma conjecture2_proof (p : ℕ) (hp : OeisA3625.A p) :
    OeisA79727.a (p * (p - 1)) ≡ p ^ 2 [MOD p ^ 3] := by
  have : Fact p.Prime := ⟨hp.1⟩
  have hp2 : p ≠ 2 := A3625_ne_two hp
  have hp3 : 3 ≤ p := A3625_three_le hp
  set m2 := (p ^ 2 - 1) / 2
  have hm2_le : m2 ≤ p * (p - 1) := by
    have : p ^ 2 - 1 ≤ 2 * (p * (p - 1)) := by
      have h1 : 1 ≤ p := by omega
      zify [h1, (show 1 ≤ p ^ 2 by nlinarith)]
      nlinarith
    omega
  have hsub : range (m2 + 1) ⊆ range (p * (p - 1) + 1) :=
    Finset.range_mono (by omega)
  have htail : ((OeisA79727.a (p * (p - 1)) : ℕ) : ZMod (p ^ 3)) =
      ((OeisA79727.a m2 : ℕ) : ZMod (p ^ 3)) := by
    simp only [OeisA79727.a, Nat.cast_sum]
    symm
    apply Finset.sum_subset hsub
    intro k hk hnot
    rw [Finset.mem_range] at hk hnot
    have hk_lt : k < p ^ 2 := by
      have h1 : p * (p - 1) + 1 ≤ p ^ 2 := by
        zify [(show 1 ≤ p by omega)]
        nlinarith
      omega
    have hd : p ∣ (2 * k).choose k := choose_two_mul_dvd_p_of_range hp2 k (by omega) hk_lt
    rcases hd with ⟨t, ht⟩
    rw [ht, mul_pow, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hmod_m2 : ((OeisA79727.a m2 : ℕ) : ZMod (p ^ 3)) = ((p ^ 2 : ℕ) : ZMod (p ^ 3)) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr (a_m2_mod_p3 hp)
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (htail.trans hmod_m2)

end OeisA79727Conjecture2

theorem OMA.solution : type_of% @OeisA79727.conjecture2 := by
  intro p hp
  exact OeisA79727Conjecture2.conjecture2_proof p hp
