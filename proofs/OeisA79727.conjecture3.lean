import FormalConjectures.OEIS.«79727»
import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Proof of Peter Bala's mod `p^4` supercongruence for OEIS A079727

For any prime `p` in OEIS A003625 (`p ≡ 3, 5, 6 (mod 7)`), we prove
`a ((p^2 - 1) / 2) ≡ p^2 [MOD p^4]`.
-/

open scoped BigOperators
open Polynomial Finset Nat

namespace OeisA79727Conjecture3

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


/- ### Section 6: General Schur congruence for `shiftedLegendre (q * p + m)` -/

private lemma coeff_comp_X_pow_mul_of_deg_lt' {R : Type*} [CommRing R] {p : ℕ} (hp : 0 < p)
    (P Q : R[X]) (hQ : Q.natDegree < p) (a b : ℕ) (hb : b < p) :
    (P.comp (X ^ p) * Q).coeff (p * a + b) = P.coeff a * Q.coeff b := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hcomp_mul : ∀ t : ℕ, (P.comp (X ^ p)).coeff (p * t) = P.coeff t := by
    intro t
    rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def, Polynomial.finsetSum_coeff]
    have ht : ∀ i ∈ P.support,
        (C (P.coeff i) * (X ^ p : R[X]) ^ i).coeff (p * t) = if i = t then P.coeff t else 0 := by
      intro i _
      rw [← pow_mul, Polynomial.coeff_C_mul_X_pow]
      by_cases h : i = t
      · subst h; simp
      · have hne : p * t ≠ p * i := fun heq => h (Nat.eq_of_mul_eq_mul_left hp heq).symm
        simp [h, hne]
    rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · exact (Polynomial.notMem_support_iff.mp hmem).symm
  have hcomp_ndvd : ∀ i : ℕ, ¬ (p ∣ i) → (P.comp (X ^ p)).coeff i = 0 := by
    intro i hi
    rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def, Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro j _
    rw [← pow_mul, Polynomial.coeff_C_mul_X_pow, if_neg]
    intro heq
    exact hi ⟨j, heq⟩
  have hterm : ∀ i ∈ range (p * a + b + 1),
      (P.comp (X ^ p)).coeff i * Q.coeff (p * a + b - i) =
      if i = p * a then P.coeff a * Q.coeff b else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases heq : i = p * a
    · subst heq
      rw [if_pos rfl, Nat.add_sub_cancel_left, hcomp_mul]
    · rw [if_neg heq]
      by_cases hdiv : p ∣ i
      · rcases hdiv with ⟨t, rfl⟩
        have hlt : t < a := by
          have : t ≠ a := fun h => heq (by rw [h])
          by_contra hge
          have : p * (a + 1) ≤ p * t := Nat.mul_le_mul_left p (by omega)
          nlinarith
        have hbig : Q.natDegree < p * a + b - p * t := by
          have h1 : p * (t + 1) ≤ p * a := Nat.mul_le_mul_left p (by omega)
          have h2 : p * t + p ≤ p * a := by linarith
          omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hbig, mul_zero]
      · rw [hcomp_ndvd i hdiv, zero_mul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]

private lemma choose_mul_choose_eq_two_mul (n k : ℕ) :
    n.choose k * (n + k).choose n = (n + k).choose (2 * k) * (2 * k).choose k := by
  by_cases h : k ≤ n
  · have h1 := Nat.choose_mul_factorial_mul_factorial h
    have h2 := Nat.choose_mul_factorial_mul_factorial (show n ≤ n + k by omega)
    have h3 := Nat.choose_mul_factorial_mul_factorial (show 2 * k ≤ n + k by omega)
    have h4 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
    rw [show n + k - n = k by omega] at h2
    rw [show n + k - 2 * k = n - k by omega] at h3
    rw [show 2 * k - k = k by omega] at h4
    have hpos : 0 < k.factorial * (n - k).factorial * (n.factorial * k.factorial) * (2 * k).factorial := by
      positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc n.choose k * (n + k).choose n *
            (k.factorial * (n - k).factorial * (n.factorial * k.factorial) * (2 * k).factorial)
        = (n.choose k * k.factorial * (n - k).factorial) *
            ((n + k).choose n * n.factorial * k.factorial) * (2 * k).factorial := by ring
      _ = n.factorial * (n + k).factorial * (2 * k).factorial := by rw [h1, h2]
      _ = ((n + k).choose (2 * k) * (2 * k).factorial * (n - k).factorial) *
            ((2 * k).choose k * k.factorial * k.factorial) * n.factorial := by rw [h3, h4]; ring
      _ = (n + k).choose (2 * k) * (2 * k).choose k *
            (k.factorial * (n - k).factorial * (n.factorial * k.factorial) * (2 * k).factorial) := by ring
  · rw [Nat.choose_eq_zero_of_lt (by omega : n < k),
      Nat.choose_eq_zero_of_lt (by omega : n + k < 2 * k), zero_mul, zero_mul]

private lemma shiftedLegendre_coeff_all (n k : ℕ) :
    (shiftedLegendre n).coeff k =
      (-1 : ℤ) ^ k * ((n + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) := by
  rw [coeff_shiftedLegendre, mul_assoc, ← Nat.cast_mul, choose_mul_choose_eq_two_mul,
    Nat.cast_mul, ← mul_assoc]

private lemma shiftedLegendre_block_mod_p {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (q : ℕ) (_hq : q < p) :
    (shiftedLegendre (q * p + (p - 1) / 2)).map (Int.castRingHom (ZMod p)) =
      ((shiftedLegendre q).map (Int.castRingHom (ZMod p))).comp (X ^ p) *
        ((shiftedLegendre ((p - 1) / 2)).map (Int.castRingHom (ZMod p))) := by
  set m := (p - 1) / 2
  have hp_pr : p.Prime := Fact.out
  have hp_pos : 0 < p := hp_pr.pos
  have hp_odd : Odd p := hp_pr.odd_of_ne_two hp2
  have h2m1 : 2 * m + 1 = p := by
    have := Nat.odd_iff.mp hp_odd
    omega
  have hm_deg : ((shiftedLegendre m).map (Int.castRingHom (ZMod p))).natDegree < p := by
    have h1 := Polynomial.natDegree_map_le (f := Int.castRingHom (ZMod p)) (p := shiftedLegendre m)
    rw [natDegree_shiftedLegendre] at h1
    omega
  ext k
  set a := k / p
  set b := k % p
  have hb : b < p := Nat.mod_lt k hp_pos
  have hk_eq : k = p * a + b := (Nat.div_add_mod k p).symm
  rw [hk_eq, coeff_comp_X_pow_mul_of_deg_lt' hp_pos _ _ hm_deg a b hb]
  rw [Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.coeff_map]
  simp only [shiftedLegendre_coeff_all, map_mul, map_pow, map_neg, map_one, map_natCast]
  by_cases hbm : b ≤ m
  · have h2b_lt : 2 * b < p := by omega
    have hmb_lt : m + b < p := by omega
    have hluc1 := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (p := p) (n := 2 * (p * a + b)) (k := p * a + b)
    have hn1 : 2 * (p * a + b) = p * (2 * a) + 2 * b := by ring
    have hm1 : 2 * (p * a + b) % p = 2 * b := by rw [hn1, Nat.mul_add_mod, Nat.mod_eq_of_lt h2b_lt]
    have hd1 : 2 * (p * a + b) / p = 2 * a := by
      rw [hn1, Nat.mul_add_div hp_pos, Nat.div_eq_of_lt h2b_lt, add_zero]
    have hk1_m : (p * a + b) % p = b := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
    have hk1_d : (p * a + b) / p = a := by
      rw [Nat.mul_add_div hp_pos, Nat.div_eq_of_lt hb, add_zero]
    rw [hm1, hd1, hk1_m, hk1_d] at hluc1
    have hc1 : (((2 * (p * a + b)).choose (p * a + b) : ℕ) : ZMod p) =
        (((2 * b).choose b : ℕ) : ZMod p) * (((2 * a).choose a : ℕ) : ZMod p) := by
      have := (ZMod.natCast_eq_natCast_iff _ _ p).mpr hluc1
      simpa only [Nat.cast_mul] using this
    have hluc2 := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (p := p) (n := q * p + m + (p * a + b)) (k := 2 * (p * a + b))
    have hn2 : q * p + m + (p * a + b) = p * (q + a) + (m + b) := by ring
    have hm2 : (q * p + m + (p * a + b)) % p = m + b := by
      rw [hn2, Nat.mul_add_mod, Nat.mod_eq_of_lt hmb_lt]
    have hd2 : (q * p + m + (p * a + b)) / p = q + a := by
      rw [hn2, Nat.mul_add_div hp_pos, Nat.div_eq_of_lt hmb_lt, add_zero]
    rw [hm2, hd2, hm1, hd1] at hluc2
    have hc2 : (((q * p + m + (p * a + b)).choose (2 * (p * a + b)) : ℕ) : ZMod p) =
        (((m + b).choose (2 * b) : ℕ) : ZMod p) * (((q + a).choose (2 * a) : ℕ) : ZMod p) := by
      have := (ZMod.natCast_eq_natCast_iff _ _ p).mpr hluc2
      simpa only [Nat.cast_mul] using this
    have hsign : (-1 : ZMod p) ^ (p * a + b) = (-1 : ZMod p) ^ a * (-1 : ZMod p) ^ b := by
      rw [pow_add, pow_mul, Odd.neg_one_pow hp_odd]
    rw [hsign, hc1, hc2]; ring
  · have hbm_gt : m < b := by omega
    have hlt_mb : m + b < 2 * b := by omega
    rw [Nat.choose_eq_zero_of_lt hlt_mb]
    have hd : p ∣ (2 * (p * a + b)).choose (p * a + b) :=
      choose_two_mul_dvd_p_of_gt_half p hp2 a b hbm_gt hb
    have hz : (((2 * (p * a + b)).choose (p * a + b) : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ p).mpr hd
    simp [hz]

private lemma shiftedLegendre_block_eval_x0_eq_zero {p : ℕ} [Fact p.Prime] (hp : OeisA3625.A p)
    (q : ℕ) (hq : q < p) :
    aeval (ZOmega.x0 : ZOmega (ZMod p)) (shiftedLegendre (q * p + (p - 1) / 2)) = 0 := by
  have hp2 : p ≠ 2 := A3625_ne_two hp
  have hpoly := shiftedLegendre_block_mod_p hp2 q hq
  have heval_comm : ∀ f : ℤ[X],
      aeval (ZOmega.x0 : ZOmega (ZMod p)) f =
        Polynomial.eval₂ (ZOmega.of : ZMod p →+* ZOmega (ZMod p)) ZOmega.x0
          (f.map (Int.castRingHom (ZMod p))) := by
    intro f
    rw [aeval_def, Polynomial.eval₂_map]
    congr 1
    ext
    simp [ZOmega.of]
  rw [heval_comm, hpoly, Polynomial.eval₂_mul, ← heval_comm,
    shiftedLegendre_eval_x0_eq_zero hp, mul_zero]

/- ### Section 7: Three-term Legendre recurrence and formal power series `g, y, f` -/

private lemma ZOmega.nsmul_re {R : Type*} [CommRing R] (n : ℕ) (x : ZOmega R) :
    (n • x).re = n • x.re := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, ZOmega.add_re, ih]

private lemma ZOmega.nsmul_im {R : Type*} [CommRing R] (n : ℕ) (x : ZOmega R) :
    (n • x).im = n • x.im := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, ZOmega.add_im, ih]

instance ZOmega.instIsAddTorsionFree {R : Type*} [CommRing R] [IsAddTorsionFree R] :
    IsAddTorsionFree (ZOmega R) where
  nsmul_right_injective n hn a b hab := by
    apply ZOmega.ext
    · exact nsmul_right_injective hn (by simpa [ZOmega.nsmul_re] using congr_arg ZOmega.re hab)
    · exact nsmul_right_injective hn (by simpa [ZOmega.nsmul_im] using congr_arg ZOmega.im hab)

private lemma ZOmega.mapRingHom_injective {R S : Type*} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (ZOmega.mapRingHom f) := by
  intro a b hab
  exact ZOmega.ext (hf (congr_arg ZOmega.re hab)) (hf (congr_arg ZOmega.im hab))

private lemma shiftedLegendre_three_term_aux (m k : ℕ) :
    (k + 1) ^ 2 * ((m + (k + 1)).choose (2 * (k + 1)) * (2 * (k + 1)).choose (k + 1)) =
      (m + k + 1) * (m - k) * ((m + k).choose (2 * k) * (2 * k).choose k) := by
  by_cases hkm : k ≤ m
  · have hch1 : (2 * k + 2) * (2 * k + 1) * (m + k + 1).choose (2 * k + 2) =
        (m + k + 1) * (m - k) * (m + k).choose (2 * k) := by
      have e1 := Nat.add_one_mul_choose_eq (m + k) (2 * k + 1)
      have e2 := Nat.choose_succ_right_eq (m + k) (2 * k)
      have hsub : m + k - 2 * k = m - k := by omega
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
    rw [show m + (k + 1) = m + k + 1 by omega, show 2 * (k + 1) = 2 * k + 2 by omega]
    have hpos : 0 < 2 * (2 * k + 1) := by omega
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc 2 * (2 * k + 1) * ((k + 1) ^ 2 * ((m + k + 1).choose (2 * k + 2) * (2 * k + 2).choose (k + 1)))
        = ((2 * k + 2) * (2 * k + 1) * (m + k + 1).choose (2 * k + 2)) *
            ((k + 1) * (2 * k + 2).choose (k + 1)) := by ring
      _ = ((m + k + 1) * (m - k) * (m + k).choose (2 * k)) *
            (2 * (2 * k + 1) * (2 * k).choose k) := by rw [hch1, hch2]
      _ = 2 * (2 * k + 1) * ((m + k + 1) * (m - k) * ((m + k).choose (2 * k) * (2 * k).choose k)) := by ring
  · have hsub : m - k = 0 := Nat.sub_eq_zero_of_le (by omega)
    have hlt : m + (k + 1) < 2 * (k + 1) := by omega
    rw [hsub, Nat.choose_eq_zero_of_lt hlt]
    simp

private lemma shiftedLegendre_choose_shift (m j : ℕ) (hjm : j ≤ m) :
    (m + 1 - j) * (m + 1 + j).choose (2 * j) = (m + 1 + j) * (m + j).choose (2 * j) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (by omega : 2 * j ≤ m + 1 + j)
  have h2 := Nat.choose_mul_factorial_mul_factorial (by omega : 2 * j ≤ m + j)
  have hsub1 : m + 1 + j - 2 * j = (m - j) + 1 := by omega
  have hsub2 : m + j - 2 * j = m - j := by omega
  rw [hsub1, Nat.factorial_succ] at h1
  rw [hsub2] at h2
  have hfac : (m + 1 + j).factorial = (m + 1 + j) * (m + j).factorial := by
    rw [show m + 1 + j = (m + j) + 1 by omega, Nat.factorial_succ]
  rw [hfac] at h1
  have hpos : 0 < (2 * j).factorial * (m - j).factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  apply Nat.eq_of_mul_eq_mul_right hpos
  have hlin : m + 1 - j = m - j + 1 := by omega
  rw [hlin]
  nlinarith

private lemma shiftedLegendre_three_term (n : ℕ) :
    C ((n : ℤ) + 2) * shiftedLegendre (n + 2) =
      C (2 * (n : ℤ) + 3) * (1 - 2 * X) * shiftedLegendre (n + 1) -
        C ((n : ℤ) + 1) * shiftedLegendre n := by
  ext k
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    mul_assoc, Polynomial.coeff_C_mul]
  have h12x : ∀ (f : ℤ[X]) (j : ℕ),
      ((1 - 2 * X) * f).coeff j = f.coeff j - if j = 0 then 0 else 2 * f.coeff (j - 1) := by
    intro f j
    rw [sub_mul, one_mul, Polynomial.coeff_sub, mul_assoc, Polynomial.coeff_ofNat_mul]
    cases j with
    | zero => simp
    | succ j => simp [Polynomial.coeff_X_mul]
  rw [h12x]
  cases k with
  | zero =>
    simp [shiftedLegendre_coeff_all]
    ring
  | succ k =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    simp only [shiftedLegendre_coeff_all]
    set c : ℕ → ℕ → ℤ := fun m j => ((m + j).choose (2 * j) : ℤ) * ((2 * j).choose j : ℤ)
    have hpow : (-1 : ℤ) ^ (k + 1) = -((-1 : ℤ) ^ k) := by rw [pow_succ]; ring
    have hgoal : ((n : ℤ) + 2) * c (n + 2) (k + 1) =
        (2 * (n : ℤ) + 3) * (c (n + 1) (k + 1) + 2 * c (n + 1) k) -
          ((n : ℤ) + 1) * c n (k + 1) := by
      by_cases hkn : k + 1 ≤ n
      · have h1 := shiftedLegendre_choose_shift (n + 1) (k + 1) (by omega)
        have h2 := shiftedLegendre_choose_shift n (k + 1) hkn
        have h3 := shiftedLegendre_three_term_aux (n + 1) k
        have hz1 : ((n : ℤ) + 1 - k) * c (n + 2) (k + 1) =
            ((n : ℤ) + k + 3) * c (n + 1) (k + 1) := by
          have := congr_arg (fun t : ℕ => (t : ℤ) * ((2 * (k + 1)).choose (k + 1) : ℤ)) h1
          dsimp only [c]
          rw [show n + 1 + 1 - (k + 1) = n + 1 - k by omega,
            show n + 1 + 1 + (k + 1) = n + 2 + (k + 1) by omega] at this
          push_cast [Nat.cast_sub (by omega : k ≤ n + 1)] at this
          linear_combination this
        have hz2 : ((n : ℤ) - k) * c (n + 1) (k + 1) =
            ((n : ℤ) + k + 2) * c n (k + 1) := by
          have := congr_arg (fun t : ℕ => (t : ℤ) * ((2 * (k + 1)).choose (k + 1) : ℤ)) h2
          dsimp only [c]
          rw [show n + 1 - (k + 1) = n - k by omega] at this
          push_cast [Nat.cast_sub (by omega : k ≤ n)] at this
          linear_combination this
        have hz3 : ((k : ℤ) + 1) ^ 2 * c (n + 1) (k + 1) =
            ((n : ℤ) + k + 2) * ((n : ℤ) + 1 - k) * c (n + 1) k := by
          have := congr_arg (Nat.cast (R := ℤ)) h3
          dsimp only [c]
          push_cast [Nat.cast_sub (by omega : k ≤ n + 1)] at this
          linear_combination this
        have hne : (((n : ℤ) + 1 - k) * ((n : ℤ) + k + 2)) ≠ 0 := by
          have hpos1 : (0 : ℤ) < (n : ℤ) + 1 - k := by omega
          have hpos2 : (0 : ℤ) < (n : ℤ) + k + 2 := by omega
          positivity
        apply mul_left_cancel₀ hne
        linear_combination
          ((n : ℤ) + 2) * ((n : ℤ) + k + 2) * hz1
          - ((n : ℤ) + 1) * ((n : ℤ) + 1 - k) * hz2
          + 2 * (2 * (n : ℤ) + 3) * hz3
      · by_cases hk1 : k = n
        · subst hk1
          have hc0 : c k (k + 1) = 0 := by
            dsimp only [c]
            rw [Nat.choose_eq_zero_of_lt (by omega : k + (k + 1) < 2 * (k + 1))]
            simp
          have h1 := shiftedLegendre_choose_shift (k + 1) (k + 1) le_rfl
          have h3 := shiftedLegendre_three_term_aux (k + 1) k
          have hz1 : c (k + 2) (k + 1) = (2 * (k : ℤ) + 3) * c (k + 1) (k + 1) := by
            have := congr_arg (fun t : ℕ => (t : ℤ) * ((2 * (k + 1)).choose (k + 1) : ℤ)) h1
            dsimp only [c]
            rw [show k + 1 + 1 - (k + 1) = 1 by omega,
              show k + 1 + 1 + (k + 1) = k + 2 + (k + 1) by omega] at this
            push_cast at this
            linear_combination this
          have hz3 : ((k : ℤ) + 1) ^ 2 * c (k + 1) (k + 1) =
              (2 * (k : ℤ) + 2) * c (k + 1) k := by
            have := congr_arg (Nat.cast (R := ℤ)) h3
            dsimp only [c]
            rw [show k + 1 - k = 1 by omega] at this
            push_cast at this
            linear_combination this
          rw [hc0, hz1]
          have hne : (2 * (k : ℤ) + 2) ≠ 0 := by positivity
          apply mul_left_cancel₀ hne
          linear_combination 2 * (2 * (k : ℤ) + 3) * hz3
        · by_cases hk2 : k = n + 1
          · subst hk2
            have hc0 : c n (n + 2) = 0 := by
              dsimp only [c]
              rw [Nat.choose_eq_zero_of_lt (by omega : n + (n + 2) < 2 * (n + 2))]
              simp
            have hc1 : c (n + 1) (n + 2) = 0 := by
              dsimp only [c]
              rw [Nat.choose_eq_zero_of_lt (by omega : n + 1 + (n + 2) < 2 * (n + 2))]
              simp
            have hch2 : (n + 2) * (2 * (n + 2)).choose (n + 2) =
                2 * (2 * n + 3) * (2 * (n + 1)).choose (n + 1) := by
              have e1 := Nat.add_one_mul_choose_eq (2 * n + 3) (n + 1)
              have e2 := Nat.choose_succ_right_eq (2 * n + 3) (n + 1)
              have e3 := Nat.add_one_mul_choose_eq (2 * n + 2) (n + 1)
              have hsub : 2 * n + 3 - (n + 1) = n + 2 := by omega
              rw [hsub] at e2
              have e4 : (2 * n + 3).choose (n + 1) = (2 * n + 3).choose (n + 2) :=
                Nat.choose_symm_of_eq_add (by omega : 2 * n + 3 = (n + 1) + (n + 2))
              rw [show 2 * (n + 2) = 2 * n + 4 by omega, show 2 * (n + 1) = 2 * n + 2 by omega]
              nlinarith
            rw [hc0, hc1]
            dsimp only [c]
            rw [show n + 2 + (n + 1 + 1) = 2 * (n + 1 + 1) by omega,
              show n + 1 + (n + 1) = 2 * (n + 1) by omega,
              Nat.choose_self, Nat.choose_self]
            have := congr_arg (Nat.cast (R := ℤ)) hch2
            push_cast at this ⊢
            linear_combination this
          · have hc0 : c n (k + 1) = 0 := by
              dsimp only [c]; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
            have hc1 : c (n + 1) (k + 1) = 0 := by
              dsimp only [c]; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
            have hc2 : c (n + 1) k = 0 := by
              dsimp only [c]; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
            have hc3 : c (n + 2) (k + 1) = 0 := by
              dsimp only [c]; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
            rw [hc0, hc1, hc2, hc3]; ring
    calc ((n : ℤ) + 2) * ((-1 : ℤ) ^ (k + 1) * ((n + 2 + (k + 1)).choose (2 * (k + 1)) : ℤ) *
            ((2 * (k + 1)).choose (k + 1) : ℤ))
        = (-1 : ℤ) ^ (k + 1) * (((n : ℤ) + 2) * c (n + 2) (k + 1)) := by dsimp only [c]; ring
      _ = (-1 : ℤ) ^ (k + 1) * ((2 * (n : ℤ) + 3) * (c (n + 1) (k + 1) + 2 * c (n + 1) k) -
            ((n : ℤ) + 1) * c n (k + 1)) := by rw [hgoal]
      _ = (2 * (n : ℤ) + 3) * ((-1 : ℤ) ^ (k + 1) * ((n + 1 + (k + 1)).choose (2 * (k + 1)) : ℤ) *
            ((2 * (k + 1)).choose (k + 1) : ℤ) -
            2 * ((-1 : ℤ) ^ k * ((n + 1 + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ))) -
          ((n : ℤ) + 1) * ((-1 : ℤ) ^ (k + 1) * ((n + (k + 1)).choose (2 * (k + 1)) : ℤ) *
            ((2 * (k + 1)).choose (k + 1) : ℤ)) := by
            rw [hpow]; dsimp only [c]; ring

/- ### Section 8: Jacobi quartic multiplication polynomials and `L_{m2}(x0) ≡ (-1)^m p (mod p^3)` -/

private def z0 {R : Type*} [CommRing R] : ZOmega R := 1 - 2 * ZOmega.x0

private noncomputable def Qpoly (z : ZOmega ℤ) : (ZOmega ℤ)[X] :=
  1 - C (2 * z) * X ^ 2 + X ^ 4

private lemma Qpoly_eval_zero (z : ZOmega ℤ) : (Qpoly z).eval 0 = 1 := by
  simp [Qpoly]

private lemma Qpoly_natDegree_le (z : ZOmega ℤ) : (Qpoly z).natDegree ≤ 4 := by
  unfold Qpoly
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ (le_trans (Polynomial.natDegree_X_pow_le 4) le_rfl))
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le (by simp) ?_)
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  exact le_trans (Polynomial.natDegree_X_pow_le 2) (by omega)

private lemma Qpoly_reflect (z : ZOmega ℤ) : (Qpoly z).reflect 4 = Qpoly z := by
  ext k
  rw [Polynomial.coeff_reflect]
  unfold Qpoly
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_one,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_X_pow]
  rcases k with _ | _ | _ | _ | _ | k
  · simp [Polynomial.revAt_le]
  · simp [Polynomial.revAt_le]
  · simp [Polynomial.revAt_le]
  · simp [Polynomial.revAt_le]
  · simp [Polynomial.revAt_le]
  · rw [Polynomial.revAt_eq_self_of_lt (by omega : 4 < k + 5)]

private lemma Qpoly_comp_neg_X (z : ZOmega ℤ) : (Qpoly z).comp (-X) = Qpoly z := by
  unfold Qpoly
  simp only [Polynomial.add_comp, Polynomial.sub_comp, Polynomial.one_comp,
    Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp]
  ring

private noncomputable def legVal (n : ℕ) : ZOmega ℤ := aeval (ZOmega.x0 : ZOmega ℤ) (shiftedLegendre n)

private lemma legVal_zero : legVal 0 = 1 := by
  have h0 : shiftedLegendre 0 = 1 := by
    ext k
    rw [shiftedLegendre_coeff_all, Polynomial.coeff_one]
    cases k with
    | zero => simp
    | succ k =>
      rw [Nat.choose_eq_zero_of_lt (by omega : 0 + (k + 1) < 2 * (k + 1))]
      simp
  simp [legVal, h0]

private lemma legVal_one : legVal 1 = z0 := by
  have h1 : shiftedLegendre 1 = 1 - 2 * X := by
    ext k
    rw [shiftedLegendre_coeff_all, Polynomial.coeff_sub, Polynomial.coeff_one,
      Polynomial.coeff_ofNat_mul, Polynomial.coeff_X]
    rcases k with _ | _ | k
    · simp
    · simp
    · rw [Nat.choose_eq_zero_of_lt (by omega : 1 + (k + 2) < 2 * (k + 2))]
      simp
  rw [legVal, h1, map_sub, map_one, map_mul, map_ofNat, aeval_X]
  rfl

private lemma legVal_three_term (n : ℕ) :
    ((n : ZOmega ℤ) + 2) * legVal (n + 2) =
      (2 * (n : ZOmega ℤ) + 3) * z0 * legVal (n + 1) - ((n : ZOmega ℤ) + 1) * legVal n := by
  have h := congr_arg (aeval (ZOmega.x0 : ZOmega ℤ)) (shiftedLegendre_three_term n)
  simp only [map_sub, map_mul, map_add, map_one, map_natCast, map_ofNat, aeval_X] at h
  simpa only [legVal, z0] using h

private noncomputable def legSeriesG : PowerSeries (ZOmega ℤ) :=
  PowerSeries.mk fun k => if k % 2 = 0 then legVal (k / 2) else 0

private lemma legSeriesG_coeff_even (n : ℕ) :
    PowerSeries.coeff (2 * n) legSeriesG = legVal n := by
  simp [legSeriesG]

private lemma legSeriesG_coeff_odd (n : ℕ) :
    PowerSeries.coeff (2 * n + 1) legSeriesG = 0 := by
  simp [legSeriesG]

private lemma legSeriesG_constantCoeff : PowerSeries.constantCoeff legSeriesG = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  have h := legSeriesG_coeff_even 0
  rw [mul_zero, legVal_zero] at h
  exact h

private lemma Qpoly_mul_deriv_legSeriesG :
    ((Qpoly z0 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) *
        PowerSeries.derivative (ZOmega ℤ) legSeriesG =
      (PowerSeries.C (2 * z0) * PowerSeries.X - 2 * PowerSeries.X ^ 3) * legSeriesG := by
  have hQ : ((Qpoly z0 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) =
      1 - PowerSeries.C (2 * z0) * PowerSeries.X ^ 2 + PowerSeries.X ^ 4 := by
    simp [Qpoly]
  rw [hQ]
  ext k
  have hcoeff_X_mul : ∀ (s : PowerSeries (ZOmega ℤ)) (j : ℕ),
      PowerSeries.coeff j (PowerSeries.X * s) = if j = 0 then 0 else PowerSeries.coeff (j - 1) s := by
    intro s j
    cases j with
    | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
    | succ j => simp [PowerSeries.coeff_succ_X_mul]
  have hcoeff_Xpow : ∀ (m : ℕ) (s : PowerSeries (ZOmega ℤ)) (j : ℕ),
      PowerSeries.coeff j (PowerSeries.X ^ m * s) =
        if m ≤ j then PowerSeries.coeff (j - m) s else 0 := by
    intro m s j
    induction m generalizing j with
    | zero => simp
    | succ m ih =>
      rw [_root_.pow_succ', mul_assoc, hcoeff_X_mul]
      cases j with
      | zero => simp
      | succ j =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, ih, Nat.succ_le_succ_iff,
          Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
  simp only [add_mul, sub_mul, one_mul, map_add, map_sub, mul_assoc, PowerSeries.coeff_C_mul]
  rw [show (2 : PowerSeries (ZOmega ℤ)) * (PowerSeries.X ^ 3 * legSeriesG) =
      PowerSeries.C (2 : ZOmega ℤ) * (PowerSeries.X ^ 3 * legSeriesG) by rw [map_ofNat],
    PowerSeries.coeff_C_mul]
  rw [hcoeff_Xpow 2, hcoeff_Xpow 4, hcoeff_X_mul, hcoeff_Xpow 3]
  simp only [PowerSeries.coeff_derivative]
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [show m + m = 2 * m by ring]
    have h0 : PowerSeries.coeff (2 * m + 1) legSeriesG = 0 := legSeriesG_coeff_odd m
    rw [h0, zero_mul]
    have h2 : (if 2 ≤ 2 * m then PowerSeries.coeff (2 * m - 2 + 1) legSeriesG * ((2 * m - 2 : ℕ) + 1) else 0) = 0 := by
      split_ifs with hle
      · rw [show 2 * m - 2 + 1 = 2 * (m - 1) + 1 by omega, legSeriesG_coeff_odd, zero_mul]
      · rfl
    have h4 : (if 4 ≤ 2 * m then PowerSeries.coeff (2 * m - 4 + 1) legSeriesG * ((2 * m - 4 : ℕ) + 1) else 0) = 0 := by
      split_ifs with hle
      · rw [show 2 * m - 4 + 1 = 2 * (m - 2) + 1 by omega, legSeriesG_coeff_odd, zero_mul]
      · rfl
    have h1 : (if 2 * m = 0 then 0 else PowerSeries.coeff (2 * m - 1) legSeriesG) = 0 := by
      split_ifs with hz
      · rfl
      · rw [show 2 * m - 1 = 2 * (m - 1) + 1 by omega, legSeriesG_coeff_odd]
    have h3 : (if 3 ≤ 2 * m then PowerSeries.coeff (2 * m - 3) legSeriesG else 0) = 0 := by
      split_ifs with hle
      · rw [show 2 * m - 3 = 2 * (m - 2) + 1 by omega, legSeriesG_coeff_odd]
      · rfl
    rw [h2, h4, h1, h3]; ring
  · rcases m with _ | _ | n
    · simp only [mul_zero, zero_add, show ¬(2 ≤ 1) by omega, show ¬(4 ≤ 1) by omega,
        show ¬(3 ≤ 1) by omega, show (1 : ℕ) ≠ 0 by omega, ↓reduceIte, Nat.sub_self,
        mul_zero, sub_zero, add_zero]
      have hg0 : PowerSeries.coeff 0 legSeriesG = 1 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff, legSeriesG_constantCoeff]
      have hg2 : PowerSeries.coeff (1 + 1) legSeriesG = z0 := by
        rw [show (1 + 1 : ℕ) = 2 * 1 by rfl, legSeriesG_coeff_even, legVal_one]
      rw [hg2, hg0]; push_cast; ring
    · have h3t := legVal_three_term 0
      simp only [Nat.cast_zero, zero_add, mul_zero] at h3t
      have h21 : 2 * 1 + 1 + 1 = 2 * 2 := by omega
      have h22 : 2 * 1 + 1 - 2 + 1 = 2 * 1 := by omega
      have h23 : 2 * 1 + 1 - 1 = 2 * 1 := by omega
      have h24 : 2 * 1 + 1 - 3 = 2 * 0 := by omega
      simp only [show ¬(4 ≤ 2 * 1 + 1) by omega, show (2 ≤ 2 * 1 + 1) by omega,
        show (3 ≤ 2 * 1 + 1) by omega, show (2 * 1 + 1 ≠ 0) by omega, ↓reduceIte]
      rw [h21, h22, h23, h24, legSeriesG_coeff_even, legSeriesG_coeff_even,
        legSeriesG_coeff_even]
      norm_num
      linear_combination 2 * h3t
    · have h3t := legVal_three_term (n + 1)
      have he1 : 2 * (n + 2) + 1 + 1 = 2 * (n + 3) := by omega
      have he2 : 2 * (n + 2) + 1 - 2 + 1 = 2 * (n + 2) := by omega
      have he3 : 2 * (n + 2) + 1 - 4 + 1 = 2 * (n + 1) := by omega
      have he4 : 2 * (n + 2) + 1 - 1 = 2 * (n + 2) := by omega
      have he5 : 2 * (n + 2) + 1 - 3 = 2 * (n + 1) := by omega
      simp only [show (2 ≤ 2 * (n + 2) + 1) by omega, show (4 ≤ 2 * (n + 2) + 1) by omega,
        show (3 ≤ 2 * (n + 2) + 1) by omega, show (2 * (n + 2) + 1 ≠ 0) by omega, ↓reduceIte]
      rw [he1, he2, he3, he4, he5, legSeriesG_coeff_even, legSeriesG_coeff_even,
        legSeriesG_coeff_even]
      have hc1 : ((2 * (n + 2) + 1 : ℕ) : ZOmega ℤ) + 1 = 2 * ((n : ZOmega ℤ) + 3) := by
        push_cast; ring
      have hc2 : ((2 * (n + 2) + 1 - 2 : ℕ) : ZOmega ℤ) + 1 = 2 * ((n : ZOmega ℤ) + 2) := by
        rw [show 2 * (n + 2) + 1 - 2 = 2 * n + 3 by omega]; push_cast; ring
      have hc3 : ((2 * (n + 2) + 1 - 4 : ℕ) : ZOmega ℤ) + 1 = 2 * ((n : ZOmega ℤ) + 1) := by
        rw [show 2 * (n + 2) + 1 - 4 = 2 * n + 1 by omega]; push_cast; ring
      rw [hc1, hc2, hc3]
      push_cast at h3t
      linear_combination 2 * h3t

private lemma Qpoly_mul_legSeriesG_sq :
    ((Qpoly z0 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) * legSeriesG ^ 2 = 1 := by
  apply PowerSeries.derivative.ext
  · rw [PowerSeries.derivative_one, Derivation.leibniz, PowerSeries.derivative_pow]
    have hQd : PowerSeries.derivative (ZOmega ℤ)
        ((Qpoly z0 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) =
        -PowerSeries.C (4 * z0) * PowerSeries.X + 4 * PowerSeries.X ^ 3 := by
      rw [PowerSeries.derivative_coe]
      have : (Qpoly z0).derivative = -C (4 * z0) * X + C 4 * X ^ 3 := by
        unfold Qpoly
        simp only [Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_one,
          Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
          Polynomial.derivative_X_pow, Nat.cast_ofNat, map_ofNat, Nat.reduceSub, pow_one]
        have hC4 : (C (4 * z0) : (ZOmega ℤ)[X]) = C (2 * z0) * 2 := by
          rw [show (4 * z0 : ZOmega ℤ) = (2 * z0) * 2 by ring, map_mul, map_ofNat]
        rw [hC4]; ring
      rw [this]
      simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_neg, Polynomial.coe_C,
        Polynomial.coe_X, Polynomial.coe_pow]
      rw [map_ofNat]
    rw [hQd]
    have hode := Qpoly_mul_deriv_legSeriesG
    simp only [smul_eq_mul, Nat.cast_ofNat]
    have hC4 : (PowerSeries.C (4 * z0) : PowerSeries (ZOmega ℤ)) =
        (2 : PowerSeries (ZOmega ℤ)) * PowerSeries.C (2 * z0) := by
      rw [show (4 * z0 : ZOmega ℤ) = 2 * (2 * z0) by ring, map_mul, map_ofNat]
    rw [hC4]
    linear_combination 2 * legSeriesG * hode
  · simp only [map_mul, map_pow, Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero,
      Qpoly_eval_zero, legSeriesG_constantCoeff, one_pow, mul_one, map_one]

private noncomputable def psInv {f : PowerSeries (ZOmega ℤ)} (hf : IsUnit f) :
    PowerSeries (ZOmega ℤ) := ↑(hf.unit⁻¹)

private lemma psInv_mul {f : PowerSeries (ZOmega ℤ)} (hf : IsUnit f) :
    f * psInv hf = 1 := hf.unit.mul_inv

private lemma mul_psInv {f : PowerSeries (ZOmega ℤ)} (hf : IsUnit f) :
    psInv hf * f = 1 := hf.unit.inv_mul

private lemma legSeriesG_isUnit : IsUnit legSeriesG := by
  rw [PowerSeries.isUnit_iff_constantCoeff, legSeriesG_constantCoeff]
  exact isUnit_one

private noncomputable def legSeriesY : PowerSeries (ZOmega ℤ) := psInv legSeriesG_isUnit

private lemma legSeriesY_mul_G : legSeriesY * legSeriesG = 1 := mul_psInv legSeriesG_isUnit

private lemma legSeriesG_mul_Y : legSeriesG * legSeriesY = 1 := psInv_mul legSeriesG_isUnit

private lemma legSeriesY_constantCoeff : PowerSeries.constantCoeff legSeriesY = 1 := by
  have h := congr_arg PowerSeries.constantCoeff legSeriesY_mul_G
  rw [map_mul, legSeriesG_constantCoeff, mul_one, map_one] at h
  exact h

private lemma legSeriesY_sq :
    legSeriesY ^ 2 = ((Qpoly z0 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) := by
  calc legSeriesY ^ 2
      = legSeriesY ^ 2 * (((Qpoly z0 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) * legSeriesG ^ 2) := by
        rw [Qpoly_mul_legSeriesG_sq, mul_one]
    _ = ((Qpoly z0 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) * (legSeriesY * legSeriesG) ^ 2 := by
        ring
    _ = ((Qpoly z0 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) := by
        rw [legSeriesY_mul_G, one_pow, mul_one]

/-- Universal Jacobi quartic addition law in `PowerSeries (ZOmega ℤ)`:
given two power-series points `(u1, y1)` and `(u2, y2)` on `y^2 = 1 - 2*z0*u^2 + u^4`
with `u_i' = n_i * g * y_i`, their sum `(u3, y3)` lies on the curve and satisfies
`u3' = (n1 + n2) * g * y3`. -/
private lemma jacobi_add_ps_law
    (u1 y1 u2 y2 : PowerSeries (ZOmega ℤ)) (n1 n2 : ℤ)
    (hu1_0 : PowerSeries.constantCoeff u1 = 0)
    (hy1_0 : PowerSeries.constantCoeff y1 = 1)
    (hu2_0 : PowerSeries.constantCoeff u2 = 0)
    (hy2_0 : PowerSeries.constantCoeff y2 = 1)
    (hcur1 : y1 ^ 2 = 1 - PowerSeries.C (2 * z0) * u1 ^ 2 + u1 ^ 4)
    (hcur2 : y2 ^ 2 = 1 - PowerSeries.C (2 * z0) * u2 ^ 2 + u2 ^ 4)
    (hdiff1 : PowerSeries.derivative (ZOmega ℤ) u1 = (n1 : PowerSeries (ZOmega ℤ)) * legSeriesG * y1)
    (hdiff2 : PowerSeries.derivative (ZOmega ℤ) u2 = (n2 : PowerSeries (ZOmega ℤ)) * legSeriesG * y2) :
    let D := 1 - u1 ^ 2 * u2 ^ 2
    let N := u1 * y2 + u2 * y1
    let Y3 := (1 + u1 ^ 2 * u2 ^ 2) * (y1 * y2 - PowerSeries.C (2 * z0) * u1 * u2) +
                2 * u1 * u2 * (u1 ^ 2 + u2 ^ 2)
    have hD_unit : IsUnit D := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      simp [D, hu1_0, hu2_0]
    let Dinv : PowerSeries (ZOmega ℤ) := psInv hD_unit
    let u3 := N * Dinv
    let y3 := Y3 * Dinv ^ 2
    PowerSeries.constantCoeff u3 = 0 ∧
    PowerSeries.constantCoeff y3 = 1 ∧
    y3 ^ 2 = 1 - PowerSeries.C (2 * z0) * u3 ^ 2 + u3 ^ 4 ∧
    PowerSeries.derivative (ZOmega ℤ) u3 =
      ((n1 + n2 : ℤ) : PowerSeries (ZOmega ℤ)) * legSeriesG * y3 := by
  intro D N Y3 hD_unit Dinv u3 y3
  have hDinv_mul : D * Dinv = 1 := psInv_mul hD_unit
  have hD0 : PowerSeries.constantCoeff D = 1 := by simp [D, hu1_0, hu2_0]
  have hDinv0 : PowerSeries.constantCoeff Dinv = 1 := by
    have h := congr_arg PowerSeries.constantCoeff hDinv_mul
    rw [map_mul, hD0, one_mul, map_one] at h; exact h
  have hu3_0 : PowerSeries.constantCoeff u3 = 0 := by
    simp [u3, N, hu1_0, hu2_0]
  have hy3_0 : PowerSeries.constantCoeff y3 = 1 := by
    simp [y3, Y3, hu1_0, hu2_0, hy1_0, hy2_0, hDinv0]
  have hY3_sq : Y3 ^ 2 = D ^ 4 - PowerSeries.C (2 * z0) * N ^ 2 * D ^ 2 + N ^ 4 := by
    have hy1_3 : y1 ^ 3 = (1 - PowerSeries.C (2 * z0) * u1 ^ 2 + u1 ^ 4) * y1 := by
      rw [show y1 ^ 3 = y1 ^ 2 * y1 by ring, hcur1]
    have hy1_4 : y1 ^ 4 = (1 - PowerSeries.C (2 * z0) * u1 ^ 2 + u1 ^ 4) ^ 2 := by
      rw [show y1 ^ 4 = (y1 ^ 2) ^ 2 by ring, hcur1]
    have hy2_3 : y2 ^ 3 = (1 - PowerSeries.C (2 * z0) * u2 ^ 2 + u2 ^ 4) * y2 := by
      rw [show y2 ^ 3 = y2 ^ 2 * y2 by ring, hcur2]
    have hy2_4 : y2 ^ 4 = (1 - PowerSeries.C (2 * z0) * u2 ^ 2 + u2 ^ 4) ^ 2 := by
      rw [show y2 ^ 4 = (y2 ^ 2) ^ 2 by ring, hcur2]
    dsimp only [Y3, D, N]
    ring_nf
    simp only [hcur1, hcur2, hy1_3, hy1_4, hy2_3, hy2_4]
    ring
  have hcur3 : y3 ^ 2 = 1 - PowerSeries.C (2 * z0) * u3 ^ 2 + u3 ^ 4 := by
    calc y3 ^ 2 = Y3 ^ 2 * Dinv ^ 4 := by dsimp only [y3]; ring
      _ = (D ^ 4 - PowerSeries.C (2 * z0) * N ^ 2 * D ^ 2 + N ^ 4) * Dinv ^ 4 := by rw [hY3_sq]
      _ = (D * Dinv) ^ 4 - PowerSeries.C (2 * z0) * (N * Dinv) ^ 2 * (D * Dinv) ^ 2 + (N * Dinv) ^ 4 := by ring
      _ = 1 - PowerSeries.C (2 * z0) * u3 ^ 2 + u3 ^ 4 := by rw [hDinv_mul]; dsimp only [u3]; ring
  -- Compute derivatives y1' and y2' via 2 * y_i * y_i' = (-4*z0*u_i + 4*u_i^3) * u_i'
  have hy_deriv : ∀ (u y : PowerSeries (ZOmega ℤ)) (n : ℤ),
      PowerSeries.constantCoeff y = 1 →
      y ^ 2 = 1 - PowerSeries.C (2 * z0) * u ^ 2 + u ^ 4 →
      PowerSeries.derivative (ZOmega ℤ) u = (n : PowerSeries (ZOmega ℤ)) * legSeriesG * y →
      PowerSeries.derivative (ZOmega ℤ) y =
        2 * (n : PowerSeries (ZOmega ℤ)) * legSeriesG * u * (u ^ 2 - PowerSeries.C z0) := by
    intro u y n hy0 hcur hdu
    have hd := congr_arg (PowerSeries.derivative (ZOmega ℤ)) hcur
    simp only [PowerSeries.derivative_pow, map_add, map_sub, PowerSeries.derivative_one,
      Derivation.leibniz, PowerSeries.derivative_C, smul_eq_mul, mul_zero,
      zero_sub, Nat.cast_ofNat] at hd
    rw [hdu] at hd
    have h2z : (PowerSeries.C (2 * z0) : PowerSeries (ZOmega ℤ)) =
        (2 : PowerSeries (ZOmega ℤ)) * PowerSeries.C z0 := by
      rw [map_mul, map_ofNat]
    rw [h2z] at hd
    have hmul : (2 : PowerSeries (ZOmega ℤ)) * y *
        (PowerSeries.derivative (ZOmega ℤ) y -
          2 * (n : PowerSeries (ZOmega ℤ)) * legSeriesG * u * (u ^ 2 - PowerSeries.C z0)) = 0 := by
      linear_combination hd
    have hy_unit : IsUnit y := by rw [PowerSeries.isUnit_iff_constantCoeff, hy0]; exact isUnit_one
    have h2mul : (2 : PowerSeries (ZOmega ℤ)) *
        (PowerSeries.derivative (ZOmega ℤ) y -
          2 * (n : PowerSeries (ZOmega ℤ)) * legSeriesG * u * (u ^ 2 - PowerSeries.C z0)) = 0 := by
      have hcomm : y * ((2 : PowerSeries (ZOmega ℤ)) *
          (PowerSeries.derivative (ZOmega ℤ) y -
            2 * (n : PowerSeries (ZOmega ℤ)) * legSeriesG * u * (u ^ 2 - PowerSeries.C z0))) = 0 := by
        linear_combination hmul
      exact hy_unit.mul_right_eq_zero.mp hcomm
    have hsub0 : PowerSeries.derivative (ZOmega ℤ) y -
        2 * (n : PowerSeries (ZOmega ℤ)) * legSeriesG * u * (u ^ 2 - PowerSeries.C z0) = 0 := by
      ext k
      have hk := congr_arg (PowerSeries.coeff k) h2mul
      have htwo : (2 : PowerSeries (ZOmega ℤ)) *
          (PowerSeries.derivative (ZOmega ℤ) y -
            2 * (n : PowerSeries (ZOmega ℤ)) * legSeriesG * u * (u ^ 2 - PowerSeries.C z0)) =
          (2 : ℕ) • (PowerSeries.derivative (ZOmega ℤ) y -
            2 * (n : PowerSeries (ZOmega ℤ)) * legSeriesG * u * (u ^ 2 - PowerSeries.C z0)) := by
        rw [two_nsmul]; ring
      rw [htwo, map_nsmul, map_zero] at hk
      exact nsmul_right_injective (by decide : 2 ≠ 0) (by simpa using hk)
    exact sub_eq_zero.mp hsub0
  have hdy1 := hy_deriv u1 y1 n1 hy1_0 hcur1 hdiff1
  have hdy2 := hy_deriv u2 y2 n2 hy2_0 hcur2 hdiff2
  have hdN : PowerSeries.derivative (ZOmega ℤ) N =
      ((n1 : PowerSeries (ZOmega ℤ)) + (n2 : PowerSeries (ZOmega ℤ))) * legSeriesG * y1 * y2 +
        2 * u1 * u2 * legSeriesG *
          ((n1 : PowerSeries (ZOmega ℤ)) * (u1 ^ 2 - PowerSeries.C z0) +
           (n2 : PowerSeries (ZOmega ℤ)) * (u2 ^ 2 - PowerSeries.C z0)) := by
    dsimp only [N]
    simp only [map_add, Derivation.leibniz, smul_eq_mul, hdiff1, hdiff2, hdy1, hdy2]
    ring
  have hdD : PowerSeries.derivative (ZOmega ℤ) D =
      -2 * u1 * u2 * legSeriesG *
        ((n1 : PowerSeries (ZOmega ℤ)) * u2 * y1 + (n2 : PowerSeries (ZOmega ℤ)) * u1 * y2) := by
    dsimp only [D]
    simp only [map_sub, PowerSeries.derivative_one, Derivation.leibniz, PowerSeries.derivative_pow,
      smul_eq_mul, hdiff1, hdiff2, Nat.cast_ofNat]
    ring
  have hwronsk : PowerSeries.derivative (ZOmega ℤ) N * D - N * PowerSeries.derivative (ZOmega ℤ) D =
      ((n1 + n2 : ℤ) : PowerSeries (ZOmega ℤ)) * legSeriesG * Y3 := by
    rw [hdN, hdD]
    have h2z : (PowerSeries.C (2 * z0) : PowerSeries (ZOmega ℤ)) =
        (2 : PowerSeries (ZOmega ℤ)) * PowerSeries.C z0 := by rw [map_mul, map_ofNat]
    dsimp only [D, N, Y3]
    rw [h2z, Int.cast_add]
    have hcur1' : y1 ^ 2 - (1 - 2 * PowerSeries.C z0 * u1 ^ 2 + u1 ^ 4) = 0 := by
      rw [← h2z]; exact sub_eq_zero.mpr hcur1
    have hcur2' : y2 ^ 2 - (1 - 2 * PowerSeries.C z0 * u2 ^ 2 + u2 ^ 4) = 0 := by
      rw [← h2z]; exact sub_eq_zero.mpr hcur2
    linear_combination
      2 * u1 * u2 * legSeriesG *
        ((n1 : PowerSeries (ZOmega ℤ)) * u2 ^ 2 * hcur1' +
         (n2 : PowerSeries (ZOmega ℤ)) * u1 ^ 2 * hcur2')
  have hdiff3 : PowerSeries.derivative (ZOmega ℤ) u3 =
      ((n1 + n2 : ℤ) : PowerSeries (ZOmega ℤ)) * legSeriesG * y3 := by
    dsimp only [u3, y3]
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have hdDinv : PowerSeries.derivative (ZOmega ℤ) Dinv =
        -Dinv ^ 2 * PowerSeries.derivative (ZOmega ℤ) D :=
      PowerSeries.derivative_inv hD_unit.unit
    rw [hdDinv]
    calc N * (-Dinv ^ 2 * PowerSeries.derivative (ZOmega ℤ) D) +
            Dinv * PowerSeries.derivative (ZOmega ℤ) N
        = PowerSeries.derivative (ZOmega ℤ) N * (D * Dinv) * Dinv -
            N * PowerSeries.derivative (ZOmega ℤ) D * Dinv ^ 2 := by
          rw [hDinv_mul]; ring
      _ = (PowerSeries.derivative (ZOmega ℤ) N * D - N * PowerSeries.derivative (ZOmega ℤ) D) * Dinv ^ 2 := by
          ring
      _ = ((n1 + n2 : ℤ) : PowerSeries (ZOmega ℤ)) * legSeriesG * (Y3 * Dinv ^ 2) := by
          rw [hwronsk]; ring
  exact ⟨hu3_0, hy3_0, hcur3, hdiff3⟩

/-- Zero-division Jacobi quartic multiplication polynomial triples `(A_n, B_n, C_n)` over `ZOmega ℤ`. -/
private noncomputable def jacobiTriple : ℕ → (ZOmega ℤ)[X] × (ZOmega ℤ)[X] × (ZOmega ℤ)[X]
  | 0 => (0, 1, 1)
  | 1 => (X, 1, 1)
  | n + 2 =>
    let Q := Qpoly z0
    if (n + 2) % 2 = 0 then
      let m := (n + 2) / 2
      let (A, B, C) := jacobiTriple m
      if m % 2 = 1 then
        (2 * A * B * C,
         B ^ 4 - A ^ 4,
         (B ^ 4 + A ^ 4) * (Q * C ^ 2 - Polynomial.C (2 * z0) * A ^ 2 * B ^ 2) +
           4 * A ^ 4 * B ^ 4)
      else
        (2 * A * B * C,
         B ^ 4 - Q ^ 2 * A ^ 4,
         (B ^ 4 + Q ^ 2 * A ^ 4) * (C ^ 2 - Polynomial.C (2 * z0) * Q * A ^ 2 * B ^ 2) +
           4 * Q ^ 2 * A ^ 4 * B ^ 4)
    else
      let m := (n + 2) / 2
      let (Ao, Bo, Co) := if m % 2 = 1 then jacobiTriple m else jacobiTriple (m + 1)
      let (Ae, Be, Ce) := if m % 2 = 1 then jacobiTriple (m + 1) else jacobiTriple m
      (Ao * Bo * Ce + Q * Ae * Be * Co,
       Bo ^ 2 * Be ^ 2 - Q * Ao ^ 2 * Ae ^ 2,
       (Bo ^ 2 * Be ^ 2 + Q * Ao ^ 2 * Ae ^ 2) *
           (Co * Ce - Polynomial.C (2 * z0) * Ao * Ae * Bo * Be) +
         2 * Ao * Ae * Bo * Be * (Ao ^ 2 * Be ^ 2 + Q * Ae ^ 2 * Bo ^ 2))
termination_by n => n
decreasing_by all_goals omega

private noncomputable def jA (n : ℕ) : (ZOmega ℤ)[X] := (jacobiTriple n).1
private noncomputable def jB (n : ℕ) : (ZOmega ℤ)[X] := (jacobiTriple n).2.1
private noncomputable def jC (n : ℕ) : (ZOmega ℤ)[X] := (jacobiTriple n).2.2

private lemma jacobiTriple_one : jA 1 = X ∧ jB 1 = 1 ∧ jC 1 = 1 := by
  simp [jA, jB, jC, jacobiTriple]

private lemma jacobiTriple_even_of_odd {m : ℕ} (hm : m % 2 = 1) :
    jA (2 * m) = 2 * jA m * jB m * jC m ∧
    jB (2 * m) = jB m ^ 4 - jA m ^ 4 ∧
    jC (2 * m) = (jB m ^ 4 + jA m ^ 4) *
      (Qpoly z0 * jC m ^ 2 - C (2 * z0) * jA m ^ 2 * jB m ^ 2) +
      4 * jA m ^ 4 * jB m ^ 4 := by
  have hm1 : 1 ≤ m := by omega
  have h2m : 2 * m = (2 * m - 2) + 2 := by omega
  have hdiv : ((2 * m - 2) + 2) / 2 = m := by omega
  have hmod : ((2 * m - 2) + 2) % 2 = 0 := by omega
  dsimp only [jA, jB, jC]
  rw [h2m, jacobiTriple]
  simp [hmod, hdiv, hm]

private lemma jacobiTriple_even_of_even {m : ℕ} (hm1 : 1 ≤ m) (hm : m % 2 = 0) :
    jA (2 * m) = 2 * jA m * jB m * jC m ∧
    jB (2 * m) = jB m ^ 4 - Qpoly z0 ^ 2 * jA m ^ 4 ∧
    jC (2 * m) = (jB m ^ 4 + Qpoly z0 ^ 2 * jA m ^ 4) *
      (jC m ^ 2 - C (2 * z0) * Qpoly z0 * jA m ^ 2 * jB m ^ 2) +
      4 * Qpoly z0 ^ 2 * jA m ^ 4 * jB m ^ 4 := by
  have h2m : 2 * m = (2 * m - 2) + 2 := by omega
  have hdiv : ((2 * m - 2) + 2) / 2 = m := by omega
  have hmod : ((2 * m - 2) + 2) % 2 = 0 := by omega
  dsimp only [jA, jB, jC]
  rw [h2m, jacobiTriple]
  simp [hmod, hdiv, hm]

private lemma jacobiTriple_odd_step {m : ℕ} (hm1 : 1 ≤ m) :
    let o := if m % 2 = 1 then m else m + 1
    let e := if m % 2 = 1 then m + 1 else m
    jA (2 * m + 1) = jA o * jB o * jC e + Qpoly z0 * jA e * jB e * jC o ∧
    jB (2 * m + 1) = jB o ^ 2 * jB e ^ 2 - Qpoly z0 * jA o ^ 2 * jA e ^ 2 ∧
    jC (2 * m + 1) = (jB o ^ 2 * jB e ^ 2 + Qpoly z0 * jA o ^ 2 * jA e ^ 2) *
        (jC o * jC e - C (2 * z0) * jA o * jA e * jB o * jB e) +
      2 * jA o * jA e * jB o * jB e *
        (jA o ^ 2 * jB e ^ 2 + Qpoly z0 * jA e ^ 2 * jB o ^ 2) := by
  have h2m : 2 * m + 1 = (2 * m - 1) + 2 := by omega
  have hdiv : ((2 * m - 1) + 2) / 2 = m := by omega
  have hmod : ((2 * m - 1) + 2) % 2 ≠ 0 := by omega
  dsimp only [jA, jB, jC]
  rw [h2m, jacobiTriple]
  simp only [hmod, ↓reduceIte, hdiv]
  split_ifs <;> simp

private lemma jacobiTriple_eval_zero (n : ℕ) (hn : 1 ≤ n) :
    (jA n).eval 0 = 0 ∧ (jB n).eval 0 = 1 ∧ (jC n).eval 0 = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst h1; simp [jacobiTriple_one]
    · by_cases hev : n % 2 = 0
      · set m := n / 2
        have hm1 : 1 ≤ m := by omega
        have hmn : m < n := by omega
        have hn_eq : n = 2 * m := by omega
        rcases ih m hmn hm1 with ⟨hA, hB, hC⟩
        by_cases hmo : m % 2 = 1
        · rcases jacobiTriple_even_of_odd hmo with ⟨eA, eB, eC⟩
          rw [hn_eq, eA, eB, eC]
          simp [hA, hB, hC, Qpoly_eval_zero]
        · have hme : m % 2 = 0 := by omega
          rcases jacobiTriple_even_of_even hm1 hme with ⟨eA, eB, eC⟩
          rw [hn_eq, eA, eB, eC]
          simp [hA, hB, hC, Qpoly_eval_zero]
      · set m := n / 2
        have hm1 : 1 ≤ m := by omega
        have hmn : m < n := by omega
        have hm1n : m + 1 < n := by omega
        have hn_eq : n = 2 * m + 1 := by omega
        have hstep := jacobiTriple_odd_step hm1
        dsimp only at hstep
        set o := if m % 2 = 1 then m else m + 1
        set e := if m % 2 = 1 then m + 1 else m
        have ho_lt : o < n := by dsimp only [o]; split_ifs <;> omega
        have he_lt : e < n := by dsimp only [e]; split_ifs <;> omega
        have ho1 : 1 ≤ o := by dsimp only [o]; split_ifs <;> omega
        have he1 : 1 ≤ e := by dsimp only [e]; split_ifs <;> omega
        rcases ih o ho_lt ho1 with ⟨hAo, hBo, hCo⟩
        rcases ih e he_lt he1 with ⟨hAe, hBe, hCe⟩
        rw [hn_eq, hstep.1, hstep.2.1, hstep.2.2]
        simp [hAo, hBo, hCo, hAe, hBe, hCe, Qpoly_eval_zero]

private lemma jacobiTriple_parity (n : ℕ) (hn : 1 ≤ n) :
    (jA n).comp (-X) = -jA n ∧ (jB n).comp (-X) = jB n ∧ (jC n).comp (-X) = jC n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst h1; simp [jacobiTriple_one]
    · by_cases hev : n % 2 = 0
      · set m := n / 2
        have hm1 : 1 ≤ m := by omega
        have hmn : m < n := by omega
        have hn_eq : n = 2 * m := by omega
        rcases ih m hmn hm1 with ⟨hA, hB, hC⟩
        by_cases hmo : m % 2 = 1
        · rcases jacobiTriple_even_of_odd hmo with ⟨eA, eB, eC⟩
          rw [hn_eq, eA, eB, eC]
          simp only [Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
            Polynomial.pow_comp, Polynomial.C_comp, Polynomial.ofNat_comp,
            hA, hB, hC, Qpoly_comp_neg_X]
          exact ⟨by ring, by ring, by ring⟩
        · have hme : m % 2 = 0 := by omega
          rcases jacobiTriple_even_of_even hm1 hme with ⟨eA, eB, eC⟩
          rw [hn_eq, eA, eB, eC]
          simp only [Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
            Polynomial.pow_comp, Polynomial.C_comp, Polynomial.ofNat_comp,
            hA, hB, hC, Qpoly_comp_neg_X]
          exact ⟨by ring, by ring, by ring⟩
      · set m := n / 2
        have hm1 : 1 ≤ m := by omega
        have hn_eq : n = 2 * m + 1 := by omega
        have hstep := jacobiTriple_odd_step hm1
        dsimp only at hstep
        set o := if m % 2 = 1 then m else m + 1
        set e := if m % 2 = 1 then m + 1 else m
        have ho_lt : o < n := by dsimp only [o]; split_ifs <;> omega
        have he_lt : e < n := by dsimp only [e]; split_ifs <;> omega
        have ho1 : 1 ≤ o := by dsimp only [o]; split_ifs <;> omega
        have he1 : 1 ≤ e := by dsimp only [e]; split_ifs <;> omega
        rcases ih o ho_lt ho1 with ⟨hAo, hBo, hCo⟩
        rcases ih e he_lt he1 with ⟨hAe, hBe, hCe⟩
        rw [hn_eq, hstep.1, hstep.2.1, hstep.2.2]
        simp only [Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
          Polynomial.pow_comp, Polynomial.C_comp, Polynomial.ofNat_comp,
          hAo, hBo, hCo, hAe, hBe, hCe, Qpoly_comp_neg_X]
        exact ⟨by ring, by ring, by ring⟩

private lemma jacobiTriple_natDegree_le (n : ℕ) (hn : 1 ≤ n) :
    (if n % 2 = 1 then (jA n).natDegree ≤ n ^ 2 ∧ (jB n).natDegree ≤ n ^ 2 - 1 ∧
        (jC n).natDegree ≤ 2 * n ^ 2 - 2
     else (jA n).natDegree ≤ n ^ 2 - 2 ∧ (jB n).natDegree ≤ n ^ 2 ∧
        (jC n).natDegree ≤ 2 * n ^ 2) := by
  have hQ : (Qpoly z0).natDegree ≤ 4 := Qpoly_natDegree_le z0
  have hmul : ∀ (p q : (ZOmega ℤ)[X]) (a b : ℕ), p.natDegree ≤ a → q.natDegree ≤ b →
      (p * q).natDegree ≤ a + b := fun p q a b hp hq =>
    le_trans Polynomial.natDegree_mul_le (Nat.add_le_add hp hq)
  have hpow : ∀ (p : (ZOmega ℤ)[X]) (k a : ℕ), p.natDegree ≤ a →
      (p ^ k).natDegree ≤ k * a := fun p k a hp =>
    le_trans Polynomial.natDegree_pow_le (Nat.mul_le_mul_left k hp)
  have hadd : ∀ (p q : (ZOmega ℤ)[X]) (a : ℕ), p.natDegree ≤ a → q.natDegree ≤ a →
      (p + q).natDegree ≤ a := fun p q a hp hq =>
    le_trans (Polynomial.natDegree_add_le _ _) (max_le hp hq)
  have hsub : ∀ (p q : (ZOmega ℤ)[X]) (a : ℕ), p.natDegree ≤ a → q.natDegree ≤ a →
      (p - q).natDegree ≤ a := fun p q a hp hq =>
    le_trans (Polynomial.natDegree_sub_le _ _) (max_le hp hq)
  have hCmul : ∀ (c : ZOmega ℤ) (p : (ZOmega ℤ)[X]) (a : ℕ), p.natDegree ≤ a →
      (C c * p).natDegree ≤ a := fun c p a hp =>
    le_trans (Polynomial.natDegree_C_mul_le c p) hp
  have h2mul : ∀ (p : (ZOmega ℤ)[X]) (a : ℕ), p.natDegree ≤ a →
      (2 * p).natDegree ≤ a := fun p a hp => by
    rw [show (2 : (ZOmega ℤ)[X]) = C 2 from (map_ofNat C 2).symm]; exact hCmul _ _ _ hp
  have h4mul : ∀ (p : (ZOmega ℤ)[X]) (a : ℕ), p.natDegree ≤ a →
      (4 * p).natDegree ≤ a := fun p a hp => by
    rw [show (4 : (ZOmega ℤ)[X]) = C 4 from (map_ofNat C 4).symm]; exact hCmul _ _ _ hp
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst h1
      simp only [Nat.one_mod, ↓reduceIte, jacobiTriple_one]
      exact ⟨le_trans Polynomial.natDegree_X_le le_rfl, by simp, by simp⟩
    · by_cases hev : n % 2 = 0
      · simp only [show n % 2 ≠ 1 by omega, ↓reduceIte]
        set m := n / 2
        have hm1 : 1 ≤ m := by omega
        have hmn : m < n := by omega
        have hn_eq : n = 2 * m := by omega
        have h2m_sq : (2 * m) ^ 2 = 4 * m ^ 2 := by ring
        have ihm := ih m hmn hm1
        by_cases hmo : m % 2 = 1
        · simp only [hmo, ↓reduceIte] at ihm
          rcases ihm with ⟨dA, dB, dC⟩
          rcases jacobiTriple_even_of_odd hmo with ⟨eA, eB, eC⟩
          rw [hn_eq, eA, eB, eC, h2m_sq]
          have hm2 : 1 ≤ m ^ 2 := by nlinarith
          have dA4 := hpow _ 4 _ dA
          have dB4 := hpow _ 4 _ dB
          have dA2 := hpow _ 2 _ dA
          have dB2 := hpow _ 2 _ dB
          have dC2 := hpow _ 2 _ dC
          refine ⟨?_, ?_, ?_⟩
          · have := hmul _ _ _ _ (hmul _ _ _ _ (h2mul _ _ dA) dB) dC
            omega
          · exact hsub _ _ (4 * m ^ 2) (by omega) (by omega)
          · apply hadd _ _ (2 * (4 * m ^ 2))
            · rw [show 2 * (4 * m ^ 2) = 4 * m ^ 2 + 4 * m ^ 2 by ring]
              apply hmul _ _ (4 * m ^ 2) (4 * m ^ 2)
              · exact hadd _ _ (4 * m ^ 2) (by omega) (by omega)
              · apply hsub _ _ (4 * m ^ 2)
                · have := hmul _ _ _ _ hQ dC2; omega
                · have := hmul _ _ _ _ (hCmul (2 * z0) _ _ dA2) dB2; omega
            · have := hmul _ _ _ _ (h4mul _ _ dA4) dB4; omega
        · have hme : m % 2 = 0 := by omega
          simp only [show m % 2 ≠ 1 by omega, ↓reduceIte] at ihm
          rcases ihm with ⟨dA, dB, dC⟩
          rcases jacobiTriple_even_of_even hm1 hme with ⟨eA, eB, eC⟩
          rw [hn_eq, eA, eB, eC, h2m_sq]
          have hm2 : 4 ≤ m ^ 2 := by
            have : 2 ≤ m := by omega
            nlinarith
          have dA4 := hpow _ 4 _ dA
          have dB4 := hpow _ 4 _ dB
          have dA2 := hpow _ 2 _ dA
          have dB2 := hpow _ 2 _ dB
          have dC2 := hpow _ 2 _ dC
          have dQ2 := hpow _ 2 _ hQ
          refine ⟨?_, ?_, ?_⟩
          · have := hmul _ _ _ _ (hmul _ _ _ _ (h2mul _ _ dA) dB) dC
            omega
          · apply hsub _ _ (4 * m ^ 2)
            · omega
            · have := hmul _ _ _ _ dQ2 dA4; omega
          · apply hadd _ _ (2 * (4 * m ^ 2))
            · rw [show 2 * (4 * m ^ 2) = 4 * m ^ 2 + 4 * m ^ 2 by ring]
              apply hmul _ _ (4 * m ^ 2) (4 * m ^ 2)
              · apply hadd _ _ (4 * m ^ 2)
                · omega
                · have := hmul _ _ _ _ dQ2 dA4; omega
              · apply hsub _ _ (4 * m ^ 2)
                · omega
                · have := hmul _ _ _ _ (hmul _ _ _ _ (hCmul (2 * z0) _ _ hQ) dA2) dB2; omega
            · have := hmul _ _ _ _ (hmul _ _ _ _ (h4mul _ _ dQ2) dA4) dB4; omega
      · have hno : n % 2 = 1 := by omega
        simp only [hno, ↓reduceIte]
        set m := n / 2
        have hm1 : 1 ≤ m := by omega
        have hn_eq : n = 2 * m + 1 := by omega
        have hstep := jacobiTriple_odd_step hm1
        dsimp only at hstep
        set o := if m % 2 = 1 then m else m + 1
        set e := if m % 2 = 1 then m + 1 else m
        have ho_odd : o % 2 = 1 := by dsimp only [o]; split_ifs <;> omega
        have he_ev : e % 2 = 0 := by dsimp only [e]; split_ifs <;> omega
        have ho_lt : o < n := by dsimp only [o]; split_ifs <;> omega
        have he_lt : e < n := by dsimp only [e]; split_ifs <;> omega
        have ho1 : 1 ≤ o := by dsimp only [o]; split_ifs <;> omega
        have he1 : 1 ≤ e := by dsimp only [e]; split_ifs <;> omega
        have hsum_sq : 2 * (o ^ 2 + e ^ 2) = (2 * m + 1) ^ 2 + 1 := by
          dsimp only [o, e]; split_ifs <;> ring
        have ho2 : 1 ≤ o ^ 2 := by nlinarith
        have he2 : 4 ≤ e ^ 2 := by
          have : 2 ≤ e := by omega
          nlinarith
        have iho := ih o ho_lt ho1; simp only [ho_odd, ↓reduceIte] at iho
        have ihe := ih e he_lt he1; simp only [show e % 2 ≠ 1 by omega, ↓reduceIte] at ihe
        rcases iho with ⟨dAo, dBo, dCo⟩
        rcases ihe with ⟨dAe, dBe, dCe⟩
        have dAe3 : (jA e).natDegree ≤ e ^ 2 - 3 := by
          by_cases hlt : (jA e).natDegree < e ^ 2 - 2
          · omega
          · exfalso
            have heq : (jA e).natDegree = e ^ 2 - 2 := by omega
            have hpar := (jacobiTriple_parity e he1).1
            have hcoeff := congr_arg (fun f => f.coeff (e ^ 2 - 2)) hpar
            have hcomp_c : ∀ (P : (ZOmega ℤ)[X]) (k : ℕ),
                (P.comp (-X)).coeff k = (-1 : ZOmega ℤ) ^ k * P.coeff k := by
              intro P k
              rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def, Polynomial.finsetSum_coeff]
              have ht : ∀ i ∈ P.support,
                  (C (P.coeff i) * (-X : (ZOmega ℤ)[X]) ^ i).coeff k =
                    if i = k then (-1 : ZOmega ℤ) ^ k * P.coeff k else 0 := by
                intro i _
                rw [show (-X : (ZOmega ℤ)[X]) = C (-1) * X by simp, mul_pow,
                  ← mul_assoc, ← map_pow, ← map_mul, Polynomial.coeff_C_mul_X_pow]
                by_cases hik : i = k
                · subst hik; simp [mul_comm]
                · have hki : k ≠ i := fun h => hik h.symm
                  simp [hik, hki]
              rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq']
              split_ifs with hk
              · rfl
              · rw [Polynomial.notMem_support_iff.mp hk, mul_zero]
            rw [hcomp_c, Polynomial.coeff_neg] at hcoeff
            have hev_d : Even (e ^ 2 - 2) := by
              rcases Nat.even_iff.mpr he_ev with ⟨r, hr⟩
              refine ⟨2 * r ^ 2 - 1, ?_⟩
              have hr1 : 1 ≤ r := by omega
              have hr2 : 1 ≤ 2 * r ^ 2 := by nlinarith
              have hesq : e ^ 2 = 4 * r ^ 2 := by rw [hr]; ring
              omega
            rw [Even.neg_one_pow hev_d, one_mul] at hcoeff
            have h2c : (2 : ℕ) • (jA e).coeff (e ^ 2 - 2) = 0 := by
              rw [two_nsmul]; exact eq_neg_iff_add_eq_zero.mp hcoeff
            have hc0 : (jA e).coeff (e ^ 2 - 2) = 0 :=
              nsmul_right_injective (by decide : 2 ≠ 0) (by simpa using h2c)
            have hnz : (jA e).coeff (jA e).natDegree ≠ 0 := by
              apply Polynomial.leadingCoeff_ne_zero.mpr
              intro h0; rw [h0] at heq; simp at heq; omega
            rw [heq] at hnz
            exact hnz hc0
        rw [hn_eq, hstep.1, hstep.2.1, hstep.2.2]
        have dAo2 := hpow _ 2 _ dAo; have dBo2 := hpow _ 2 _ dBo
        have dAe2 := hpow _ 2 _ dAe3; have dBe2 := hpow _ 2 _ dBe
        refine ⟨?_, ?_, ?_⟩
        · apply hadd _ _ ((2 * m + 1) ^ 2)
          · have := hmul _ _ _ _ (hmul _ _ _ _ dAo dBo) dCe; omega
          · have := hmul _ _ _ _ (hmul _ _ _ _ (hmul _ _ _ _ hQ dAe3) dBe) dCo; omega
        · apply hsub _ _ ((2 * m + 1) ^ 2 - 1)
          · have := hmul _ _ _ _ dBo2 dBe2; omega
          · have := hmul _ _ _ _ (hmul _ _ _ _ hQ dAo2) dAe2; omega
        · apply hadd _ _ (2 * (2 * m + 1) ^ 2 - 2)
          · have hsplit2 : 2 * (2 * m + 1) ^ 2 - 2 = ((2 * m + 1) ^ 2 - 1) + ((2 * m + 1) ^ 2 - 1) := by
              have : 1 ≤ (2 * m + 1) ^ 2 := by nlinarith
              omega
            rw [hsplit2]
            apply hmul _ _ ((2 * m + 1) ^ 2 - 1) ((2 * m + 1) ^ 2 - 1)
            · apply hadd _ _ ((2 * m + 1) ^ 2 - 1)
              · have := hmul _ _ _ _ dBo2 dBe2; omega
              · have := hmul _ _ _ _ (hmul _ _ _ _ hQ dAo2) dAe2; omega
            · apply hsub _ _ ((2 * m + 1) ^ 2 - 1)
              · have := hmul _ _ _ _ dCo dCe; omega
              · have := hmul _ _ _ _ (hmul _ _ _ _ (hmul _ _ _ _ (hCmul (2 * z0) _ _ dAo) dAe) dBo) dBe
                omega
          · have h1' := hmul _ _ _ _ (hmul _ _ _ _ (hmul _ _ _ _ (h2mul _ _ dAo) dAe3) dBo) dBe
            have h2 : (jA o ^ 2 * jB e ^ 2 + Qpoly z0 * jA e ^ 2 * jB o ^ 2).natDegree ≤
                (2 * m + 1) ^ 2 + 1 := by
              apply hadd _ _ ((2 * m + 1) ^ 2 + 1)
              · have := hmul _ _ _ _ dAo2 dBe2; omega
              · have := hmul _ _ _ _ (hmul _ _ _ _ hQ dAe2) dBo2; omega
            have h3' := hmul _ _ _ _ h1' h2
            omega

private lemma jB_isUnit_ps (n : ℕ) (hn : 1 ≤ n) :
    IsUnit ((jB n : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, Polynomial.constantCoeff_coe,
    Polynomial.coeff_zero_eq_eval_zero, (jacobiTriple_eval_zero n hn).2.1]
  exact isUnit_one

private noncomputable def jU (n : ℕ) (hn : 1 ≤ n) : PowerSeries (ZOmega ℤ) :=
  let Binv : PowerSeries (ZOmega ℤ) := psInv (jB_isUnit_ps n hn)
  if n % 2 = 1 then ((jA n : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) * Binv
  else legSeriesY * ((jA n : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) * Binv

private noncomputable def jY (n : ℕ) (hn : 1 ≤ n) : PowerSeries (ZOmega ℤ) :=
  let Binv : PowerSeries (ZOmega ℤ) := psInv (jB_isUnit_ps n hn)
  if n % 2 = 1 then legSeriesY * ((jC n : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) * Binv ^ 2
  else ((jC n : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) * Binv ^ 2

private lemma jU_jY_props (n : ℕ) (hn : 1 ≤ n) :
    PowerSeries.constantCoeff (jU n hn) = 0 ∧
    PowerSeries.constantCoeff (jY n hn) = 1 ∧
    (jY n hn) ^ 2 = 1 - PowerSeries.C (2 * z0) * (jU n hn) ^ 2 + (jU n hn) ^ 4 ∧
    PowerSeries.derivative (ZOmega ℤ) (jU n hn) =
      ((n : ℤ) : PowerSeries (ZOmega ℤ)) * legSeriesG * jY n hn := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst h1
      have hB1 : ((jB 1 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) = 1 := by
        simp [jacobiTriple_one]
      have hBinv : psInv (jB_isUnit_ps 1 hn) = 1 := by
        have hmul := psInv_mul (jB_isUnit_ps 1 hn)
        exact (one_mul _).symm.trans
          ((congr_arg (· * psInv (jB_isUnit_ps 1 hn)) hB1).symm.trans hmul)
      have hU1 : jU 1 hn = PowerSeries.X := by
        simp [jU, jacobiTriple_one, hBinv]
      have hY1 : jY 1 hn = legSeriesY := by
        simp [jY, jacobiTriple_one, hBinv]
      rw [hU1, hY1]
      refine ⟨by simp, legSeriesY_constantCoeff, ?_, ?_⟩
      · rw [legSeriesY_sq]; simp [Qpoly]
      · simp [PowerSeries.derivative_X, legSeriesG_mul_Y]
    · have hcoe2 : ((2 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) = 2 := by
        rw [show (2 : (ZOmega ℤ)[X]) = 1 + 1 by norm_num, Polynomial.coe_add, Polynomial.coe_one]
        norm_num
      have hcoe4 : ((4 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) = 4 := by
        rw [show (4 : (ZOmega ℤ)[X]) = 2 + 2 by norm_num, Polynomial.coe_add, hcoe2]
        norm_num
      by_cases hev : n % 2 = 0
      · set m := n / 2
        have hm1 : 1 ≤ m := by omega
        have hmn : m < n := by omega
        have hn_eq : n = 2 * m := by omega
        rcases ih m hmn hm1 with ⟨hu0, hy0, hcur, hdiff⟩
        have hlaw := jacobi_add_ps_law (jU m hm1) (jY m hm1) (jU m hm1) (jY m hm1) m m
          hu0 hy0 hu0 hy0 hcur hcur hdiff hdiff
        dsimp only at hlaw
        set Bm : PowerSeries (ZOmega ℤ) := ((jB m : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
        set Am : PowerSeries (ZOmega ℤ) := ((jA m : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
        set Cm : PowerSeries (ZOmega ℤ) := ((jC m : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
        set Bminv : PowerSeries (ZOmega ℤ) := psInv (jB_isUnit_ps m hm1)
        set Bn : PowerSeries (ZOmega ℤ) := ((jB n : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
        set An : PowerSeries (ZOmega ℤ) := ((jA n : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
        set Cn : PowerSeries (ZOmega ℤ) := ((jC n : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
        set Bninv : PowerSeries (ZOmega ℤ) := psInv (jB_isUnit_ps n hn)
        have hBn_mul : Bn * Bninv = 1 := psInv_mul (jB_isUnit_ps n hn)
        have hBm_mul : Bm * Bminv = 1 := psInv_mul (jB_isUnit_ps m hm1)
        set Qps : PowerSeries (ZOmega ℤ) := ((Qpoly z0 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
        have hQps : legSeriesY ^ 2 = Qps := legSeriesY_sq
        have hident :
            (1 - jU m hm1 ^ 2 * jU m hm1 ^ 2) = Bn * Bminv ^ 4 ∧
            (jU m hm1 * jY m hm1 + jU m hm1 * jY m hm1) = legSeriesY * An * Bminv ^ 4 ∧
            ((1 + jU m hm1 ^ 2 * jU m hm1 ^ 2) *
                (jY m hm1 * jY m hm1 - PowerSeries.C (2 * z0) * jU m hm1 * jU m hm1) +
              2 * jU m hm1 * jU m hm1 * (jU m hm1 ^ 2 + jU m hm1 ^ 2)) = Cn * Bminv ^ 8 := by
          by_cases hmo : m % 2 = 1
          · rcases jacobiTriple_even_of_odd hmo with ⟨eA, eB, eC⟩
            have hAn : An = 2 * Am * Bm * Cm := by
              dsimp only [An, Am, Bm, Cm]; rw [hn_eq, eA]
              simp [Polynomial.coe_mul, hcoe2]
            have hBn : Bn = Bm ^ 4 - Am ^ 4 := by
              dsimp only [Bn, Am, Bm]; rw [hn_eq, eB]
              simp [Polynomial.coe_sub, Polynomial.coe_pow]
            have hCn : Cn = (Bm ^ 4 + Am ^ 4) *
                (Qps * Cm ^ 2 - PowerSeries.C (2 * z0) * Am ^ 2 * Bm ^ 2) +
                4 * Am ^ 4 * Bm ^ 4 := by
              dsimp only [Cn, Am, Bm, Cm, Qps]; rw [hn_eq, eC]
              simp [Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul,
                Polynomial.coe_pow, Polynomial.coe_C, hcoe4]
            have hUm : jU m hm1 = Am * Bminv := by simp [jU, hmo, Am, Bminv]
            have hYm : jY m hm1 = legSeriesY * Cm * Bminv ^ 2 := by simp [jY, hmo, Cm, Bminv]
            rw [hUm, hYm, hAn, hBn, hCn]
            refine ⟨?_, ?_, ?_⟩
            · calc 1 - (Am * Bminv) ^ 2 * (Am * Bminv) ^ 2
                  = (Bm * Bminv) ^ 4 - Am ^ 4 * Bminv ^ 4 := by rw [hBm_mul]; ring
                _ = (Bm ^ 4 - Am ^ 4) * Bminv ^ 4 := by ring
            · calc Am * Bminv * (legSeriesY * Cm * Bminv ^ 2) +
                    Am * Bminv * (legSeriesY * Cm * Bminv ^ 2)
                  = 2 * legSeriesY * Am * Cm * (Bm * Bminv) * Bminv ^ 3 := by rw [hBm_mul]; ring
                _ = legSeriesY * (2 * Am * Bm * Cm) * Bminv ^ 4 := by ring
            · calc (1 + (Am * Bminv) ^ 2 * (Am * Bminv) ^ 2) *
                      (legSeriesY * Cm * Bminv ^ 2 * (legSeriesY * Cm * Bminv ^ 2) -
                        PowerSeries.C (2 * z0) * (Am * Bminv) * (Am * Bminv)) +
                    2 * (Am * Bminv) * (Am * Bminv) * ((Am * Bminv) ^ 2 + (Am * Bminv) ^ 2)
                  = ((Bm * Bminv) ^ 4 + Am ^ 4 * Bminv ^ 4) *
                      (legSeriesY ^ 2 * Cm ^ 2 * Bminv ^ 4 -
                        PowerSeries.C (2 * z0) * Am ^ 2 * (Bm * Bminv) ^ 2 * Bminv ^ 2) +
                    4 * Am ^ 4 * (Bm * Bminv) ^ 4 * Bminv ^ 4 := by rw [hBm_mul]; ring
                _ = ((Bm ^ 4 + Am ^ 4) *
                      (Qps * Cm ^ 2 - PowerSeries.C (2 * z0) * Am ^ 2 * Bm ^ 2) +
                      4 * Am ^ 4 * Bm ^ 4) * Bminv ^ 8 := by rw [hQps]; ring
          · have hme : m % 2 = 0 := by omega
            rcases jacobiTriple_even_of_even hm1 hme with ⟨eA, eB, eC⟩
            have hAn : An = 2 * Am * Bm * Cm := by
              dsimp only [An, Am, Bm, Cm]; rw [hn_eq, eA]
              simp [Polynomial.coe_mul, hcoe2]
            have hBn : Bn = Bm ^ 4 - Qps ^ 2 * Am ^ 4 := by
              dsimp only [Bn, Am, Bm, Qps]; rw [hn_eq, eB]
              simp [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow]
            have hCn : Cn = (Bm ^ 4 + Qps ^ 2 * Am ^ 4) *
                (Cm ^ 2 - PowerSeries.C (2 * z0) * Qps * Am ^ 2 * Bm ^ 2) +
                4 * Qps ^ 2 * Am ^ 4 * Bm ^ 4 := by
              dsimp only [Cn, Am, Bm, Cm, Qps]; rw [hn_eq, eC]
              simp [Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul,
                Polynomial.coe_pow, Polynomial.coe_C, hcoe4]
            have hUm : jU m hm1 = legSeriesY * Am * Bminv := by simp [jU, hme, Am, Bminv]
            have hYm : jY m hm1 = Cm * Bminv ^ 2 := by simp [jY, hme, Cm, Bminv]
            rw [hUm, hYm, hAn, hBn, hCn]
            have hY4 : legSeriesY ^ 4 = Qps ^ 2 := by
              rw [show legSeriesY ^ 4 = (legSeriesY ^ 2) ^ 2 by ring, hQps]
            refine ⟨?_, ?_, ?_⟩
            · calc 1 - (legSeriesY * Am * Bminv) ^ 2 * (legSeriesY * Am * Bminv) ^ 2
                  = (Bm * Bminv) ^ 4 - legSeriesY ^ 4 * Am ^ 4 * Bminv ^ 4 := by rw [hBm_mul]; ring
                _ = (Bm ^ 4 - Qps ^ 2 * Am ^ 4) * Bminv ^ 4 := by rw [hY4]; ring
            · calc legSeriesY * Am * Bminv * (Cm * Bminv ^ 2) +
                    legSeriesY * Am * Bminv * (Cm * Bminv ^ 2)
                  = 2 * legSeriesY * Am * Cm * (Bm * Bminv) * Bminv ^ 3 := by rw [hBm_mul]; ring
                _ = legSeriesY * (2 * Am * Bm * Cm) * Bminv ^ 4 := by ring
            · calc (1 + (legSeriesY * Am * Bminv) ^ 2 * (legSeriesY * Am * Bminv) ^ 2) *
                      (Cm * Bminv ^ 2 * (Cm * Bminv ^ 2) -
                        PowerSeries.C (2 * z0) * (legSeriesY * Am * Bminv) * (legSeriesY * Am * Bminv)) +
                    2 * (legSeriesY * Am * Bminv) * (legSeriesY * Am * Bminv) *
                      ((legSeriesY * Am * Bminv) ^ 2 + (legSeriesY * Am * Bminv) ^ 2)
                  = ((Bm * Bminv) ^ 4 + legSeriesY ^ 4 * Am ^ 4 * Bminv ^ 4) *
                      (Cm ^ 2 * Bminv ^ 4 -
                        PowerSeries.C (2 * z0) * legSeriesY ^ 2 * Am ^ 2 * (Bm * Bminv) ^ 2 * Bminv ^ 2) +
                    4 * legSeriesY ^ 4 * Am ^ 4 * (Bm * Bminv) ^ 4 * Bminv ^ 4 := by rw [hBm_mul]; ring
                _ = ((Bm ^ 4 + Qps ^ 2 * Am ^ 4) *
                      (Cm ^ 2 - PowerSeries.C (2 * z0) * Qps * Am ^ 2 * Bm ^ 2) +
                      4 * Qps ^ 2 * Am ^ 4 * Bm ^ 4) * Bminv ^ 8 := by rw [hQps, hY4]; ring
        have hD_unit : IsUnit (1 - jU m hm1 ^ 2 * jU m hm1 ^ 2) := by
          rw [PowerSeries.isUnit_iff_constantCoeff]; simp [hu0]
        have hDinv_eq : psInv hD_unit = Bninv * Bm ^ 4 := by
          have h1u : (1 - jU m hm1 ^ 2 * jU m hm1 ^ 2) * psInv hD_unit = 1 := psInv_mul hD_unit
          have h2u : (1 - jU m hm1 ^ 2 * jU m hm1 ^ 2) * (Bninv * Bm ^ 4) = 1 := by
            rw [hident.1]
            calc Bn * Bminv ^ 4 * (Bninv * Bm ^ 4) = (Bn * Bninv) * (Bm * Bminv) ^ 4 := by ring
              _ = 1 := by rw [hBn_mul, hBm_mul]; ring
          exact hD_unit.mul_left_cancel (h1u.trans h2u.symm)
        have hUn_eq : jU n hn = (jU m hm1 * jY m hm1 + jU m hm1 * jY m hm1) * psInv hD_unit := by
          rw [hident.2.1, hDinv_eq]
          have hdef : jU n hn = legSeriesY * An * Bninv := by
            simp [jU, show n % 2 ≠ 1 by omega, An, Bninv]
          rw [hdef]
          calc legSeriesY * An * Bninv
              = legSeriesY * An * Bninv * (Bm * Bminv) ^ 4 := by rw [hBm_mul]; ring
            _ = legSeriesY * An * Bminv ^ 4 * (Bninv * Bm ^ 4) := by ring
        have hYn_eq : jY n hn = ((1 + jU m hm1 ^ 2 * jU m hm1 ^ 2) *
              (jY m hm1 * jY m hm1 - PowerSeries.C (2 * z0) * jU m hm1 * jU m hm1) +
            2 * jU m hm1 * jU m hm1 * (jU m hm1 ^ 2 + jU m hm1 ^ 2)) * (psInv hD_unit) ^ 2 := by
          rw [hident.2.2, hDinv_eq]
          have hdef : jY n hn = Cn * Bninv ^ 2 := by
            simp [jY, show n % 2 ≠ 1 by omega, Cn, Bninv]
          rw [hdef]
          calc Cn * Bninv ^ 2
              = Cn * Bninv ^ 2 * (Bm * Bminv) ^ 8 := by rw [hBm_mul]; ring
            _ = Cn * Bminv ^ 8 * (Bninv * Bm ^ 4) ^ 2 := by ring
        have hcast : (((m : ℤ) + (m : ℤ) : ℤ) : PowerSeries (ZOmega ℤ)) =
            ((n : ℤ) : PowerSeries (ZOmega ℤ)) := by
          rw [hn_eq]; push_cast; ring
        rw [hUn_eq, hYn_eq, ← hcast]
        exact hlaw
      · have hno : n % 2 = 1 := by omega
        set m := n / 2
        have hm1 : 1 ≤ m := by omega
        have hn_eq : n = 2 * m + 1 := by omega
        set o := if m % 2 = 1 then m else m + 1
        set e := if m % 2 = 1 then m + 1 else m
        have ho_odd : o % 2 = 1 := by dsimp only [o]; split_ifs <;> omega
        have he_ev : e % 2 = 0 := by dsimp only [e]; split_ifs <;> omega
        have ho_lt : o < n := by dsimp only [o]; split_ifs <;> omega
        have he_lt : e < n := by dsimp only [e]; split_ifs <;> omega
        have ho1 : 1 ≤ o := by dsimp only [o]; split_ifs <;> omega
        have he1 : 1 ≤ e := by dsimp only [e]; split_ifs <;> omega
        have hoe_sum : o + e = n := by dsimp only [o, e]; split_ifs <;> omega
        rcases ih o ho_lt ho1 with ⟨huo0, hyo0, hcuro, hdiffo⟩
        rcases ih e he_lt he1 with ⟨hue0, hye0, hcure, hdiffe⟩
        have hlaw := jacobi_add_ps_law (jU o ho1) (jY o ho1) (jU e he1) (jY e he1) o e
          huo0 hyo0 hue0 hye0 hcuro hcure hdiffo hdiffe
        dsimp only at hlaw
        have hstep := jacobiTriple_odd_step hm1
        dsimp only at hstep
        set Bo : PowerSeries (ZOmega ℤ) := ((jB o : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
        set Ao : PowerSeries (ZOmega ℤ) := ((jA o : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
        set Co : PowerSeries (ZOmega ℤ) := ((jC o : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
        set Boinv : PowerSeries (ZOmega ℤ) := psInv (jB_isUnit_ps o ho1)
        set Be : PowerSeries (ZOmega ℤ) := ((jB e : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
        set Ae : PowerSeries (ZOmega ℤ) := ((jA e : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
        set Ce : PowerSeries (ZOmega ℤ) := ((jC e : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
        set Beinv : PowerSeries (ZOmega ℤ) := psInv (jB_isUnit_ps e he1)
        set Bn : PowerSeries (ZOmega ℤ) := ((jB n : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
        set An : PowerSeries (ZOmega ℤ) := ((jA n : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
        set Cn : PowerSeries (ZOmega ℤ) := ((jC n : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
        set Bninv : PowerSeries (ZOmega ℤ) := psInv (jB_isUnit_ps n hn)
        set Qps : PowerSeries (ZOmega ℤ) := ((Qpoly z0 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
        have hBo_mul : Bo * Boinv = 1 := psInv_mul (jB_isUnit_ps o ho1)
        have hBe_mul : Be * Beinv = 1 := psInv_mul (jB_isUnit_ps e he1)
        have hBn_mul : Bn * Bninv = 1 := psInv_mul (jB_isUnit_ps n hn)
        have hQps : legSeriesY ^ 2 = Qps := legSeriesY_sq
        have hAn : An = Ao * Bo * Ce + Qps * Ae * Be * Co := by
          dsimp only [An, Ao, Bo, Ce, Ae, Be, Co, Qps]; rw [hn_eq, hstep.1]
          simp [Polynomial.coe_add, Polynomial.coe_mul, o, e]
        have hBn : Bn = Bo ^ 2 * Be ^ 2 - Qps * Ao ^ 2 * Ae ^ 2 := by
          dsimp only [Bn, Bo, Be, Ao, Ae, Qps]; rw [hn_eq, hstep.2.1]
          simp [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow, o, e]
        have hCn : Cn = (Bo ^ 2 * Be ^ 2 + Qps * Ao ^ 2 * Ae ^ 2) *
            (Co * Ce - PowerSeries.C (2 * z0) * Ao * Ae * Bo * Be) +
            2 * Ao * Ae * Bo * Be * (Ao ^ 2 * Be ^ 2 + Qps * Ae ^ 2 * Bo ^ 2) := by
          dsimp only [Cn, Bo, Be, Ao, Ae, Co, Ce, Qps]; rw [hn_eq, hstep.2.2]
          simp [Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul,
            Polynomial.coe_pow, Polynomial.coe_C, hcoe2, o, e]
        have hUo : jU o ho1 = Ao * Boinv := by simp [jU, ho_odd, Ao, Boinv]
        have hYo : jY o ho1 = legSeriesY * Co * Boinv ^ 2 := by simp [jY, ho_odd, Co, Boinv]
        have hUe : jU e he1 = legSeriesY * Ae * Beinv := by simp [jU, he_ev, Ae, Beinv]
        have hYe : jY e he1 = Ce * Beinv ^ 2 := by simp [jY, he_ev, Ce, Beinv]
        have hident :
            (1 - jU o ho1 ^ 2 * jU e he1 ^ 2) = Bn * Boinv ^ 2 * Beinv ^ 2 ∧
            (jU o ho1 * jY e he1 + jU e he1 * jY o ho1) = An * Boinv ^ 2 * Beinv ^ 2 ∧
            ((1 + jU o ho1 ^ 2 * jU e he1 ^ 2) *
                (jY o ho1 * jY e he1 - PowerSeries.C (2 * z0) * jU o ho1 * jU e he1) +
              2 * jU o ho1 * jU e he1 * (jU o ho1 ^ 2 + jU e he1 ^ 2)) =
              legSeriesY * Cn * Boinv ^ 4 * Beinv ^ 4 := by
          rw [hUo, hYo, hUe, hYe, hAn, hBn, hCn]
          refine ⟨?_, ?_, ?_⟩
          · calc 1 - (Ao * Boinv) ^ 2 * (legSeriesY * Ae * Beinv) ^ 2
                = (Bo * Boinv) ^ 2 * (Be * Beinv) ^ 2 -
                    legSeriesY ^ 2 * Ao ^ 2 * Ae ^ 2 * Boinv ^ 2 * Beinv ^ 2 := by
                  rw [hBo_mul, hBe_mul]; ring
              _ = (Bo ^ 2 * Be ^ 2 - Qps * Ao ^ 2 * Ae ^ 2) * Boinv ^ 2 * Beinv ^ 2 := by
                  rw [hQps]; ring
          · calc Ao * Boinv * (Ce * Beinv ^ 2) + legSeriesY * Ae * Beinv * (legSeriesY * Co * Boinv ^ 2)
                = Ao * (Bo * Boinv) * Ce * Boinv * Beinv ^ 2 +
                    legSeriesY ^ 2 * Ae * (Be * Beinv) * Co * Boinv ^ 2 * Beinv := by
                  rw [hBo_mul, hBe_mul]; ring
              _ = (Ao * Bo * Ce + Qps * Ae * Be * Co) * Boinv ^ 2 * Beinv ^ 2 := by
                  rw [hQps]; ring
          · calc (1 + (Ao * Boinv) ^ 2 * (legSeriesY * Ae * Beinv) ^ 2) *
                    (legSeriesY * Co * Boinv ^ 2 * (Ce * Beinv ^ 2) -
                      PowerSeries.C (2 * z0) * (Ao * Boinv) * (legSeriesY * Ae * Beinv)) +
                  2 * (Ao * Boinv) * (legSeriesY * Ae * Beinv) *
                    ((Ao * Boinv) ^ 2 + (legSeriesY * Ae * Beinv) ^ 2)
                = legSeriesY * (((Bo * Boinv) ^ 2 * (Be * Beinv) ^ 2 +
                      legSeriesY ^ 2 * Ao ^ 2 * Ae ^ 2 * Boinv ^ 2 * Beinv ^ 2) *
                    (Co * Ce * Boinv ^ 2 * Beinv ^ 2 -
                      PowerSeries.C (2 * z0) * Ao * Ae * (Bo * Boinv) * (Be * Beinv) * Boinv * Beinv) +
                  2 * Ao * Ae * (Bo * Boinv) * (Be * Beinv) * Boinv * Beinv *
                    (Ao ^ 2 * (Be * Beinv) ^ 2 * Boinv ^ 2 +
                      legSeriesY ^ 2 * Ae ^ 2 * (Bo * Boinv) ^ 2 * Beinv ^ 2)) := by
                  rw [hBo_mul, hBe_mul]; ring
              _ = legSeriesY * ((Bo ^ 2 * Be ^ 2 + Qps * Ao ^ 2 * Ae ^ 2) *
                    (Co * Ce - PowerSeries.C (2 * z0) * Ao * Ae * Bo * Be) +
                    2 * Ao * Ae * Bo * Be * (Ao ^ 2 * Be ^ 2 + Qps * Ae ^ 2 * Bo ^ 2)) *
                    Boinv ^ 4 * Beinv ^ 4 := by rw [hQps]; ring
        have hD_unit : IsUnit (1 - jU o ho1 ^ 2 * jU e he1 ^ 2) := by
          rw [PowerSeries.isUnit_iff_constantCoeff]; simp [huo0, hue0]
        have hDinv_eq : psInv hD_unit = Bninv * Bo ^ 2 * Be ^ 2 := by
          have h1u : (1 - jU o ho1 ^ 2 * jU e he1 ^ 2) * psInv hD_unit = 1 := psInv_mul hD_unit
          have h2u : (1 - jU o ho1 ^ 2 * jU e he1 ^ 2) * (Bninv * Bo ^ 2 * Be ^ 2) = 1 := by
            rw [hident.1]
            calc Bn * Boinv ^ 2 * Beinv ^ 2 * (Bninv * Bo ^ 2 * Be ^ 2)
                = (Bn * Bninv) * (Bo * Boinv) ^ 2 * (Be * Beinv) ^ 2 := by ring
              _ = 1 := by rw [hBn_mul, hBo_mul, hBe_mul]; ring
          exact hD_unit.mul_left_cancel (h1u.trans h2u.symm)
        have hUn_eq : jU n hn = (jU o ho1 * jY e he1 + jU e he1 * jY o ho1) * psInv hD_unit := by
          rw [hident.2.1, hDinv_eq]
          have hdef : jU n hn = An * Bninv := by simp [jU, hno, An, Bninv]
          rw [hdef]
          calc An * Bninv = An * Bninv * (Bo * Boinv) ^ 2 * (Be * Beinv) ^ 2 := by
                rw [hBo_mul, hBe_mul]; ring
            _ = An * Boinv ^ 2 * Beinv ^ 2 * (Bninv * Bo ^ 2 * Be ^ 2) := by ring
        have hYn_eq : jY n hn = ((1 + jU o ho1 ^ 2 * jU e he1 ^ 2) *
              (jY o ho1 * jY e he1 - PowerSeries.C (2 * z0) * jU o ho1 * jU e he1) +
            2 * jU o ho1 * jU e he1 * (jU o ho1 ^ 2 + jU e he1 ^ 2)) * (psInv hD_unit) ^ 2 := by
          rw [hident.2.2, hDinv_eq]
          have hdef : jY n hn = legSeriesY * Cn * Bninv ^ 2 := by simp [jY, hno, Cn, Bninv]
          rw [hdef]
          calc legSeriesY * Cn * Bninv ^ 2
              = legSeriesY * Cn * Bninv ^ 2 * (Bo * Boinv) ^ 4 * (Be * Beinv) ^ 4 := by
                rw [hBo_mul, hBe_mul]; ring
            _ = legSeriesY * Cn * Boinv ^ 4 * Beinv ^ 4 * (Bninv * Bo ^ 2 * Be ^ 2) ^ 2 := by ring
        have hcast : (((o : ℤ) + (e : ℤ) : ℤ) : PowerSeries (ZOmega ℤ)) =
            ((n : ℤ) : PowerSeries (ZOmega ℤ)) := by
          rw [← hoe_sum]; push_cast; ring
        rw [hUn_eq, hYn_eq, ← hcast]
        exact hlaw

private lemma jA_jB_wronskian_odd (n : ℕ) (hn : 1 ≤ n) (hno : n % 2 = 1) :
    (jA n).derivative * jB n - jA n * (jB n).derivative = C (n : ZOmega ℤ) * jC n := by
  have hprops := jU_jY_props n hn
  have hdiff := hprops.2.2.2
  set B : PowerSeries (ZOmega ℤ) := ((jB n : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
  set A : PowerSeries (ZOmega ℤ) := ((jA n : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
  set Cps : PowerSeries (ZOmega ℤ) := ((jC n : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
  set Binv : PowerSeries (ZOmega ℤ) := psInv (jB_isUnit_ps n hn)
  have hBmul : B * Binv = 1 := psInv_mul (jB_isUnit_ps n hn)
  have hU : jU n hn = A * Binv := by simp [jU, hno, A, Binv]
  have hY : jY n hn = legSeriesY * Cps * Binv ^ 2 := by simp [jY, hno, Cps, Binv]
  rw [hU, hY] at hdiff
  have hAB : A = (A * Binv) * B := by rw [mul_assoc, mul_comm Binv B, hBmul, mul_one]
  have hdAB := congr_arg (PowerSeries.derivative (ZOmega ℤ)) hAB
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hdiff] at hdAB
  have hps_eq : PowerSeries.derivative (ZOmega ℤ) A * B - A * PowerSeries.derivative (ZOmega ℤ) B =
      PowerSeries.C (n : ZOmega ℤ) * Cps := by
    calc PowerSeries.derivative (ZOmega ℤ) A * B - A * PowerSeries.derivative (ZOmega ℤ) B
        = (A * Binv * PowerSeries.derivative (ZOmega ℤ) B +
            B * (((n : ℤ) : PowerSeries (ZOmega ℤ)) * legSeriesG * (legSeriesY * Cps * Binv ^ 2))) * B -
            A * PowerSeries.derivative (ZOmega ℤ) B := by rw [← hdAB]
      _ = ((n : ℤ) : PowerSeries (ZOmega ℤ)) * (legSeriesG * legSeriesY) * Cps * (B * Binv) ^ 2 +
            A * (B * Binv - 1) * PowerSeries.derivative (ZOmega ℤ) B := by ring
      _ = PowerSeries.C (n : ZOmega ℤ) * Cps := by
            rw [legSeriesG_mul_Y, hBmul]; simp
  rw [PowerSeries.derivative_coe, PowerSeries.derivative_coe] at hps_eq
  have hcoe : (((jA n).derivative * jB n - jA n * (jB n).derivative : (ZOmega ℤ)[X]) :
      PowerSeries (ZOmega ℤ)) =
      ((C (n : ZOmega ℤ) * jC n : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) := by
    rw [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_mul,
      Polynomial.coe_C]
    exact hps_eq
  exact Polynomial.coe_injective (ZOmega ℤ) hcoe

private def ιQ : ZOmega ℤ →+* ZOmega ℚ := ZOmega.mapRingHom (Int.castRingHom ℚ)

private lemma ιQ_injective : Function.Injective ιQ :=
  ZOmega.mapRingHom_injective Int.cast_injective

private noncomputable def legLogF : PowerSeries (ZOmega ℚ) :=
  PowerSeries.mk fun k =>
    if k % 2 = 1 then
      ZOmega.of ((k : ℚ)⁻¹) * ιQ (legVal (k / 2))
    else 0

private lemma legLogF_constantCoeff : PowerSeries.constantCoeff legLogF = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [legLogF]

private lemma legLogF_coeff_one : PowerSeries.coeff 1 legLogF = 1 := by
  simp [legLogF, legVal_zero]

private lemma legLogF_deriv :
    PowerSeries.derivative (ZOmega ℚ) legLogF = PowerSeries.map ιQ legSeriesG := by
  ext k
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_map]
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [show m + m = 2 * m by ring]
    have hmod : (2 * m + 1) % 2 = 1 := by omega
    have hdiv : (2 * m + 1) / 2 = m := by omega
    simp only [legLogF, PowerSeries.coeff_mk, hmod, ↓reduceIte, hdiv, legSeriesG_coeff_even]
    have hne : ((2 * m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hcast : ((2 * m + 1 : ℕ) : ZOmega ℚ) = ZOmega.of ((2 * m + 1 : ℕ) : ℚ) := by
      apply ZOmega.ext <;> simp
    rw [show ((2 * m : ℕ) : ZOmega ℚ) + 1 = ((2 * m + 1 : ℕ) : ZOmega ℚ) by push_cast; ring, hcast]
    calc ZOmega.of (((2 * m + 1 : ℕ) : ℚ)⁻¹) * ιQ (legVal m) * ZOmega.of ((2 * m + 1 : ℕ) : ℚ)
        = (ZOmega.of (((2 * m + 1 : ℕ) : ℚ)⁻¹) * ZOmega.of ((2 * m + 1 : ℕ) : ℚ)) * ιQ (legVal m) := by ring
      _ = ZOmega.of ((((2 * m + 1 : ℕ) : ℚ)⁻¹) * ((2 * m + 1 : ℕ) : ℚ)) * ιQ (legVal m) := by rw [← map_mul]
      _ = ιQ (legVal m) := by
          rw [inv_mul_cancel₀ hne, map_one, one_mul]
  · have hmod : (2 * m + 1 + 1) % 2 ≠ 1 := by omega
    simp [legLogF, hmod, legSeriesG_coeff_odd]

private lemma ps_map_derivative {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : PowerSeries R) :
    PowerSeries.derivative S (PowerSeries.map f s) =
      PowerSeries.map f (PowerSeries.derivative R s) := by
  ext k
  simp [PowerSeries.coeff_derivative, PowerSeries.coeff_map, map_mul, map_add, map_natCast, map_one]

private lemma ps_constantCoeff_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : PowerSeries R) :
    PowerSeries.constantCoeff (PowerSeries.map f s) = f (PowerSeries.constantCoeff s) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff]

private lemma legLogF_subst_eq (u y : PowerSeries (ZOmega ℤ)) (n : ℤ)
    (hu0 : PowerSeries.constantCoeff u = 0)
    (hy0 : PowerSeries.constantCoeff y = 1)
    (hcur : y ^ 2 = 1 - PowerSeries.C (2 * z0) * u ^ 2 + u ^ 4)
    (hdiff : PowerSeries.derivative (ZOmega ℤ) u = (n : PowerSeries (ZOmega ℤ)) * legSeriesG * y) :
    PowerSeries.subst (PowerSeries.map ιQ u) legLogF =
      (n : PowerSeries (ZOmega ℚ)) * legLogF := by
  have hu_subst : PowerSeries.HasSubst u := PowerSeries.HasSubst.of_constantCoeff_zero' hu0
  have huQ_0 : PowerSeries.constantCoeff (PowerSeries.map ιQ u) = 0 := by
    rw [ps_constantCoeff_map, hu0, map_zero]
  have huQ_subst : PowerSeries.HasSubst (PowerSeries.map ιQ u) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' huQ_0
  have hsubst_one : PowerSeries.subst u (1 : PowerSeries (ZOmega ℤ)) = 1 := by
    rw [← PowerSeries.coe_substAlgHom hu_subst, map_one]
  -- Show (y * g.subst u)^2 = 1 in PowerSeries (ZOmega ℤ), then cancel (y * g.subst u + 1) in ZOmega ℚ!
  have hQ_subst : PowerSeries.subst u ((Qpoly z0 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) = y ^ 2 := by
    have hQ : ((Qpoly z0 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) =
        1 - PowerSeries.C (2 * z0) * PowerSeries.X ^ 2 + PowerSeries.X ^ 4 := by
      simp [Qpoly]
    rw [hQ, PowerSeries.subst_add hu_subst, PowerSeries.subst_sub hu_subst,
      hsubst_one, PowerSeries.subst_mul hu_subst,
      PowerSeries.subst_C, PowerSeries.subst_pow hu_subst, PowerSeries.subst_pow hu_subst,
      PowerSeries.subst_X hu_subst, hcur]; rfl
  have hsq1 : (y * PowerSeries.subst u legSeriesG) ^ 2 = 1 := by
    have h := congr_arg (PowerSeries.subst u) Qpoly_mul_legSeriesG_sq
    rw [PowerSeries.subst_mul hu_subst, PowerSeries.subst_pow hu_subst,
      hsubst_one, hQ_subst] at h
    linear_combination h
  have hmap_subst_g : PowerSeries.map ιQ (PowerSeries.subst u legSeriesG) =
      PowerSeries.subst (PowerSeries.map ιQ u) (PowerSeries.map ιQ legSeriesG) :=
    PowerSeries.map_subst hu_subst legSeriesG
  have hsqQ : (PowerSeries.map ιQ y *
      PowerSeries.subst (PowerSeries.map ιQ u) (PowerSeries.map ιQ legSeriesG)) ^ 2 = 1 := by
    have h := congr_arg (PowerSeries.map ιQ) hsq1
    rw [map_pow, map_mul, hmap_subst_g, map_one] at h
    exact h
  have hprod0 : (PowerSeries.map ιQ y *
        PowerSeries.subst (PowerSeries.map ιQ u) (PowerSeries.map ιQ legSeriesG) + 1) *
      (PowerSeries.map ιQ y *
        PowerSeries.subst (PowerSeries.map ιQ u) (PowerSeries.map ιQ legSeriesG) - 1) = 0 := by
    linear_combination hsqQ
  have hplus_unit : IsUnit (PowerSeries.map ιQ y *
      PowerSeries.subst (PowerSeries.map ιQ u) (PowerSeries.map ιQ legSeriesG) + 1) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_add, map_mul, map_one,
      ps_constantCoeff_map, hy0, map_one, one_mul]
    have hgs0 : PowerSeries.constantCoeff
        (PowerSeries.subst (PowerSeries.map ιQ u) (PowerSeries.map ιQ legSeriesG)) = 1 := by
      change MvPowerSeries.constantCoeff _ = 1
      rw [PowerSeries.constantCoeff_subst huQ_subst]
      rw [finsum_eq_single _ 0]
      · simp [PowerSeries.coeff_zero_eq_constantCoeff, legSeriesG_constantCoeff]
      · intro d hd
        change PowerSeries.coeff d _ • PowerSeries.constantCoeff ((PowerSeries.map ιQ u) ^ d) = 0
        rw [map_pow, huQ_0, zero_pow hd, smul_zero]
    rw [hgs0]
    exact ⟨⟨(2 : ZOmega ℚ), ZOmega.of (2⁻¹ : ℚ),
      by apply ZOmega.ext <;> simp, by apply ZOmega.ext <;> simp⟩, by norm_num⟩
  have hyg1 : PowerSeries.map ιQ y *
      PowerSeries.subst (PowerSeries.map ιQ u) (PowerSeries.map ιQ legSeriesG) = 1 :=
    sub_eq_zero.mp (hplus_unit.mul_right_eq_zero.mp hprod0)
  apply PowerSeries.derivative.ext
  · have hdn : PowerSeries.derivative (ZOmega ℚ) (n : PowerSeries (ZOmega ℚ)) = 0 := by
      have hnC : (n : PowerSeries (ZOmega ℚ)) = PowerSeries.C (n : ZOmega ℚ) := by
        rw [map_intCast]
      rw [hnC, PowerSeries.derivative_C]
    rw [PowerSeries.derivative_subst huQ_subst, legLogF_deriv, ps_map_derivative, hdiff]
    simp only [map_mul, map_intCast, Derivation.leibniz, hdn,
      smul_eq_mul, mul_zero, add_zero, legLogF_deriv]
    calc PowerSeries.subst (PowerSeries.map ιQ u) (PowerSeries.map ιQ legSeriesG) *
            ((n : PowerSeries (ZOmega ℚ)) * PowerSeries.map ιQ legSeriesG * PowerSeries.map ιQ y)
        = (n : PowerSeries (ZOmega ℚ)) * PowerSeries.map ιQ legSeriesG *
            (PowerSeries.map ιQ y * PowerSeries.subst (PowerSeries.map ιQ u) (PowerSeries.map ιQ legSeriesG)) := by
          ring
      _ = (n : PowerSeries (ZOmega ℚ)) * PowerSeries.map ιQ legSeriesG := by rw [hyg1, mul_one]
  · change MvPowerSeries.constantCoeff _ = PowerSeries.constantCoeff _
    rw [PowerSeries.constantCoeff_subst huQ_subst, map_mul, legLogF_constantCoeff, mul_zero]
    rw [finsum_eq_single _ 0]
    · simp [PowerSeries.coeff_zero_eq_constantCoeff, legLogF_constantCoeff]
    · intro d hd
      change PowerSeries.coeff d _ • PowerSeries.constantCoeff ((PowerSeries.map ιQ u) ^ d) = 0
      rw [map_pow, huQ_0, zero_pow hd, smul_zero]

private lemma coeff_pow_eq_of_coeff_lt {R : Type*} [CommRing R] (a b : PowerSeries R) (N : ℕ)
    (h : ∀ j < N, PowerSeries.coeff j a = PowerSeries.coeff j b) :
    ∀ d : ℕ, ∀ j < N, PowerSeries.coeff j (a ^ d) = PowerSeries.coeff j (b ^ d) := by
  intro d
  induction d with
  | zero => intro j _; simp
  | succ d ih =>
    intro j hj
    rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    rw [ih x (by omega), h (j - x) (by omega)]

private lemma coeff_pow_eq_zero_of_lt {R : Type*} [CommRing R] (a : PowerSeries R)
    (ha0 : PowerSeries.constantCoeff a = 0) :
    ∀ d n : ℕ, n < d → PowerSeries.coeff n (a ^ d) = 0 := by
  intro d
  induction d with
  | zero => intro n hn; omega
  | succ d ih =>
    intro n hn
    rw [pow_succ, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_range] at hx
    by_cases hx2 : n - x = 0
    · rw [hx2, PowerSeries.coeff_zero_eq_constantCoeff, ha0, mul_zero]
    · rw [ih x (by omega), zero_mul]

private lemma coeff_subst_eq_sum {R : Type*} [CommRing R] (f a : PowerSeries R)
    (ha0 : PowerSeries.constantCoeff a = 0) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.subst a f) =
      ∑ d ∈ range (n + 1), PowerSeries.coeff d f * PowerSeries.coeff n (a ^ d) := by
  have ha : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero' ha0
  rw [PowerSeries.coeff_subst' ha]
  rw [finsum_eq_sum_of_support_subset _ (s := range (n + 1))]
  · apply Finset.sum_congr rfl
    intro d _; simp [smul_eq_mul]
  · intro d hd
    simp only [Function.mem_support, smul_eq_mul, ne_eq] at hd
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hge
    exact hd (by rw [coeff_pow_eq_zero_of_lt a ha0 d n (by omega), mul_zero])

private lemma legLogF_subst_injective (a b : PowerSeries (ZOmega ℚ))
    (ha0 : PowerSeries.constantCoeff a = 0) (hb0 : PowerSeries.constantCoeff b = 0)
    (heq : PowerSeries.subst a legLogF = PowerSeries.subst b legLogF) :
    a = b := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff, ha0, hb0]
    | succ k =>
      have hn := congr_arg (PowerSeries.coeff (k + 1)) heq
      rw [coeff_subst_eq_sum _ _ ha0, coeff_subst_eq_sum _ _ hb0] at hn
      have hsplit : ∀ c : PowerSeries (ZOmega ℚ),
          ∑ d ∈ range (k + 1 + 1),
            PowerSeries.coeff d legLogF * PowerSeries.coeff (k + 1) (c ^ d) =
          (∑ d ∈ range k,
            PowerSeries.coeff (d + 1 + 1) legLogF * PowerSeries.coeff (k + 1) (c ^ (d + 1 + 1))) +
            PowerSeries.coeff (k + 1) c := by
        intro c
        rw [Finset.sum_range_succ', Finset.sum_range_succ']
        simp only [PowerSeries.coeff_zero_eq_constantCoeff, legLogF_constantCoeff,
          zero_mul, add_zero, zero_add, legLogF_coeff_one, one_mul, pow_one]
      rw [hsplit a, hsplit b] at hn
      have htail : ∀ d ∈ range k,
          PowerSeries.coeff (d + 1 + 1) legLogF * PowerSeries.coeff (k + 1) (a ^ (d + 1 + 1)) =
          PowerSeries.coeff (d + 1 + 1) legLogF * PowerSeries.coeff (k + 1) (b ^ (d + 1 + 1)) := by
        intro d _
        congr 1
        rw [pow_succ a (d + 1), pow_succ b (d + 1), PowerSeries.coeff_mul, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mem_range] at hx
        by_cases hx2 : k + 1 - x = 0
        · rw [hx2, PowerSeries.coeff_zero_eq_constantCoeff, ha0, hb0, mul_zero, mul_zero]
        · by_cases hx1 : x = 0
          · rw [hx1, coeff_pow_eq_zero_of_lt a ha0 (d + 1) 0 (by omega),
              coeff_pow_eq_zero_of_lt b hb0 (d + 1) 0 (by omega), zero_mul, zero_mul]
          · rw [coeff_pow_eq_of_coeff_lt a b (k + 1) ih (d + 1) x (by omega), ih (k + 1 - x) (by omega)]
      rw [Finset.sum_congr rfl htail] at hn
      exact add_left_cancel hn

private lemma jacobi_consec_diff (m : ℕ) (hm1 : 1 ≤ m) :
    let o := if m % 2 = 1 then m else m + 1
    let e := if m % 2 = 1 then m + 1 else m
    let sgn : ZOmega ℤ := if m % 2 = 1 then -1 else 1
    jA o * jB o * jC e - Qpoly z0 * jA e * jB e * jC o =
      C sgn * X * jB (2 * m + 1) := by
  intro o e sgn
  have ho_odd : o % 2 = 1 := by dsimp only [o]; split_ifs <;> omega
  have he_ev : e % 2 = 0 := by dsimp only [e]; split_ifs <;> omega
  have ho1 : 1 ≤ o := by dsimp only [o]; split_ifs <;> omega
  have he1 : 1 ≤ e := by dsimp only [e]; split_ifs <;> omega
  have hoe_diff : (o : ℤ) + (-(e : ℤ)) = if m % 2 = 1 then -1 else 1 := by
    dsimp only [o, e]; split_ifs <;> omega
  rcases jU_jY_props o ho1 with ⟨huo0, hyo0, hcuro, hdiffo⟩
  rcases jU_jY_props e he1 with ⟨hue0, hye0, hcure, hdiffe⟩
  -- Apply jacobi_add_ps_law to (jU o, jY o) and (-jU e, jY e)!
  have hnege_0 : PowerSeries.constantCoeff (-jU e he1) = 0 := by simp [hue0]
  have hnege_cur : jY e he1 ^ 2 =
      1 - PowerSeries.C (2 * z0) * (-jU e he1) ^ 2 + (-jU e he1) ^ 4 := by
    rw [hcure]; ring
  have hnege_diff : PowerSeries.derivative (ZOmega ℤ) (-jU e he1) =
      ((-(e : ℤ) : ℤ) : PowerSeries (ZOmega ℤ)) * legSeriesG * jY e he1 := by
    rw [map_neg, hdiffe]; push_cast; ring
  have hlaw := jacobi_add_ps_law (jU o ho1) (jY o ho1) (-jU e he1) (jY e he1) o (-(e : ℤ))
    huo0 hyo0 hnege_0 hye0 hcuro hnege_cur hdiffo hnege_diff
  dsimp only at hlaw
  set D := 1 - jU o ho1 ^ 2 * (-jU e he1) ^ 2
  set N := jU o ho1 * jY e he1 + (-jU e he1) * jY o ho1
  have hD_unit : IsUnit D := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp [D, huo0, hue0]
  set Dinv : PowerSeries (ZOmega ℤ) := psInv hD_unit
  set udiff := N * Dinv
  have hlog_diff := legLogF_subst_eq udiff _ ((o : ℤ) + (-(e : ℤ)))
    hlaw.1 hlaw.2.1 hlaw.2.2.1 hlaw.2.2.2
  -- Also legLogF(sgn * X) = sgn * legLogF since legLogF is odd!
  have hsgn_X : PowerSeries.subst (PowerSeries.C (ιQ sgn) * PowerSeries.X) legLogF =
      (((o : ℤ) + (-(e : ℤ)) : ℤ) : PowerSeries (ZOmega ℚ)) * legLogF := by
    have hsgn_val : ιQ sgn = if m % 2 = 1 then -1 else 1 := by
      dsimp only [sgn]; split_ifs <;> simp
    have hX0 : PowerSeries.constantCoeff (PowerSeries.C (ιQ sgn) * PowerSeries.X) = 0 := by simp
    ext k
    rw [coeff_subst_eq_sum _ _ hX0]
    have hpowX : ∀ d : ℕ, PowerSeries.coeff k ((PowerSeries.C (ιQ sgn) * PowerSeries.X) ^ d) =
        if d = k then (ιQ sgn) ^ k else 0 := by
      intro d
      rw [mul_pow, ← map_pow, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      by_cases h : d = k
      · subst h; simp
      · have hk' : k ≠ d := fun heq => h heq.symm
        simp [h, hk']
    simp only [hpowX, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_self, ↓reduceIte]
    rw [hoe_diff]
    rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · rw [show r + r = 2 * r by ring]
      have h0 : PowerSeries.coeff (2 * r) legLogF = 0 := by simp [legLogF]
      rw [h0, zero_mul]
      split_ifs <;> simp [h0]
    · have hodd_pow : (ιQ sgn) ^ (2 * r + 1) = ιQ sgn := by
        rw [hsgn_val]; split_ifs <;> simp [pow_succ]
      rw [hodd_pow, hsgn_val]
      split_ifs <;> simp [mul_comm]
  have hudiff_eq : PowerSeries.map ιQ udiff = PowerSeries.C (ιQ sgn) * PowerSeries.X := by
    apply legLogF_subst_injective
    · rw [ps_constantCoeff_map, hlaw.1, map_zero]
    · simp
    · rw [hlog_diff, hsgn_X]
  have hudiff_Z : udiff = PowerSeries.C sgn * PowerSeries.X := by
    ext k
    apply ιQ_injective
    have hk := congr_arg (PowerSeries.coeff k) hudiff_eq
    rw [PowerSeries.coeff_map, PowerSeries.coeff_C_mul, PowerSeries.coeff_X] at hk
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
    split_ifs at hk ⊢ <;> simpa using hk
  -- Clear denominators B_o^2 B_e^2 - Q A_o^2 A_e^2 = jB (2*m + 1)
  have hN_eq : N = PowerSeries.C sgn * PowerSeries.X * D := by
    calc N = udiff * D := by
          dsimp only [udiff]; rw [mul_assoc, mul_comm Dinv D, psInv_mul hD_unit, mul_one]
      _ = PowerSeries.C sgn * PowerSeries.X * D := by rw [hudiff_Z]
  have hstep := jacobiTriple_odd_step hm1
  dsimp only at hstep
  set Bo : PowerSeries (ZOmega ℤ) := ((jB o : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
  set Ao : PowerSeries (ZOmega ℤ) := ((jA o : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
  set Co : PowerSeries (ZOmega ℤ) := ((jC o : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
  set Boinv : PowerSeries (ZOmega ℤ) := psInv (jB_isUnit_ps o ho1)
  set Be : PowerSeries (ZOmega ℤ) := ((jB e : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
  set Ae : PowerSeries (ZOmega ℤ) := ((jA e : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
  set Ce : PowerSeries (ZOmega ℤ) := ((jC e : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
  set Beinv : PowerSeries (ZOmega ℤ) := psInv (jB_isUnit_ps e he1)
  set Qps : PowerSeries (ZOmega ℤ) := ((Qpoly z0 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
  have hBo_mul : Bo * Boinv = 1 := psInv_mul (jB_isUnit_ps o ho1)
  have hBe_mul : Be * Beinv = 1 := psInv_mul (jB_isUnit_ps e he1)
  have hUo : jU o ho1 = Ao * Boinv := by simp [jU, ho_odd, Ao, Boinv]
  have hYo : jY o ho1 = legSeriesY * Co * Boinv ^ 2 := by simp [jY, ho_odd, Co, Boinv]
  have hUe : jU e he1 = legSeriesY * Ae * Beinv := by simp [jU, he_ev, Ae, Beinv]
  have hYe : jY e he1 = Ce * Beinv ^ 2 := by simp [jY, he_ev, Ce, Beinv]
  have hN_mul : N * Bo ^ 2 * Be ^ 2 = Ao * Bo * Ce - Qps * Ae * Be * Co := by
    dsimp only [N]; rw [hUo, hYo, hUe, hYe]
    calc (Ao * Boinv * (Ce * Beinv ^ 2) + -(legSeriesY * Ae * Beinv) * (legSeriesY * Co * Boinv ^ 2)) *
            Bo ^ 2 * Be ^ 2
        = Ao * Bo * (Bo * Boinv) * Ce * (Be * Beinv) ^ 2 -
            legSeriesY ^ 2 * Ae * Be * (Be * Beinv) * Co * (Bo * Boinv) ^ 2 := by ring
      _ = Ao * Bo * Ce - Qps * Ae * Be * Co := by rw [hBo_mul, hBe_mul, legSeriesY_sq]; ring
  have hD_mul : D * Bo ^ 2 * Be ^ 2 = Bo ^ 2 * Be ^ 2 - Qps * Ao ^ 2 * Ae ^ 2 := by
    dsimp only [D]; rw [hUo, hUe]
    calc (1 - (Ao * Boinv) ^ 2 * (-(legSeriesY * Ae * Beinv)) ^ 2) * Bo ^ 2 * Be ^ 2
        = Bo ^ 2 * Be ^ 2 - legSeriesY ^ 2 * Ao ^ 2 * Ae ^ 2 * (Bo * Boinv) ^ 2 * (Be * Beinv) ^ 2 := by ring
      _ = Bo ^ 2 * Be ^ 2 - Qps * Ao ^ 2 * Ae ^ 2 := by rw [hBo_mul, hBe_mul, legSeriesY_sq]; ring
  have hps : (((jA o * jB o * jC e - Qpoly z0 * jA e * jB e * jC o : (ZOmega ℤ)[X]) :
      PowerSeries (ZOmega ℤ))) =
      ((C sgn * X * jB (2 * m + 1) : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) := by
    rw [hstep.2.1]
    simp only [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C,
      Polynomial.coe_X]
    change Ao * Bo * Ce - Qps * Ae * Be * Co =
      PowerSeries.C sgn * PowerSeries.X * (Bo ^ 2 * Be ^ 2 - Qps * Ao ^ 2 * Ae ^ 2)
    rw [← hN_mul, ← hD_mul, hN_eq]; ring
  exact Polynomial.coe_injective (ZOmega ℤ) hps

private lemma reflect_succ_eq_X_mul {R : Type*} [CommRing R] (d : ℕ) (f : R[X])
    (hf : f.natDegree ≤ d) :
    f.reflect (d + 1) = X * f.reflect d := by
  ext k
  rw [Polynomial.coeff_reflect]
  cases k with
  | zero =>
    rw [Polynomial.revAt_zero, Polynomial.coeff_X_mul_zero]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  | succ k =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_reflect]
    by_cases hk : k ≤ d
    · rw [Polynomial.revAt_le (by omega : k + 1 ≤ d + 1), Polynomial.revAt_le hk]
      congr 1; omega
    · rw [Polynomial.revAt_eq_self_of_lt (by omega : d + 1 < k + 1),
        Polynomial.revAt_eq_self_of_lt (by omega : d < k),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

private lemma X_mul_cancel_poly {R : Type*} [CommRing R] {f g : R[X]} (h : X * f = X * g) : f = g := by
  ext k
  have hk := congr_arg (fun P => P.coeff (k + 1)) h
  simpa [Polynomial.coeff_X_mul] using hk

private lemma reflect_derivative {R : Type*} [CommRing R] (d : ℕ) (hd : 1 ≤ d) (f : R[X])
    (hf : f.natDegree ≤ d) :
    f.derivative.reflect (d - 1) = C (d : R) * f.reflect d - X * (f.reflect d).derivative := by
  ext k
  rw [Polynomial.coeff_reflect, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_reflect]
  cases k with
  | zero =>
    rw [Polynomial.revAt_zero, Polynomial.revAt_zero, Polynomial.coeff_X_mul_zero, sub_zero,
      Polynomial.coeff_derivative]
    rw [show d - 1 + 1 = d by omega]
    have hcast : ((d - 1 : ℕ) : R) + 1 = (d : R) := by
      have := congr_arg (Nat.cast (R := R)) (show d - 1 + 1 = d by omega)
      push_cast at this; exact this
    linear_combination f.coeff d * hcast
  | succ k =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, Polynomial.coeff_derivative,
      Polynomial.coeff_reflect]
    by_cases hk1 : k + 1 ≤ d - 1
    · rw [Polynomial.revAt_le hk1, Polynomial.revAt_le (by omega : k + 1 ≤ d)]
      have hsub1 : d - 1 - (k + 1) + 1 = d - (k + 1) := by omega
      have hsub2 : ((d - 1 - (k + 1) : ℕ) : R) + 1 = (d : R) - ((k : R) + 1) := by
        have hnat : d - 1 - (k + 1) + 1 + (k + 1) = d := by omega
        have := congr_arg (Nat.cast (R := R)) hnat
        push_cast at this
        linear_combination this
      rw [hsub1, hsub2]; ring
    · by_cases hk2 : k + 1 = d
      · rw [hk2, Polynomial.revAt_eq_self_of_lt (by omega : d - 1 < d),
          Polynomial.revAt_le le_rfl, Nat.sub_self]
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < d + 1), zero_mul]
        have hk2R : (k : R) + 1 = (d : R) := by
          have := congr_arg (Nat.cast (R := R)) hk2
          push_cast at this; exact this
        rw [hk2R]; ring
      · rw [Polynomial.revAt_eq_self_of_lt (by omega : d - 1 < k + 1),
          Polynomial.revAt_eq_self_of_lt (by omega : d < k + 1),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < k + 1 + 1),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < k + 1)]
        ring

private lemma jacobiTriple_reflect (n : ℕ) (hn : 1 ≤ n) :
    (if n % 2 = 1 then
      let s : ZOmega ℤ := (-1 : ZOmega ℤ) ^ ((n - 1) / 2)
      (jA n).reflect (n ^ 2) = C s * jB n ∧
      (jB n).reflect (n ^ 2) = C s * jA n ∧
      (jC n).reflect (2 * n ^ 2 - 2) = jC n
    else
      let t : ZOmega ℤ := (-1 : ZOmega ℤ) ^ (n / 2)
      (jA n).reflect (n ^ 2 - 2) = C (-t) * jA n ∧
      (jB n).reflect (n ^ 2) = C t * jB n ∧
      (jC n).reflect (2 * n ^ 2) = jC n) := by
  have hQref : (Qpoly z0).reflect 4 = Qpoly z0 := Qpoly_reflect z0
  have hQdeg : (Qpoly z0).natDegree ≤ 4 := Qpoly_natDegree_le z0
  have href_sub : ∀ (d : ℕ) (f g : (ZOmega ℤ)[X]),
      (f - g).reflect d = f.reflect d - g.reflect d := fun d f g => by
    rw [sub_eq_add_neg, Polynomial.reflect_add, show (-g) = C (-1) * g by simp,
      Polynomial.reflect_C_mul]; simp [sub_eq_add_neg]
  have href_2mul : ∀ (d : ℕ) (f : (ZOmega ℤ)[X]),
      (2 * f).reflect d = 2 * f.reflect d := fun d f => by
    rw [show (2 : (ZOmega ℤ)[X]) = C 2 from (map_ofNat C 2).symm, Polynomial.reflect_C_mul]
  have href_4mul : ∀ (d : ℕ) (f : (ZOmega ℤ)[X]),
      (4 * f).reflect d = 4 * f.reflect d := fun d f => by
    rw [show (4 : (ZOmega ℤ)[X]) = C 4 from (map_ofNat C 4).symm, Polynomial.reflect_C_mul]
  have hdeg_2mul : ∀ (f : (ZOmega ℤ)[X]) (a : ℕ), f.natDegree ≤ a →
      (2 * f).natDegree ≤ a := fun f a hf => by
    rw [show (2 : (ZOmega ℤ)[X]) = C 2 from (map_ofNat C 2).symm]
    exact le_trans (Polynomial.natDegree_C_mul_le _ _) hf
  have hdeg_4mul : ∀ (f : (ZOmega ℤ)[X]) (a : ℕ), f.natDegree ≤ a →
      (4 * f).natDegree ≤ a := fun f a hf => by
    rw [show (4 : (ZOmega ℤ)[X]) = C 4 from (map_ofNat C 4).symm]
    exact le_trans (Polynomial.natDegree_C_mul_le _ _) hf
  have href_pow : ∀ {d : ℕ} (k : ℕ) {f : (ZOmega ℤ)[X]}, f.natDegree ≤ d →
      (f ^ k).reflect (k * d) = (f.reflect d) ^ k := fun {d} k {f} hf => by
    rw [mul_comm]; exact reflect_pow_eq f d hf k
  have hmul_deg : ∀ (p q : (ZOmega ℤ)[X]) (a b : ℕ), p.natDegree ≤ a → q.natDegree ≤ b →
      (p * q).natDegree ≤ a + b := fun p q a b hp hq =>
    le_trans Polynomial.natDegree_mul_le (Nat.add_le_add hp hq)
  have hpow_deg : ∀ (p : (ZOmega ℤ)[X]) (k a : ℕ), p.natDegree ≤ a →
      (p ^ k).natDegree ≤ k * a := fun p k a hp =>
    le_trans Polynomial.natDegree_pow_le (Nat.mul_le_mul_left k hp)
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst h1
      simp only [Nat.one_mod, ↓reduceIte, Nat.sub_self, Nat.zero_div, pow_zero, map_one,
        one_mul, one_pow, mul_one, jacobiTriple_one]
      exact ⟨by rw [← pow_one (X : (ZOmega ℤ)[X]), Polynomial.reflect_monomial]; simp [Polynomial.revAt_le],
             by rw [Polynomial.reflect_one]; simp,
             by rw [Polynomial.reflect_one]; simp⟩
    · by_cases hev : n % 2 = 0
      · simp only [show n % 2 ≠ 1 by omega, ↓reduceIte]
        set m := n / 2
        have hm1 : 1 ≤ m := by omega
        have hmn : m < n := by omega
        have hn_eq : n = 2 * m := by omega
        have hdiv_eq : n / 2 = m := rfl
        have ihm := ih m hmn hm1
        have hdm := jacobiTriple_natDegree_le m hm1
        by_cases hmo : m % 2 = 1
        · simp only [hmo, ↓reduceIte] at ihm hdm
          rcases ihm with ⟨rA, rB, rC⟩
          rcases hdm with ⟨dA, dB, dC⟩
          have dB' : (jB m).natDegree ≤ m ^ 2 := by omega
          have hm2 : 1 ≤ m ^ 2 := by nlinarith
          rcases jacobiTriple_even_of_odd hmo with ⟨eA, eB, eC⟩
          have ht : (-1 : ZOmega ℤ) ^ m = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr hmo)
          set s : ZOmega ℤ := (-1 : ZOmega ℤ) ^ ((m - 1) / 2)
          have hs2 : s ^ 2 = 1 := by dsimp only [s]; rw [← pow_mul, mul_comm, pow_mul]; simp
          rw [hn_eq, ht, neg_neg, eA, eB, eC]
          refine ⟨?_, ?_, ?_⟩
          · have hdeg_eq : (2 * m) ^ 2 - 2 = (m ^ 2 + m ^ 2) + (2 * m ^ 2 - 2) := by
              have : (2 * m) ^ 2 = 4 * m ^ 2 := by ring
              omega
            rw [hdeg_eq, Polynomial.reflect_mul _ _ (hmul_deg _ _ _ _ (hdeg_2mul _ _ dA) dB') dC,
              Polynomial.reflect_mul _ _ (hdeg_2mul _ _ dA) dB',
              href_2mul, rA, rB, rC]
            have hCs2 : C s * C s = 1 := by rw [← map_mul, ← pow_two, hs2, map_one]
            simp only [map_one, one_mul]
            linear_combination 2 * jA m * jB m * jC m * hCs2
          · rw [href_sub, show (2 * m) ^ 2 = 4 * m ^ 2 by ring,
              href_pow 4 dB', href_pow 4 dA, rB, rA]
            have hCs4 : C s ^ 4 = 1 := by
              rw [← map_pow, show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2, one_pow, map_one]
            simp only [mul_pow, hCs4, one_mul, map_neg, map_one]; ring
          · have hdeg8 : 2 * (2 * m) ^ 2 = 4 * m ^ 2 + 4 * m ^ 2 := by ring
            have hdeg4 : 4 * m ^ 2 = 4 + 2 * (2 * m ^ 2 - 2) := by omega
            have hdeg4' : 4 * m ^ 2 = 2 * m ^ 2 + 2 * m ^ 2 := by ring
            have hCs2 : C s ^ 2 = 1 := by rw [← map_pow, hs2, map_one]
            have hCs4 : C s ^ 4 = 1 := by
              rw [← map_pow, show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2, one_pow, map_one]
            rw [Polynomial.reflect_add, hdeg8]
            have hdegL : (jB m ^ 4 + jA m ^ 4).natDegree ≤ 4 * m ^ 2 :=
              le_trans (Polynomial.natDegree_add_le _ _)
                (max_le (hpow_deg _ 4 _ dB') (hpow_deg _ 4 _ dA))
            have hdegR : (Qpoly z0 * jC m ^ 2 - C (2 * z0) * jA m ^ 2 * jB m ^ 2).natDegree ≤ 4 * m ^ 2 := by
              refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
              · have := hmul_deg _ _ _ _ hQdeg (hpow_deg _ 2 _ dC); omega
              · have := hmul_deg _ _ _ _ (le_trans (Polynomial.natDegree_C_mul_le (2 * z0) _) (hpow_deg _ 2 _ dA))
                  (hpow_deg _ 2 _ dB'); omega
            rw [Polynomial.reflect_mul _ _ hdegL hdegR,
              Polynomial.reflect_mul _ _ (hdeg_4mul _ _ (hpow_deg _ 4 _ dA)) (hpow_deg _ 4 _ dB'),
              Polynomial.reflect_add, href_sub, href_4mul,
              href_pow 4 dB', href_pow 4 dA, rB, rA]
            have hR1 : (Qpoly z0 * jC m ^ 2).reflect (4 * m ^ 2) = Qpoly z0 * jC m ^ 2 := by
              rw [hdeg4, Polynomial.reflect_mul _ _ hQdeg (hpow_deg _ 2 _ dC),
                hQref, href_pow 2 dC, rC]
            have hR2 : (C (2 * z0) * jA m ^ 2 * jB m ^ 2).reflect (4 * m ^ 2) =
                C (2 * z0) * jA m ^ 2 * jB m ^ 2 := by
              rw [hdeg4', Polynomial.reflect_mul _ _ (le_trans (Polynomial.natDegree_C_mul_le _ _) (hpow_deg _ 2 _ dA)) (hpow_deg _ 2 _ dB'),
                Polynomial.reflect_C_mul, href_pow 2 dA, href_pow 2 dB', rA, rB]
              simp only [mul_pow, hCs2, one_mul]; ring
            rw [hR1, hR2]
            simp only [mul_pow, hCs4, one_mul]; ring
        · have hme : m % 2 = 0 := by omega
          simp only [show m % 2 ≠ 1 by omega, ↓reduceIte] at ihm hdm
          rcases ihm with ⟨rA, rB, rC⟩
          rcases hdm with ⟨dA, dB, dC⟩
          have hm2 : 4 ≤ m ^ 2 := by
            have : 2 ≤ m := by omega
            nlinarith
          rcases jacobiTriple_even_of_even hm1 hme with ⟨eA, eB, eC⟩
          have ht2m : (-1 : ZOmega ℤ) ^ m = 1 := Even.neg_one_pow (Nat.even_iff.mpr hme)
          set tm : ZOmega ℤ := (-1 : ZOmega ℤ) ^ (m / 2)
          have htm2 : tm ^ 2 = 1 := by dsimp only [tm]; rw [← pow_mul, mul_comm, pow_mul]; simp
          have hCtm2 : C tm ^ 2 = 1 := by rw [← map_pow, htm2, map_one]
          have hCtm4 : C tm ^ 4 = 1 := by
            rw [← map_pow, show tm ^ 4 = (tm ^ 2) ^ 2 by ring, htm2, one_pow, map_one]
          rw [hn_eq, ht2m, eA, eB, eC]
          refine ⟨?_, ?_, ?_⟩
          · have hdeg_eq : (2 * m) ^ 2 - 2 = ((m ^ 2 - 2) + m ^ 2) + 2 * m ^ 2 := by
              have : (2 * m) ^ 2 = 4 * m ^ 2 := by ring
              omega
            rw [hdeg_eq, Polynomial.reflect_mul _ _ (hmul_deg _ _ _ _ (hdeg_2mul _ _ dA) dB) dC,
              Polynomial.reflect_mul _ _ (hdeg_2mul _ _ dA) dB,
              href_2mul, rA, rB, rC]
            simp only [map_neg, map_one]
            linear_combination -2 * jA m * jB m * jC m * hCtm2
          · have hdeg4 : (2 * m) ^ 2 = 4 * m ^ 2 := by ring
            have hdeg4' : 4 * m ^ 2 = 2 * 4 + 4 * (m ^ 2 - 2) := by omega
            rw [href_sub, hdeg4, href_pow 4 dB, hdeg4',
              Polynomial.reflect_mul _ _ (hpow_deg _ 2 _ hQdeg) (hpow_deg _ 4 _ dA),
              href_pow 2 hQdeg, href_pow 4 dA, hQref, rA, rB]
            simp only [mul_pow, map_neg, neg_pow, Even.neg_one_pow (by decide : Even 4),
              hCtm4, one_mul, map_one]
          · have hdeg8 : 2 * (2 * m) ^ 2 = 4 * m ^ 2 + 4 * m ^ 2 := by ring
            have hdeg4' : 4 * m ^ 2 = 2 * 4 + 4 * (m ^ 2 - 2) := by omega
            have hdeg4'' : 4 * m ^ 2 = (4 + 2 * (m ^ 2 - 2)) + 2 * m ^ 2 := by omega
            have hdegL : (jB m ^ 4 + Qpoly z0 ^ 2 * jA m ^ 4).natDegree ≤ 4 * m ^ 2 := by
              refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (hpow_deg _ 4 _ dB) ?_)
              have := hmul_deg _ _ _ _ (hpow_deg _ 2 _ hQdeg) (hpow_deg _ 4 _ dA); omega
            have hdegR : (jC m ^ 2 - C (2 * z0) * Qpoly z0 * jA m ^ 2 * jB m ^ 2).natDegree ≤ 4 * m ^ 2 := by
              refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le (by have := hpow_deg _ 2 _ dC; omega) ?_)
              have := hmul_deg _ _ _ _ (hmul_deg _ _ _ _ (le_trans (Polynomial.natDegree_C_mul_le (2 * z0) _) hQdeg) (hpow_deg _ 2 _ dA))
                (hpow_deg _ 2 _ dB); omega
            have hdegQA4 : (4 * Qpoly z0 ^ 2 * jA m ^ 4).natDegree ≤ 4 * m ^ 2 := by
              have := hmul_deg _ _ _ _ (hdeg_4mul _ _ (hpow_deg _ 2 _ hQdeg)) (hpow_deg _ 4 _ dA)
              omega
            rw [Polynomial.reflect_add, hdeg8,
              Polynomial.reflect_mul _ _ hdegL hdegR,
              Polynomial.reflect_mul _ _ hdegQA4 (hpow_deg _ 4 _ dB),
              Polynomial.reflect_add, href_sub]
            have hQA4 : (Qpoly z0 ^ 2 * jA m ^ 4).reflect (4 * m ^ 2) = Qpoly z0 ^ 2 * jA m ^ 4 := by
              rw [hdeg4', Polynomial.reflect_mul _ _ (hpow_deg _ 2 _ hQdeg) (hpow_deg _ 4 _ dA),
                href_pow 2 hQdeg, href_pow 4 dA, hQref, rA]
              simp only [mul_pow, map_neg, neg_pow, Even.neg_one_pow (by decide : Even 4),
                hCtm4, one_mul]
            have h4QA4 : (4 * Qpoly z0 ^ 2 * jA m ^ 4).reflect (4 * m ^ 2) = 4 * Qpoly z0 ^ 2 * jA m ^ 4 := by
              rw [mul_assoc, href_4mul, hQA4, ← mul_assoc]
            have hB4 : (jB m ^ 4).reflect (4 * m ^ 2) = jB m ^ 4 := by
              rw [href_pow 4 dB, rB]; simp only [mul_pow, hCtm4, one_mul]
            have hC2 : (jC m ^ 2).reflect (4 * m ^ 2) = jC m ^ 2 := by
              rw [show 4 * m ^ 2 = 2 * (2 * m ^ 2) by ring, href_pow 2 dC, rC]
            have hQAB : (C (2 * z0) * Qpoly z0 * jA m ^ 2 * jB m ^ 2).reflect (4 * m ^ 2) =
                C (2 * z0) * Qpoly z0 * jA m ^ 2 * jB m ^ 2 := by
              rw [hdeg4'', Polynomial.reflect_mul _ _
                  (hmul_deg _ _ _ _ (le_trans (Polynomial.natDegree_C_mul_le _ _) hQdeg) (hpow_deg _ 2 _ dA))
                  (hpow_deg _ 2 _ dB),
                Polynomial.reflect_mul _ _ (le_trans (Polynomial.natDegree_C_mul_le _ _) hQdeg) (hpow_deg _ 2 _ dA),
                Polynomial.reflect_C_mul, hQref, href_pow 2 dA, href_pow 2 dB, rA, rB]
              simp only [mul_pow, map_neg, neg_sq, hCtm2, one_mul]
            rw [hB4, hQA4, h4QA4, hC2, hQAB]
      · -- n = 2 * m + 1 odd!
        have hno : n % 2 = 1 := by omega
        simp only [hno, ↓reduceIte]
        set m := n / 2
        have hm1 : 1 ≤ m := by omega
        have hn_eq : n = 2 * m + 1 := by omega
        set o := if m % 2 = 1 then m else m + 1
        set e := if m % 2 = 1 then m + 1 else m
        have ho_odd : o % 2 = 1 := by dsimp only [o]; split_ifs <;> omega
        have he_ev : e % 2 = 0 := by dsimp only [e]; split_ifs <;> omega
        have ho_lt : o < n := by dsimp only [o]; split_ifs <;> omega
        have he_lt : e < n := by dsimp only [e]; split_ifs <;> omega
        have ho1 : 1 ≤ o := by dsimp only [o]; split_ifs <;> omega
        have he1 : 1 ≤ e := by dsimp only [e]; split_ifs <;> omega
        have hsum_sq : 2 * (o ^ 2 + e ^ 2) = n ^ 2 + 1 := by
          rw [hn_eq]; dsimp only [o, e]; split_ifs <;> ring
        have he2 : 4 ≤ e ^ 2 := by
          have : 2 ≤ e := by omega
          nlinarith
        have ho2 : 1 ≤ o ^ 2 := by nlinarith
        have iho := ih o ho_lt ho1; simp only [ho_odd, ↓reduceIte] at iho
        have ihe := ih e he_lt he1; simp only [show e % 2 ≠ 1 by omega, ↓reduceIte] at ihe
        have hdo := jacobiTriple_natDegree_le o ho1; simp only [ho_odd, ↓reduceIte] at hdo
        have hde := jacobiTriple_natDegree_le e he1; simp only [show e % 2 ≠ 1 by omega, ↓reduceIte] at hde
        have hdn := jacobiTriple_natDegree_le n hn; simp only [hno, ↓reduceIte] at hdn
        rcases iho with ⟨rAo, rBo, rCo⟩
        rcases ihe with ⟨rAe, rBe, rCe⟩
        rcases hdo with ⟨dAo, dBo, dCo⟩
        rcases hde with ⟨dAe, dBe, dCe⟩
        rcases hdn with ⟨dAn, dBn, dCn⟩
        have dBo' : (jB o).natDegree ≤ o ^ 2 := by omega
        have dBn' : (jB n).natDegree ≤ n ^ 2 := by omega
        have hstep := jacobiTriple_odd_step hm1
        dsimp only at hstep
        have hconsec := jacobi_consec_diff m hm1
        dsimp only at hconsec
        set so : ZOmega ℤ := (-1 : ZOmega ℤ) ^ ((o - 1) / 2)
        set te : ZOmega ℤ := (-1 : ZOmega ℤ) ^ (e / 2)
        set sn : ZOmega ℤ := (-1 : ZOmega ℤ) ^ ((n - 1) / 2)
        have hso2 : so ^ 2 = 1 := by dsimp only [so]; rw [← pow_mul, mul_comm, pow_mul]; simp
        have hte2 : te ^ 2 = 1 := by dsimp only [te]; rw [← pow_mul, mul_comm, pow_mul]; simp
        have hsn_eq : sn = if m % 2 = 1 then -1 else 1 := by
          dsimp only [sn]
          rw [show (n - 1) / 2 = m by omega]
          split_ifs with hmo
          · exact Odd.neg_one_pow (Nat.odd_iff.mpr hmo)
          · exact Even.neg_one_pow (Nat.even_iff.mpr (by omega))
        have hCso2 : C so ^ 2 = 1 := by rw [← map_pow, hso2, map_one]
        have hCte2 : C te ^ 2 = 1 := by rw [← map_pow, hte2, map_one]
        -- 1. Prove (jA n).reflect (n^2) = C sn * jB n via X * rev(n^2) A_n = rev(n^2 + 1) A_n = C sn * X * B_n!
        have hrAn : (jA n).reflect (n ^ 2) = C sn * jB n := by
          have hXmul : X * (jA n).reflect (n ^ 2) = X * (C sn * jB n) := by
            rw [← reflect_succ_eq_X_mul (n ^ 2) (jA n) dAn]
            rw [hn_eq, hstep.1, Polynomial.reflect_add]
            have hdeg1 : (2 * m + 1) ^ 2 + 1 = (o ^ 2 + o ^ 2) + 2 * e ^ 2 := by
              rw [← hn_eq]; omega
            have hdeg2 : (2 * m + 1) ^ 2 + 1 = ((4 + (e ^ 2 - 2)) + e ^ 2) + (2 * o ^ 2 - 2) := by
              rw [← hn_eq]; omega
            have ht1 : (jA o * jB o * jC e).reflect ((2 * m + 1) ^ 2 + 1) = jA o * jB o * jC e := by
              rw [hdeg1, Polynomial.reflect_mul _ _ (hmul_deg _ _ _ _ dAo dBo') dCe,
                Polynomial.reflect_mul _ _ dAo dBo', rAo, rBo, rCe]
              linear_combination jA o * jB o * jC e * hCso2
            have ht2 : (Qpoly z0 * jA e * jB e * jC o).reflect ((2 * m + 1) ^ 2 + 1) =
                -(Qpoly z0 * jA e * jB e * jC o) := by
              rw [hdeg2, Polynomial.reflect_mul _ _ (hmul_deg _ _ _ _ (hmul_deg _ _ _ _ hQdeg dAe) dBe) dCo,
                Polynomial.reflect_mul _ _ (hmul_deg _ _ _ _ hQdeg dAe) dBe,
                Polynomial.reflect_mul _ _ hQdeg dAe, hQref, rAe, rBe, rCo]
              simp only [map_neg]
              linear_combination -(Qpoly z0 * jA e * jB e * jC o) * hCte2
            change (jA o * jB o * jC e).reflect ((2 * m + 1) ^ 2 + 1) +
                (Qpoly z0 * jA e * jB e * jC o).reflect ((2 * m + 1) ^ 2 + 1) =
                X * (C sn * jB (2 * m + 1))
            rw [ht1, ht2, ← sub_eq_add_neg, hconsec, ← hsn_eq]; ring
          exact X_mul_cancel_poly hXmul
        -- 2. Prove (jB n).reflect (n^2) = C sn * jA n via curve equations + hconsec!
        have hrBn : (jB n).reflect (n ^ 2) = C sn * jA n := by
          have hBrev1 : X * (jB n).reflect (n ^ 2) =
              jA o ^ 2 * jB e ^ 2 - Qpoly z0 * jA e ^ 2 * jB o ^ 2 := by
            rw [← reflect_succ_eq_X_mul (n ^ 2) (jB n) dBn']
            rw [hn_eq, hstep.2.1, href_sub]
            change (jB o ^ 2 * jB e ^ 2).reflect ((2 * m + 1) ^ 2 + 1) -
                (Qpoly z0 * jA o ^ 2 * jA e ^ 2).reflect ((2 * m + 1) ^ 2 + 1) = _
            have hdeg1 : (2 * m + 1) ^ 2 + 1 = o ^ 2 * 2 + e ^ 2 * 2 := by
              rw [← hn_eq]; omega
            have hdeg2 : (2 * m + 1) ^ 2 + 1 = (4 + o ^ 2 * 2) + (e ^ 2 - 2) * 2 := by
              rw [← hn_eq]; omega
            have h1 : (jB o ^ 2 * jB e ^ 2).reflect ((2 * m + 1) ^ 2 + 1) = jA o ^ 2 * jB e ^ 2 := by
              rw [hdeg1, Polynomial.reflect_mul _ _
                  (by have := hpow_deg _ 2 _ dBo'; omega)
                  (by have := hpow_deg _ 2 _ dBe; omega),
                reflect_pow_eq _ _ dBo', reflect_pow_eq _ _ dBe, rBo, rBe]
              simp only [mul_pow, hCso2, hCte2, one_mul]
            have h2 : (Qpoly z0 * jA o ^ 2 * jA e ^ 2).reflect ((2 * m + 1) ^ 2 + 1) =
                Qpoly z0 * jA e ^ 2 * jB o ^ 2 := by
              rw [hdeg2, Polynomial.reflect_mul _ _
                  (by have := hmul_deg _ _ _ _ hQdeg (hpow_deg _ 2 _ dAo); omega)
                  (by have := hpow_deg _ 2 _ dAe; omega),
                Polynomial.reflect_mul _ _ hQdeg (by have := hpow_deg _ 2 _ dAo; omega),
                hQref, reflect_pow_eq _ _ dAo, reflect_pow_eq _ _ dAe, rAo, rAe]
              simp only [mul_pow, map_neg, neg_sq, hCso2, hCte2, one_mul]; ring
            rw [h1, h2]
          have hcur_o : Qpoly z0 * jC o ^ 2 =
              jB o ^ 4 - C (2 * z0) * jA o ^ 2 * jB o ^ 2 + jA o ^ 4 := by
            have h := (jU_jY_props o ho1).2.2.1
            set Bo : PowerSeries (ZOmega ℤ) := ((jB o : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
            set Ao : PowerSeries (ZOmega ℤ) := ((jA o : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
            set Co : PowerSeries (ZOmega ℤ) := ((jC o : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
            set Boinv : PowerSeries (ZOmega ℤ) := psInv (jB_isUnit_ps o ho1)
            have hBm : Bo * Boinv = 1 := psInv_mul (jB_isUnit_ps o ho1)
            simp only [jU, jY, ho_odd, ↓reduceIte] at h
            have hmul4 := congr_arg (· * Bo ^ 4) h
            have hps : (((Qpoly z0 * jC o ^ 2 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))) =
                ((jB o ^ 4 - C (2 * z0) * jA o ^ 2 * jB o ^ 2 + jA o ^ 4 : (ZOmega ℤ)[X]) :
                  PowerSeries (ZOmega ℤ)) := by
              simp only [Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul,
                Polynomial.coe_pow, Polynomial.coe_C]
              change ((Qpoly z0 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) * Co ^ 2 =
                Bo ^ 4 - PowerSeries.C (2 * z0) * Ao ^ 2 * Bo ^ 2 + Ao ^ 4
              rw [← legSeriesY_sq]
              calc legSeriesY ^ 2 * Co ^ 2
                  = (legSeriesY * Co * Boinv ^ 2) ^ 2 * Bo ^ 4 := by
                    have : (Boinv * Bo) ^ 4 = 1 := by rw [mul_comm, hBm, one_pow]
                    linear_combination -legSeriesY ^ 2 * Co ^ 2 * this
                _ = (1 - PowerSeries.C (2 * z0) * (Ao * Boinv) ^ 2 + (Ao * Boinv) ^ 4) * Bo ^ 4 := hmul4
                _ = Bo ^ 4 - PowerSeries.C (2 * z0) * Ao ^ 2 * Bo ^ 2 * (Bo * Boinv) ^ 2 +
                      Ao ^ 4 * (Bo * Boinv) ^ 4 := by ring
                _ = Bo ^ 4 - PowerSeries.C (2 * z0) * Ao ^ 2 * Bo ^ 2 + Ao ^ 4 := by rw [hBm]; ring
            exact Polynomial.coe_injective (ZOmega ℤ) hps
          have hcur_e : jC e ^ 2 =
              jB e ^ 4 - C (2 * z0) * Qpoly z0 * jA e ^ 2 * jB e ^ 2 + Qpoly z0 ^ 2 * jA e ^ 4 := by
            have h := (jU_jY_props e he1).2.2.1
            set Be : PowerSeries (ZOmega ℤ) := ((jB e : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
            set Ae : PowerSeries (ZOmega ℤ) := ((jA e : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
            set Ce : PowerSeries (ZOmega ℤ) := ((jC e : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
            set Beinv : PowerSeries (ZOmega ℤ) := psInv (jB_isUnit_ps e he1)
            have hBm : Be * Beinv = 1 := psInv_mul (jB_isUnit_ps e he1)
            simp only [jU, jY, show e % 2 ≠ 1 by omega, ↓reduceIte] at h
            have hmul4 := congr_arg (· * Be ^ 4) h
            have hY4 : legSeriesY ^ 4 = ((Qpoly z0 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) ^ 2 := by
              rw [show legSeriesY ^ 4 = (legSeriesY ^ 2) ^ 2 by ring, legSeriesY_sq]
            have hps : ((jC e ^ 2 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) =
                ((jB e ^ 4 - C (2 * z0) * Qpoly z0 * jA e ^ 2 * jB e ^ 2 +
                  Qpoly z0 ^ 2 * jA e ^ 4 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) := by
              simp only [Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul,
                Polynomial.coe_pow, Polynomial.coe_C]
              change Ce ^ 2 = Be ^ 4 - PowerSeries.C (2 * z0) *
                ((Qpoly z0 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) * Ae ^ 2 * Be ^ 2 +
                ((Qpoly z0 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) ^ 2 * Ae ^ 4
              calc Ce ^ 2
                  = (Ce * Beinv ^ 2) ^ 2 * Be ^ 4 := by
                    have : (Beinv * Be) ^ 4 = 1 := by rw [mul_comm, hBm, one_pow]
                    linear_combination -Ce ^ 2 * this
                _ = (1 - PowerSeries.C (2 * z0) * (legSeriesY * Ae * Beinv) ^ 2 +
                      (legSeriesY * Ae * Beinv) ^ 4) * Be ^ 4 := hmul4
                _ = Be ^ 4 - PowerSeries.C (2 * z0) * legSeriesY ^ 2 * Ae ^ 2 * Be ^ 2 * (Be * Beinv) ^ 2 +
                      legSeriesY ^ 4 * Ae ^ 4 * (Be * Beinv) ^ 4 := by ring
                _ = Be ^ 4 - PowerSeries.C (2 * z0) *
                      ((Qpoly z0 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) * Ae ^ 2 * Be ^ 2 +
                    ((Qpoly z0 : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) ^ 2 * Ae ^ 4 := by
                  rw [hBm, legSeriesY_sq, hY4]; ring
            exact Polynomial.coe_injective (ZOmega ℤ) hps
          have hprod_id : jB n * (X * (jB n).reflect (n ^ 2)) = jB n * (X * (C sn * jA n)) := by
            rw [hBrev1, hn_eq]
            have h1 : jA (2 * m + 1) * (C sn * X * jB (2 * m + 1)) =
                (jA o * jB o * jC e) ^ 2 - (Qpoly z0 * jA e * jB e * jC o) ^ 2 := by
              rw [hstep.1, hsn_eq]
              change (jA o * jB o * jC e + Qpoly z0 * jA e * jB e * jC o) *
                  (C (if m % 2 = 1 then -1 else 1) * X * jB (2 * m + 1)) = _
              rw [← hconsec]; ring
            have h2 : (jA o * jB o * jC e) ^ 2 - (Qpoly z0 * jA e * jB e * jC o) ^ 2 =
                jB (2 * m + 1) * (jA o ^ 2 * jB e ^ 2 - Qpoly z0 * jA e ^ 2 * jB o ^ 2) := by
              rw [hstep.2.1]
              change (jA o * jB o * jC e) ^ 2 - (Qpoly z0 * jA e * jB e * jC o) ^ 2 =
                (jB o ^ 2 * jB e ^ 2 - Qpoly z0 * jA o ^ 2 * jA e ^ 2) *
                  (jA o ^ 2 * jB e ^ 2 - Qpoly z0 * jA e ^ 2 * jB o ^ 2)
              linear_combination jA o ^ 2 * jB o ^ 2 * hcur_e - Qpoly z0 * jA e ^ 2 * jB e ^ 2 * hcur_o
            linear_combination -h2 - h1
          have hcancelB : X * (jB n).reflect (n ^ 2) = X * (C sn * jA n) := by
            apply Polynomial.coe_injective (ZOmega ℤ)
            have hps := congr_arg ((↑) : (ZOmega ℤ)[X] → PowerSeries (ZOmega ℤ)) hprod_id
            rw [Polynomial.coe_mul (jB n), Polynomial.coe_mul (jB n)] at hps
            exact (jB_isUnit_ps n hn).mul_left_cancel hps
          exact X_mul_cancel_poly hcancelB
        -- 3. Prove (jC n).reflect (2 * n^2 - 2) = jC n via the 5-line derivative-reflection trick!
        have hrCn : (jC n).reflect (2 * n ^ 2 - 2) = jC n := by
          have hwr := jA_jB_wronskian_odd n hn hno
          have hsn2 : sn ^ 2 = 1 := by
            rw [hsn_eq]; split_ifs <;> ring
          have hCsn2 : C sn ^ 2 = 1 := by rw [← map_pow, hsn2, map_one]
          have hn2_1 : 1 ≤ n ^ 2 := by nlinarith
          have h2n2_1 : 2 * n ^ 2 - 2 + 1 = 2 * n ^ 2 - 1 := by omega
          have hdeg_wr : (C (n : ZOmega ℤ) * jC n).natDegree ≤ 2 * n ^ 2 - 2 :=
            le_trans (Polynomial.natDegree_C_mul_le _ _) dCn
          have hX_lhs : (C (n : ZOmega ℤ) * jC n).reflect (2 * n ^ 2 - 1) =
              X * (C (n : ZOmega ℤ) * (jC n).reflect (2 * n ^ 2 - 2)) := by
            rw [← h2n2_1, reflect_succ_eq_X_mul _ _ hdeg_wr, Polynomial.reflect_C_mul]
          have hX_rhs : ((jA n).derivative * jB n - jA n * (jB n).derivative).reflect (2 * n ^ 2 - 1) =
              X * (C (n : ZOmega ℤ) * jC n) := by
            rw [href_sub]
            have hsum_d : 2 * n ^ 2 - 1 = (n ^ 2 - 1) + n ^ 2 := by omega
            have hsum_d' : 2 * n ^ 2 - 1 = n ^ 2 + (n ^ 2 - 1) := by omega
            have hdAp : (jA n).derivative.natDegree ≤ n ^ 2 - 1 :=
              le_trans (Polynomial.natDegree_derivative_le _) (Nat.sub_le_sub_right dAn 1)
            have hdBp : (jB n).derivative.natDegree ≤ n ^ 2 - 1 :=
              le_trans (Polynomial.natDegree_derivative_le _) (Nat.sub_le_sub_right dBn' 1)
            rw [hsum_d, Polynomial.reflect_mul _ _ hdAp dBn',
              ← hsum_d, hsum_d', Polynomial.reflect_mul _ _ dAn hdBp,
              reflect_derivative (n ^ 2) hn2_1 (jA n) dAn,
              reflect_derivative (n ^ 2) hn2_1 (jB n) dBn',
              hrAn, hrBn]
            simp only [Polynomial.derivative_C_mul]
            rw [← hwr]
            linear_combination X * ((jA n).derivative * jB n - jA n * (jB n).derivative) * hCsn2
          have hEq : X * (C (n : ZOmega ℤ) * (jC n).reflect (2 * n ^ 2 - 2)) =
              X * (C (n : ZOmega ℤ) * jC n) := by
            rw [← hX_lhs, ← hX_rhs, hwr]
          have hCeq := X_mul_cancel_poly hEq
          ext k
          have hk := congr_arg (fun P => P.coeff k) hCeq
          simp only [Polynomial.coeff_C_mul] at hk
          have hnsm : n • ((jC n).reflect (2 * n ^ 2 - 2)).coeff k = n • (jC n).coeff k := by
            simpa [nsmul_eq_mul] using hk
          exact nsmul_right_injective (by omega : n ≠ 0) hnsm
        exact ⟨hrAn, hrBn, hrCn⟩

private lemma dvd_pow_coeff_of_dvd_lt {p : ℕ} (h : PowerSeries (ZOmega ℤ)) (N : ℕ)
    (h0 : PowerSeries.constantCoeff h = 0)
    (hlt : ∀ j < N, (p : ZOmega ℤ) ∣ PowerSeries.coeff j h) :
    (∀ d ≥ 1, ∀ k < N, (p : ZOmega ℤ) ^ d ∣ PowerSeries.coeff k (h ^ d)) ∧
    (∀ d ≥ 2, (p : ZOmega ℤ) ^ d ∣ PowerSeries.coeff N (h ^ d)) := by
  have hpart1 : ∀ d ≥ 1, ∀ k < N, (p : ZOmega ℤ) ^ d ∣ PowerSeries.coeff k (h ^ d) := by
    intro d hd
    induction d with
    | zero => omega
    | succ d ih =>
      intro k hk
      cases d with
      | zero => simpa using hlt k hk
      | succ d =>
        rw [pow_succ (p : ZOmega ℤ) (d + 1), pow_succ h (d + 1), PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        apply Finset.dvd_sum
        intro x hx
        rw [Finset.mem_range] at hx
        exact mul_dvd_mul (ih (by omega) x (by omega)) (hlt (k - x) (by omega))
  refine ⟨hpart1, ?_⟩
  intro d hd
  rcases d with _ | _ | d
  · omega
  · omega
  · rw [pow_succ (p : ZOmega ℤ) (d + 1), pow_succ h (d + 1), PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.dvd_sum
    intro x hx
    rw [Finset.mem_range] at hx
    by_cases hx2 : N - x = 0
    · rw [hx2, PowerSeries.coeff_zero_eq_constantCoeff, h0, mul_zero]; exact dvd_zero _
    · by_cases hx1 : x = 0
      · rw [hx1, coeff_pow_eq_zero_of_lt h h0 (d + 1) 0 (by omega), zero_mul]; exact dvd_zero _
      · exact mul_dvd_mul (hpart1 (d + 1) (by omega) x (by omega)) (hlt (N - x) (by omega))

private lemma zomega_dvd_of_mul_coprime {p u : ℕ} (hcop : Nat.Coprime u p) (a : ZOmega ℤ)
    (hd : (p : ZOmega ℤ) ∣ (u : ZOmega ℤ) * a) :
    (p : ZOmega ℤ) ∣ a := by
  rcases hd with ⟨w, hw⟩
  have hre : (p : ℤ) ∣ (u : ℤ) * a.re := ⟨w.re, by simpa using congr_arg ZOmega.re hw⟩
  have him : (p : ℤ) ∣ (u : ℤ) * a.im := ⟨w.im, by simpa using congr_arg ZOmega.im hw⟩
  have hcopZ : IsCoprime (p : ℤ) (u : ℤ) := (Nat.isCoprime_iff_coprime.mpr hcop.symm)
  rcases hcopZ.dvd_of_dvd_mul_left hre with ⟨r, hr⟩
  rcases hcopZ.dvd_of_dvd_mul_left him with ⟨i, hi⟩
  refine ⟨⟨r, i⟩, ?_⟩
  apply ZOmega.ext <;> simp [hr, hi]

private lemma shiftedLegendre_m2_eval_x0_mod_p3 {p : ℕ} [Fact p.Prime]
    (hp : OeisA3625.A p) (hp5 : 5 ≤ p) :
    ((p : ZOmega ℤ) ^ 3) ∣
      (legVal ((p ^ 2 - 1) / 2) - (-1 : ZOmega ℤ) ^ ((p - 1) / 2) * (p : ZOmega ℤ)) := by
  set m := (p - 1) / 2
  set m2 := (p ^ 2 - 1) / 2
  have hp_pr : p.Prime := Fact.out
  have hp_pos : 0 < p := hp_pr.pos
  have hp1 : 1 ≤ p := by omega
  have hp2 : p ≠ 2 := A3625_ne_two hp
  have hp_odd : Odd p := A3625_odd hp
  have hp_mod2 : p % 2 = 1 := Nat.odd_iff.mp hp_odd
  have h2m1 : 2 * m + 1 = p := by omega
  have h2m2 : 2 * m2 + 1 = p ^ 2 := by
    have : 2 * (p * m + m) + 1 = p ^ 2 := by nlinarith
    have h1 : 1 ≤ p ^ 2 := by nlinarith
    omega
  set h : PowerSeries (ZOmega ℤ) := jU p hp1
  set Bp : PowerSeries (ZOmega ℤ) := ((jB p : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
  set Ap : PowerSeries (ZOmega ℤ) := ((jA p : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
  set Cp : PowerSeries (ZOmega ℤ) := ((jC p : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ))
  set Bpinv : PowerSeries (ZOmega ℤ) := psInv (jB_isUnit_ps p hp1)
  have hBmul : Bp * Bpinv = 1 := psInv_mul (jB_isUnit_ps p hp1)
  have hA_eq : Ap = Bp * h := by
    simp only [h, jU, hp_mod2, ↓reduceIte, Ap]
    change Ap = Bp * (Ap * Bpinv)
    calc Ap = Ap * (Bp * Bpinv) := by rw [hBmul, mul_one]
      _ = Bp * (Ap * Bpinv) := by ring
  have hprops := jU_jY_props p hp1
  have hh0 : PowerSeries.constantCoeff h = 0 := hprops.1
  -- Parity: h is odd, so all even coefficients vanish!
  have hh_even_zero : ∀ k : ℕ, PowerSeries.coeff (2 * k) h = 0 := by
    have hpar := jacobiTriple_parity p hp1
    have hres_coe : ∀ (P : (ZOmega ℤ)[X]),
        PowerSeries.rescale (-1 : ZOmega ℤ) (P : PowerSeries (ZOmega ℤ)) =
          ((P.comp (-X) : (ZOmega ℤ)[X]) : PowerSeries (ZOmega ℤ)) := by
      intro P
      ext j
      rw [PowerSeries.coeff_rescale, Polynomial.coeff_coe, Polynomial.coeff_coe]
      rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def, Polynomial.finsetSum_coeff]
      have ht : ∀ i ∈ P.support,
          (C (P.coeff i) * (-X : (ZOmega ℤ)[X]) ^ i).coeff j =
            if i = j then (-1 : ZOmega ℤ) ^ j * P.coeff j else 0 := by
        intro i _
        rw [show (-X : (ZOmega ℤ)[X]) = C (-1) * X by simp, mul_pow,
          ← mul_assoc, ← map_pow, ← map_mul, Polynomial.coeff_C_mul_X_pow]
        by_cases hij : i = j
        · subst hij; simp [mul_comm]
        · have hji : j ≠ i := fun h => hij h.symm
          simp [hij, hji]
      rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq']
      split_ifs with hj
      · rfl
      · rw [Polynomial.notMem_support_iff.mp hj, mul_zero]
    have hresA : PowerSeries.rescale (-1 : ZOmega ℤ) Ap = -Ap := by
      dsimp only [Ap]; rw [hres_coe, hpar.1, Polynomial.coe_neg]
    have hresB : PowerSeries.rescale (-1 : ZOmega ℤ) Bp = Bp := by
      dsimp only [Bp]; rw [hres_coe, hpar.2.1]
    have hres_eq : Bp * PowerSeries.rescale (-1 : ZOmega ℤ) h = Bp * (-h) := by
      calc Bp * PowerSeries.rescale (-1 : ZOmega ℤ) h
          = PowerSeries.rescale (-1 : ZOmega ℤ) Bp * PowerSeries.rescale (-1 : ZOmega ℤ) h := by
            rw [hresB]
        _ = PowerSeries.rescale (-1 : ZOmega ℤ) (Bp * h) := (map_mul _ _ _).symm
        _ = PowerSeries.rescale (-1 : ZOmega ℤ) Ap := by rw [← hA_eq]
        _ = -Ap := hresA
        _ = Bp * (-h) := by rw [hA_eq, mul_neg]
    have hres_h : PowerSeries.rescale (-1 : ZOmega ℤ) h = -h :=
      (jB_isUnit_ps p hp1).mul_left_cancel hres_eq
    intro k
    have hk := congr_arg (PowerSeries.coeff (2 * k)) hres_h
    rw [PowerSeries.coeff_rescale, map_neg, Even.neg_one_pow (even_two_mul k), one_mul] at hk
    have h2 : (2 : ℕ) • PowerSeries.coeff (2 * k) h = 0 := by
      rw [two_nsmul]; exact eq_neg_iff_add_eq_zero.mp hk
    exact nsmul_right_injective (by decide : 2 ≠ 0) (by simpa using h2)
  -- Step 1: h' = p * (Cp * Bpinv^2), so p ∣ h.coeff j for all j with p ∤ j!
  have hh_deriv : PowerSeries.derivative (ZOmega ℤ) h = (p : PowerSeries (ZOmega ℤ)) * (Cp * Bpinv ^ 2) := by
    have hwr := jA_jB_wronskian_odd p hp1 hp_mod2
    have hdA := congr_arg (PowerSeries.derivative (ZOmega ℤ)) hA_eq
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hdA
    have hwr_ps := congr_arg ((↑) : (ZOmega ℤ)[X] → PowerSeries (ZOmega ℤ)) hwr
    simp only [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_C,
      ← PowerSeries.derivative_coe] at hwr_ps
    have hB2 : Bp ^ 2 * PowerSeries.derivative (ZOmega ℤ) h = (p : PowerSeries (ZOmega ℤ)) * Cp := by
      have h1 : Bp ^ 2 * PowerSeries.derivative (ZOmega ℤ) h =
          PowerSeries.derivative (ZOmega ℤ) Ap * Bp - Ap * PowerSeries.derivative (ZOmega ℤ) Bp := by
        linear_combination Bp * (-hdA) + PowerSeries.derivative (ZOmega ℤ) Bp * hA_eq
      rw [h1]
      simpa [Ap, Bp, Cp] using hwr_ps
    calc PowerSeries.derivative (ZOmega ℤ) h
        = (Bp * Bpinv) ^ 2 * PowerSeries.derivative (ZOmega ℤ) h := by rw [hBmul, one_pow, one_mul]
      _ = (Bp ^ 2 * PowerSeries.derivative (ZOmega ℤ) h) * Bpinv ^ 2 := by ring
      _ = (p : PowerSeries (ZOmega ℤ)) * (Cp * Bpinv ^ 2) := by rw [hB2]; ring
  have hh_dvd_not_dvd : ∀ j : ℕ, ¬ (p ∣ j) → (p : ZOmega ℤ) ∣ PowerSeries.coeff j h := by
    intro j hj
    cases j with
    | zero => exact absurd (dvd_zero p) hj
    | succ j =>
      have hk := congr_arg (PowerSeries.coeff j) hh_deriv
      rw [PowerSeries.coeff_derivative,
        show (p : PowerSeries (ZOmega ℤ)) = PowerSeries.C (p : ZOmega ℤ) by simp,
        PowerSeries.coeff_C_mul] at hk
      have hmul_dvd : (p : ZOmega ℤ) ∣ ((j + 1 : ℕ) : ZOmega ℤ) * PowerSeries.coeff (j + 1) h := by
        refine ⟨PowerSeries.coeff j (Cp * Bpinv ^ 2), ?_⟩
        rw [mul_comm, ← hk]; push_cast; ring
      exact zomega_dvd_of_mul_coprime (hp_pr.coprime_iff_not_dvd.mpr hj).symm _ hmul_dvd
  -- Formal log equation: legLogF(h_Q) = p * legLogF!
  have hlog := legLogF_subst_eq h (jY p hp1) p hh0 hprops.2.1 hprops.2.2.1 hprops.2.2.2
  -- Define coprime multiplier U = ∏_{n ∈ range (m2 + 1)} u_part(2*n + 1), coprime to p!
  let uPart : ℕ → ℕ := fun d =>
    if p ^ 2 ∣ d then d / p ^ 2 else if p ∣ d then d / p else d
  let ePart : ℕ → ℕ := fun d =>
    if p ^ 2 ∣ d then 2 else if p ∣ d then 1 else 0
  have hd_eq : ∀ d : ℕ, d = p ^ (ePart d) * uPart d := by
    intro d
    dsimp only [uPart, ePart]
    split_ifs with h2 h1
    · exact (Nat.mul_div_cancel' h2).symm
    · rw [pow_one]; exact (Nat.mul_div_cancel' h1).symm
    · simp
  have hu_cop : ∀ d : ℕ, 1 ≤ d → d ≤ p ^ 2 → Nat.Coprime (uPart d) p := by
    intro d hd1 hd2
    rw [Nat.coprime_comm, hp_pr.coprime_iff_not_dvd]
    intro hdv
    dsimp only [uPart] at hdv
    split_ifs at hdv with h2 h1
    · have hq : d / p ^ 2 = 1 := by
        have hle : 1 ≤ d / p ^ 2 := Nat.div_pos (Nat.le_of_dvd (by omega) h2) (by positivity)
        have hge : d / p ^ 2 ≤ 1 := (Nat.div_le_iff_le_mul_add_pred (by positivity)).mpr (by omega)
        omega
      rw [hq] at hdv
      exact hp_pr.not_dvd_one hdv
    · apply h2
      rcases h1 with ⟨t, rfl⟩
      rw [Nat.mul_div_cancel_left t hp_pos] at hdv
      rcases hdv with ⟨s, rfl⟩
      exact ⟨s, by ring⟩
    · exact h1 hdv
  set U : ℕ := ∏ n ∈ range (m2 + 1), uPart (2 * n + 1)
  have hU_cop : Nat.Coprime U p := by
    apply Nat.Coprime.prod_left
    intro n hn
    rw [Finset.mem_range] at hn
    exact hu_cop (2 * n + 1) (by omega) (by omega)
  have hu_dvd_U : ∀ n ≤ m2, uPart (2 * n + 1) ∣ U := fun n hn =>
    Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega))
  -- Key coefficient extraction from legLogF(h_Q) = p * legLogF at ANY odd N ≤ p^2!
  have hcoeff_log : ∀ N : ℕ, N % 2 = 1 → N ≤ p ^ 2 →
      (∀ j < N, (p : ZOmega ℤ) ∣ PowerSeries.coeff j h) →
      ((p : ZOmega ℤ) ^ 5) ∣
        ((p : ZOmega ℤ) ^ 2 * (U : ZOmega ℤ) * PowerSeries.coeff N h -
          (p : ZOmega ℤ) ^ (3 - ePart N) * ((U / uPart N : ℕ) : ZOmega ℤ) * legVal (N / 2)) := by
    intro N hN_odd hN_le hlt
    have hN_eq := hd_eq N
    have hN_half : N / 2 ≤ m2 := by omega
    have huN_dvd : uPart N ∣ U := by
      have : 2 * (N / 2) + 1 = N := by omega
      rw [← this]; exact hu_dvd_U (N / 2) hN_half
    have hpow_dvd := dvd_pow_coeff_of_dvd_lt h N hh0 hlt
    have hQ0 : PowerSeries.constantCoeff (PowerSeries.map ιQ h) = 0 := by
      rw [ps_constantCoeff_map, hh0, map_zero]
    have hN := congr_arg (PowerSeries.coeff N) hlog
    rw [Int.cast_natCast, coeff_subst_eq_sum _ _ hQ0] at hN
    -- Multiply hN by ιQ (p^2 * U) in ZOmega ℚ!
    have hN_scaled := congr_arg (fun x => ιQ ((p : ZOmega ℤ) ^ 2 * (U : ZOmega ℤ)) * x) hN
    rw [Finset.mul_sum] at hN_scaled
    -- Compute RHS of hN_scaled
    have hrhs_Q : ιQ ((p : ZOmega ℤ) ^ 2 * (U : ZOmega ℤ)) *
        PowerSeries.coeff N ((p : PowerSeries (ZOmega ℚ)) * legLogF) =
        ιQ ((p : ZOmega ℤ) ^ (3 - ePart N) * ((U / uPart N : ℕ) : ZOmega ℤ) * legVal (N / 2)) := by
      rw [show (p : PowerSeries (ZOmega ℚ)) = PowerSeries.C (p : ZOmega ℚ) by simp,
        PowerSeries.coeff_C_mul]
      simp only [legLogF, PowerSeries.coeff_mk, hN_odd, ↓reduceIte]
      have hN_ne : (N : ℚ) ≠ 0 := by
        have : 1 ≤ N := by omega
        positivity
      have hN_cast : (N : ℚ) = (p : ℚ) ^ (ePart N) * (uPart N : ℚ) := by
        exact_mod_cast hN_eq
      have hU_cast : (U : ℚ) = (uPart N : ℚ) * ((U / uPart N : ℕ) : ℚ) := by
        exact_mod_cast (Nat.mul_div_cancel' huN_dvd).symm
      have he_le : ePart N ≤ 2 := by dsimp only [ePart]; split_ifs <;> omega
      have hp3_cast : (p : ℚ) ^ 3 = (p : ℚ) ^ (ePart N) * (p : ℚ) ^ (3 - ePart N) := by
        rw [← pow_add, Nat.add_sub_of_le (by omega)]
      have hfrac : (p : ℚ) ^ 2 * (U : ℚ) * (p : ℚ) * (N : ℚ)⁻¹ =
          (p : ℚ) ^ (3 - ePart N) * ((U / uPart N : ℕ) : ℚ) := by
        have hup_ne : (uPart N : ℚ) ≠ 0 := by
          intro h0; rw [h0, mul_zero] at hN_cast; exact hN_ne hN_cast
        have hpe_ne : (p : ℚ) ^ (ePart N) ≠ 0 := by positivity
        rw [hN_cast, hU_cast]
        field_simp
        rw [hp3_cast]; ring
      have hof_nat : ∀ a : ℕ, ιQ (a : ZOmega ℤ) = ZOmega.of (a : ℚ) := fun a => by
        apply ZOmega.ext <;> simp [ιQ, ZOmega.mapRingHom]
      have hp_of : (p : ZOmega ℚ) = ZOmega.of (p : ℚ) := by apply ZOmega.ext <;> simp
      simp only [map_mul, map_pow, hof_nat, hp_of]
      calc ZOmega.of (p : ℚ) ^ 2 * ZOmega.of (U : ℚ) *
            (ZOmega.of (p : ℚ) * (ZOmega.of (N : ℚ)⁻¹ * ιQ (legVal (N / 2))))
          = ZOmega.of ((p : ℚ) ^ 2 * (U : ℚ) * (p : ℚ) * (N : ℚ)⁻¹) * ιQ (legVal (N / 2)) := by
            simp only [map_mul, map_pow]; ring
        _ = ZOmega.of ((p : ℚ) ^ (3 - ePart N) * ((U / uPart N : ℕ) : ℚ)) * ιQ (legVal (N / 2)) := by
            rw [hfrac]
        _ = ZOmega.of (p : ℚ) ^ (3 - ePart N) * ZOmega.of ((U / uPart N : ℕ) : ℚ) * ιQ (legVal (N / 2)) := by
            simp only [map_mul, map_pow]
    -- Compute each term of LHS of hN_scaled as ιQ of an explicit ZOmega ℤ element!
    let termZ : ℕ → ZOmega ℤ := fun d =>
      if d % 2 = 1 then
        (p : ZOmega ℤ) ^ (2 - ePart d) * ((U / uPart d : ℕ) : ZOmega ℤ) *
          legVal (d / 2) * PowerSeries.coeff N (h ^ d)
      else 0
    have hlhs_Q : ∀ d ∈ range (N + 1),
        ιQ ((p : ZOmega ℤ) ^ 2 * (U : ZOmega ℤ)) *
          (PowerSeries.coeff d legLogF * PowerSeries.coeff N (PowerSeries.map ιQ h ^ d)) =
        ιQ (termZ d) := by
      intro d hd
      rw [Finset.mem_range] at hd
      dsimp only [termZ, legLogF]
      rw [PowerSeries.coeff_mk]
      split_ifs with hdo
      · have hd_le : d ≤ p ^ 2 := by omega
        have hd_half : d / 2 ≤ m2 := by omega
        have hud_dvd : uPart d ∣ U := by
          have : 2 * (d / 2) + 1 = d := by omega
          rw [← this]; exact hu_dvd_U (d / 2) hd_half
        have hd_ne : (d : ℚ) ≠ 0 := by
          have : 1 ≤ d := by omega
          positivity
        have hd_cast : (d : ℚ) = (p : ℚ) ^ (ePart d) * (uPart d : ℚ) := by
          exact_mod_cast hd_eq d
        have hU_cast : (U : ℚ) = (uPart d : ℚ) * ((U / uPart d : ℕ) : ℚ) := by
          exact_mod_cast (Nat.mul_div_cancel' hud_dvd).symm
        have he_le : ePart d ≤ 2 := by dsimp only [ePart]; split_ifs <;> omega
        have hp2_cast : (p : ℚ) ^ 2 = (p : ℚ) ^ (ePart d) * (p : ℚ) ^ (2 - ePart d) := by
          rw [← pow_add, Nat.add_sub_of_le he_le]
        have hfrac : (p : ℚ) ^ 2 * (U : ℚ) * (d : ℚ)⁻¹ =
            (p : ℚ) ^ (2 - ePart d) * ((U / uPart d : ℕ) : ℚ) := by
          have hup_ne : (uPart d : ℚ) ≠ 0 := by
            intro h0; rw [h0, mul_zero] at hd_cast; exact hd_ne hd_cast
          have hpe_ne : (p : ℚ) ^ (ePart d) ≠ 0 := by positivity
          rw [hd_cast, hU_cast]
          field_simp
          rw [hp2_cast]; ring
        have hof_nat : ∀ a : ℕ, ιQ (a : ZOmega ℤ) = ZOmega.of (a : ℚ) := fun a => by
          apply ZOmega.ext <;> simp [ιQ, ZOmega.mapRingHom]
        have hpow_map : PowerSeries.coeff N (PowerSeries.map ιQ h ^ d) =
            ιQ (PowerSeries.coeff N (h ^ d)) := by
          rw [← map_pow, PowerSeries.coeff_map]
        rw [hpow_map]
        simp only [map_mul, map_pow, hof_nat]
        calc ZOmega.of (p : ℚ) ^ 2 * ZOmega.of (U : ℚ) *
              (ZOmega.of (d : ℚ)⁻¹ * ιQ (legVal (d / 2)) * ιQ (PowerSeries.coeff N (h ^ d)))
            = ZOmega.of ((p : ℚ) ^ 2 * (U : ℚ) * (d : ℚ)⁻¹) *
                ιQ (legVal (d / 2)) * ιQ (PowerSeries.coeff N (h ^ d)) := by
              simp only [map_mul, map_pow]; ring
          _ = ZOmega.of ((p : ℚ) ^ (2 - ePart d) * ((U / uPart d : ℕ) : ℚ)) *
                ιQ (legVal (d / 2)) * ιQ (PowerSeries.coeff N (h ^ d)) := by rw [hfrac]
          _ = ZOmega.of (p : ℚ) ^ (2 - ePart d) * ZOmega.of ((U / uPart d : ℕ) : ℚ) *
                ιQ (legVal (d / 2)) * ιQ (PowerSeries.coeff N (h ^ d)) := by
              simp only [map_mul, map_pow]
      · simp
    rw [Finset.sum_congr rfl hlhs_Q, ← map_sum, hrhs_Q] at hN_scaled
    have hZ := ιQ_injective hN_scaled
    -- Split off d = 0 (0) and d = 1 (p^2 * U * h.coeff N)!
    have hN1 : 1 ≤ N := by omega
    have hsum_split : (∑ d ∈ range (N + 1), termZ d) =
        (p : ZOmega ℤ) ^ 2 * (U : ZOmega ℤ) * PowerSeries.coeff N h +
          ∑ d ∈ Finset.Ico 2 (N + 1), termZ d := by
      have h1 : range (N + 1) = range 2 ∪ Finset.Ico 2 (N + 1) := by
        ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
      have hd1 : Disjoint (range 2) (Finset.Ico 2 (N + 1)) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        rw [Finset.mem_range] at hx1; rw [Finset.mem_Ico] at hx2; omega
      rw [h1, Finset.sum_union hd1, Finset.sum_range_succ, Finset.sum_range_one]
      have ht0 : termZ 0 = 0 := by simp [termZ]
      have ht1 : termZ 1 = (p : ZOmega ℤ) ^ 2 * (U : ZOmega ℤ) * PowerSeries.coeff N h := by
        have hnp1 : ¬ (p ∣ 1) := hp_pr.not_dvd_one
        have hnp2 : ¬ (p ^ 2 ∣ 1) := fun h2 => hnp1 (dvd_trans (dvd_pow_self p (by decide : 2 ≠ 0)) h2)
        simp [termZ, ePart, uPart, hnp1, hnp2, legVal_zero]
      rw [ht0, ht1, zero_add]
    rw [hsum_split] at hZ
    have hdiff_eq : (p : ZOmega ℤ) ^ 2 * (U : ZOmega ℤ) * PowerSeries.coeff N h -
        (p : ZOmega ℤ) ^ (3 - ePart N) * ((U / uPart N : ℕ) : ZOmega ℤ) * legVal (N / 2) =
        -(∑ d ∈ Finset.Ico 2 (N + 1), termZ d) := by
      linear_combination hZ
    rw [hdiff_eq, dvd_neg]
    apply Finset.dvd_sum
    intro d hd
    rw [Finset.mem_Ico] at hd
    dsimp only [termZ]
    split_ifs with hdo
    · have hd3 : 3 ≤ d := by omega
      have hpd : (p : ZOmega ℤ) ^ d ∣ PowerSeries.coeff N (h ^ d) := hpow_dvd.2 d (by omega)
      have hexp : 5 ≤ (2 - ePart d) + d := by
        dsimp only [ePart]
        split_ifs with h2 h1
        · have : p ^ 2 ≤ d := Nat.le_of_dvd (by omega) h2
          nlinarith
        · have : p ≤ d := Nat.le_of_dvd (by omega) h1
          omega
        · omega
      have hdvd_tot : (p : ZOmega ℤ) ^ ((2 - ePart d) + d) ∣
          (p : ZOmega ℤ) ^ (2 - ePart d) * ((U / uPart d : ℕ) : ZOmega ℤ) *
            legVal (d / 2) * PowerSeries.coeff N (h ^ d) := by
        rw [pow_add]
        rcases hpd with ⟨w, hw⟩
        refine ⟨((U / uPart d : ℕ) : ZOmega ℤ) * legVal (d / 2) * w, ?_⟩
        rw [hw]; ring
      exact dvd_trans (pow_dvd_pow (p : ZOmega ℤ) hexp) hdvd_tot
    · exact dvd_zero _
  -- Step 2: By strong induction on N < p^2, prove p ∣ h.coeff N for ALL N < p^2!
  have hh_dvd_lt : ∀ N < p ^ 2, (p : ZOmega ℤ) ∣ PowerSeries.coeff N h := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro hN_lt
      by_cases hdiv : p ∣ N
      · by_cases hodd : N % 2 = 1
        · have hlogN := hcoeff_log N hodd (by omega) (fun j hj => ih j hj (by omega))
          have hnp2 : ¬ (p ^ 2 ∣ N) := by
            intro h2
            have : N = 0 ∨ p ^ 2 ≤ N := by
              by_cases h0 : N = 0
              · exact Or.inl h0
              · exact Or.inr (Nat.le_of_dvd (by omega) h2)
            omega
          have heN : ePart N = 1 := by simp [ePart, hnp2, hdiv]
          rw [heN] at hlogN
          -- Write N = p * (2*q + 1), so N / 2 = q * p + m with q < p!
          rcases hdiv with ⟨k, rfl⟩
          have hk_odd : k % 2 = 1 := by
            have : (p * k) % 2 = (p % 2 * (k % 2)) % 2 := Nat.mul_mod p k 2
            rw [hp_mod2, one_mul, Nat.mod_mod] at this
            omega
          set q := (k - 1) / 2
          have hk_eq : k = 2 * q + 1 := by omega
          have hq_lt : q < p := by nlinarith
          have hhalf_eq : (p * k) / 2 = q * p + m := by
            have : 2 * (q * p + m) + 1 = p * k := by rw [hk_eq]; nlinarith
            omega
          -- By Schur congruence (Section 6), p ∣ legVal (q * p + m)!
          have hschur : (p : ZOmega ℤ) ∣ legVal (q * p + m) := by
            have h0 := shiftedLegendre_block_eval_x0_eq_zero hp q hq_lt
            have hmap : ZOmega.mapRingHom (Int.castRingHom (ZMod p)) (legVal (q * p + m)) = 0 := by
              dsimp only [legVal]
              rw [aeval_def, Polynomial.hom_eval₂, ZOmega.mapRingHom_x0]
              convert h0 using 1
              rw [aeval_def]; congr 1; ext x; apply ZOmega.ext <;> simp [ZOmega.mapRingHom]
            have hre : (p : ℤ) ∣ (legVal (q * p + m)).re :=
              (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (congr_arg ZOmega.re hmap)
            have him : (p : ℤ) ∣ (legVal (q * p + m)).im :=
              (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (congr_arg ZOmega.im hmap)
            rcases hre with ⟨r, hr⟩; rcases him with ⟨i, hi⟩
            exact ⟨⟨r, i⟩, by apply ZOmega.ext <;> simp [hr, hi]⟩
          rw [hhalf_eq] at hlogN
          have hp3_dvd : (p : ZOmega ℤ) ^ 3 ∣ (p : ZOmega ℤ) ^ 2 * (U : ZOmega ℤ) * PowerSeries.coeff (p * k) h := by
            have hd1 : (p : ZOmega ℤ) ^ 3 ∣
                (p : ZOmega ℤ) ^ 2 * (U : ZOmega ℤ) * PowerSeries.coeff (p * k) h -
                  (p : ZOmega ℤ) ^ (3 - 1) * ((U / uPart (p * k) : ℕ) : ZOmega ℤ) * legVal (q * p + m) :=
              dvd_trans (pow_dvd_pow (p : ZOmega ℤ) (by decide : 3 ≤ 5)) hlogN
            have hd2 : (p : ZOmega ℤ) ^ 3 ∣
                (p : ZOmega ℤ) ^ (3 - 1) * ((U / uPart (p * k) : ℕ) : ZOmega ℤ) * legVal (q * p + m) := by
              rcases hschur with ⟨w, hw⟩
              refine ⟨((U / uPart (p * k) : ℕ) : ZOmega ℤ) * w, ?_⟩
              rw [hw]; ring
            simpa using dvd_add hd1 hd2
          -- Cancel p^2 using torsion-freeness of ZOmega ℤ!
          have hp_dvd_U : (p : ZOmega ℤ) ∣ (U : ZOmega ℤ) * PowerSeries.coeff (p * k) h := by
            rcases hp3_dvd with ⟨w, hw⟩
            refine ⟨w, ?_⟩
            have hns : (p ^ 2) • ((U : ZOmega ℤ) * PowerSeries.coeff (p * k) h) =
                (p ^ 2) • ((p : ZOmega ℤ) * w) := by
              simp only [nsmul_eq_mul, Nat.cast_pow]
              linear_combination hw
            exact nsmul_right_injective (by positivity : p ^ 2 ≠ 0) hns
          exact zomega_dvd_of_mul_coprime hU_cop _ hp_dvd_U
        · -- N is even, so h.coeff N = 0!
          have hN_ev : N = 2 * (N / 2) := by omega
          rw [hN_ev, hh_even_zero]
          exact dvd_zero _
      · exact hh_dvd_not_dvd N hdiv
  -- Step 3: Ap = Bp * h + reversal => p ∣ (jB p).coeff j for all j ≥ 1!
  have hBp_dvd_pos : ∀ j : ℕ, 1 ≤ j → (p : ZOmega ℤ) ∣ (jB p).coeff j := by
    have href := jacobiTriple_reflect p hp1
    simp only [hp_mod2, ↓reduceIte] at href
    have hAp_dvd_lt : ∀ k < p ^ 2, (p : ZOmega ℤ) ∣ (jA p).coeff k := by
      intro k hk
      have hk_eq := congr_arg (PowerSeries.coeff k) hA_eq
      rw [Polynomial.coeff_coe, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hk_eq
      rw [hk_eq]
      apply Finset.dvd_sum
      intro x hx
      rw [Finset.mem_range] at hx
      exact dvd_mul_of_dvd_right (hh_dvd_lt (k - x) (by omega)) _
    intro j hj
    by_cases hle : j ≤ p ^ 2
    · have hcoeff_ref := congr_arg (fun P => P.coeff j) href.1
      rw [Polynomial.coeff_reflect, Polynomial.revAt_le hle, Polynomial.coeff_C_mul] at hcoeff_ref
      have hdiv_A : (p : ZOmega ℤ) ∣ (jA p).coeff (p ^ 2 - j) := hAp_dvd_lt (p ^ 2 - j) (by omega)
      rw [hcoeff_ref] at hdiv_A
      set s : ZOmega ℤ := (-1 : ZOmega ℤ) ^ ((p - 1) / 2)
      have hs2 : s ^ 2 = 1 := by dsimp only [s]; rw [← pow_mul, mul_comm, pow_mul]; simp
      rcases hdiv_A with ⟨w, hw⟩
      refine ⟨s * w, ?_⟩
      calc (jB p).coeff j = s ^ 2 * (jB p).coeff j := by rw [hs2, one_mul]
        _ = s * (s * (jB p).coeff j) := by ring
        _ = s * ((p : ZOmega ℤ) * w) := by rw [hw]
        _ = (p : ZOmega ℤ) * (s * w) := by ring
    · have hdB := jacobiTriple_natDegree_le p hp1
      simp only [hp_mod2, ↓reduceIte] at hdB
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : (jB p).natDegree < j)]
      exact dvd_zero _
  -- Step 4: [X^{p^2}] (Ap = Bp * h) => p^2 ∣ (h.coeff (p^2) - (-1)^m)!
  have hh_p2_mod_p2 : ((p : ZOmega ℤ) ^ 2) ∣
      (PowerSeries.coeff (p ^ 2) h - (-1 : ZOmega ℤ) ^ m) := by
    have href := jacobiTriple_reflect p hp1
    simp only [hp_mod2, ↓reduceIte] at href
    have hAp_top : (jA p).coeff (p ^ 2) = (-1 : ZOmega ℤ) ^ m := by
      have h0 := congr_arg (fun P => P.coeff 0) href.1
      rw [Polynomial.coeff_reflect, Polynomial.revAt_zero, Polynomial.coeff_C_mul] at h0
      have hB0 : (jB p).coeff 0 = 1 := by
        rw [Polynomial.coeff_zero_eq_eval_zero]; exact (jacobiTriple_eval_zero p hp1).2.1
      rw [hB0, mul_one] at h0
      exact h0
    have hcoeff_p2 := congr_arg (PowerSeries.coeff (p ^ 2)) hA_eq
    rw [Polynomial.coeff_coe, hAp_top, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcoeff_p2
    rw [Finset.sum_range_succ'] at hcoeff_p2
    have hBp0 : PowerSeries.coeff 0 Bp = 1 := by
      rw [Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero]
      exact (jacobiTriple_eval_zero p hp1).2.1
    rw [Nat.sub_zero, hBp0, one_mul] at hcoeff_p2
    have hsub : PowerSeries.coeff (p ^ 2) h - (-1 : ZOmega ℤ) ^ m =
        -(∑ i ∈ range (p ^ 2),
          PowerSeries.coeff (i + 1) Bp * PowerSeries.coeff (p ^ 2 - (i + 1)) h) := by
      linear_combination -hcoeff_p2
    rw [hsub, dvd_neg]
    apply Finset.dvd_sum
    intro i hi
    rw [Finset.mem_range] at hi
    rw [pow_two]
    exact mul_dvd_mul (by rw [Polynomial.coeff_coe]; exact hBp_dvd_pos (i + 1) (by omega))
      (hh_dvd_lt (p ^ 2 - (i + 1)) (by omega))
  -- Step 5: Apply hcoeff_log at N = p^2 to get p^3 ∣ (legVal m2 - (-1)^m * p)!
  have hp2_odd : (p ^ 2) % 2 = 1 := by
    have : Odd (p ^ 2) := hp_odd.pow
    exact Nat.odd_iff.mp this
  have hlog_p2 := hcoeff_log (p ^ 2) hp2_odd le_rfl hh_dvd_lt
  have he_p2 : ePart (p ^ 2) = 2 := by simp [ePart]
  have hu_p2 : uPart (p ^ 2) = 1 := by simp [uPart, Nat.div_self (by positivity : 0 < p ^ 2)]
  have hhalf_p2 : p ^ 2 / 2 = m2 := by omega
  rw [he_p2, hu_p2, Nat.div_one, hhalf_p2] at hlog_p2
  -- p^5 ∣ (p^2 * U * h.coeff (p^2) - p * U * legVal m2) => p^4 ∣ (U * (p * h.coeff (p^2) - legVal m2))!
  have hp4_dvd : ((p : ZOmega ℤ) ^ 4) ∣
      (U : ZOmega ℤ) * ((p : ZOmega ℤ) * PowerSeries.coeff (p ^ 2) h - legVal m2) := by
    rcases hlog_p2 with ⟨w, hw⟩
    refine ⟨w, ?_⟩
    have hns : p • ((U : ZOmega ℤ) * ((p : ZOmega ℤ) * PowerSeries.coeff (p ^ 2) h - legVal m2)) =
        p • ((p : ZOmega ℤ) ^ 4 * w) := by
      simp only [nsmul_eq_mul]
      linear_combination hw
    exact nsmul_right_injective (by omega : p ≠ 0) hns
  -- Combine with hp2_mod_p2: p^3 ∣ U * (legVal m2 - (-1)^m * p)!
  have hp3_U : ((p : ZOmega ℤ) ^ 3) ∣
      (U : ZOmega ℤ) * (legVal m2 - (-1 : ZOmega ℤ) ^ m * (p : ZOmega ℤ)) := by
    have hd1 : ((p : ZOmega ℤ) ^ 3) ∣
        (U : ZOmega ℤ) * ((p : ZOmega ℤ) * PowerSeries.coeff (p ^ 2) h - legVal m2) :=
      dvd_trans (pow_dvd_pow (p : ZOmega ℤ) (by decide : 3 ≤ 4)) hp4_dvd
    have hd2 : ((p : ZOmega ℤ) ^ 3) ∣
        (U : ZOmega ℤ) * (p : ZOmega ℤ) * (PowerSeries.coeff (p ^ 2) h - (-1 : ZOmega ℤ) ^ m) := by
      rcases hh_p2_mod_p2 with ⟨w, hw⟩
      refine ⟨(U : ZOmega ℤ) * w, ?_⟩
      rw [hw]; ring
    have heq : (U : ZOmega ℤ) * (legVal m2 - (-1 : ZOmega ℤ) ^ m * (p : ZOmega ℤ)) =
        (U : ZOmega ℤ) * (p : ZOmega ℤ) * (PowerSeries.coeff (p ^ 2) h - (-1 : ZOmega ℤ) ^ m) -
          (U : ZOmega ℤ) * ((p : ZOmega ℤ) * PowerSeries.coeff (p ^ 2) h - legVal m2) := by ring
    rw [heq]
    exact dvd_sub hd2 hd1
  -- Cancel coprime U from p^3 ∣ U * x!
  rcases hp3_U with ⟨w, hw⟩
  have hp3_re : ((p : ZOmega ℤ) ^ 3).re = (p : ℤ) ^ 3 := by
    rw [← Nat.cast_pow, ZOmega.natCast_re, Nat.cast_pow]
  have hp3_im : ((p : ZOmega ℤ) ^ 3).im = 0 := by
    rw [← Nat.cast_pow, ZOmega.natCast_im]
  have hre : ((p ^ 3 : ℕ) : ℤ) ∣ (U : ℤ) * (legVal m2 - (-1 : ZOmega ℤ) ^ m * (p : ZOmega ℤ)).re :=
    ⟨w.re, by
      have := congr_arg ZOmega.re hw
      simpa [hp3_re, hp3_im, Nat.cast_pow] using this⟩
  have him : ((p ^ 3 : ℕ) : ℤ) ∣ (U : ℤ) * (legVal m2 - (-1 : ZOmega ℤ) ^ m * (p : ZOmega ℤ)).im :=
    ⟨w.im, by
      have := congr_arg ZOmega.im hw
      simpa [hp3_re, hp3_im, Nat.cast_pow] using this⟩
  have hcop3 : IsCoprime ((p ^ 3 : ℕ) : ℤ) (U : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (hU_cop.symm.pow_left 3)
  rcases hcop3.dvd_of_dvd_mul_left hre with ⟨r, hr⟩
  rcases hcop3.dvd_of_dvd_mul_left him with ⟨i, hi⟩
  refine ⟨⟨r, i⟩, ?_⟩
  apply ZOmega.ext
  · simpa [hp3_re, hp3_im, Nat.cast_pow] using hr
  · simpa [hp3_re, hp3_im, Nat.cast_pow] using hi

/- ### Section 9: Squaring lift, Clausen mod `p^4`, and proof of the main theorem -/

private lemma shiftedLegendre_m2_eval_x0_sq_mod_p4 {p : ℕ} [Fact p.Prime]
    (hp : OeisA3625.A p) (hp5 : 5 ≤ p) :
    aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 4))) ((shiftedLegendre ((p ^ 2 - 1) / 2)) ^ 2) =
      (p : ZOmega (ZMod (p ^ 4))) ^ 2 := by
  set m := (p - 1) / 2
  set m2 := (p ^ 2 - 1) / 2
  rcases shiftedLegendre_m2_eval_x0_mod_p3 hp hp5 with ⟨w, hw⟩
  have hval : legVal m2 = (-1 : ZOmega ℤ) ^ m * (p : ZOmega ℤ) + (p : ZOmega ℤ) ^ 3 * w := by
    linear_combination hw
  have hsq : (legVal m2) ^ 2 = (p : ZOmega ℤ) ^ 2 +
      (p : ZOmega ℤ) ^ 4 * (2 * (-1 : ZOmega ℤ) ^ m * w + (p : ZOmega ℤ) ^ 2 * w ^ 2) := by
    have hs2 : ((-1 : ZOmega ℤ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    rw [hval]
    linear_combination (p : ZOmega ℤ) ^ 2 * hs2
  have hmap_aeval : ZOmega.mapRingHom (Int.castRingHom (ZMod (p ^ 4))) ((legVal m2) ^ 2) =
      aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 4))) ((shiftedLegendre m2) ^ 2) := by
    rw [map_pow, map_pow]
    congr 1
    dsimp only [legVal]
    rw [aeval_def, aeval_def, Polynomial.hom_eval₂, ZOmega.mapRingHom_x0]
    congr 1
    ext x
    apply ZOmega.ext <;> simp [ZOmega.mapRingHom]
  rw [← hmap_aeval, hsq]
  simp only [map_add, map_mul, map_pow, map_natCast]
  have hp4_zero : (p : ZOmega (ZMod (p ^ 4))) ^ 4 = 0 := by
    apply ZOmega.ext
    · rw [← Nat.cast_pow, ZOmega.natCast_re, ZOmega.zero_re, ZMod.natCast_self]
    · rw [← Nat.cast_pow, ZOmega.natCast_im, ZOmega.zero_im]
  rw [hp4_zero, zero_mul, add_zero]

private lemma prod_sub_p2_mod_p4 {p : ℕ} (q : ℕ) (f : ℕ → ZMod (p ^ 4)) :
    ∃ c : ZMod (p ^ 4), (∏ i ∈ range q, (f i - (p : ZMod (p ^ 4)) ^ 2)) =
      (∏ i ∈ range q, f i) + (p : ZMod (p ^ 4)) ^ 2 * c := by
  induction q with
  | zero => exact ⟨0, by simp⟩
  | succ q ih =>
    rcases ih with ⟨c, hc⟩
    rw [Finset.prod_range_succ, hc, Finset.prod_range_succ]
    exact ⟨c * f q - (∏ i ∈ range q, f i) - (p : ZMod (p ^ 4)) ^ 2 * c, by ring⟩

private lemma block_cube_sum_dvd_p2 {p : ℕ} [Fact p.Prime]
    (hp : OeisA3625.A p) (hp5 : 5 ≤ p) (q : ℕ) :
    p ^ 2 ∣ ∑ r ∈ range ((p - 1) / 2 + 1), ((2 * (p * q + r)).choose (p * q + r)) ^ 3 := by
  set m := (p - 1) / 2
  have hp2 : p ≠ 2 := A3625_ne_two hp
  have h2m1 : 2 * m + 1 = p := by
    have := Nat.odd_iff.mp (A3625_odd hp)
    omega
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
  have hterm : ∀ r ∈ range (m + 1),
      ((((2 * (p * q + r)).choose (p * q + r)) ^ 3 : ℕ) : ZMod (p ^ 2)) =
      (((2 * q).choose q : ℕ) ^ 3 : ZMod (p ^ 2)) * (((2 * r).choose r : ℕ) ^ 3 : ZMod (p ^ 2)) +
      (6 * (q : ZMod (p ^ 2)) * (((2 * q).choose q : ℕ) ^ 3 : ZMod (p ^ 2))) *
        ((p : ZMod (p ^ 2)) * ((((2 * r).choose r : ℕ) ^ 3 : ZMod (p ^ 2)) *
          ((∑ j ∈ range (2 * r), ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹) -
           (∑ j ∈ range r, ((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹)))) := by
    intro r hr
    rw [Finset.mem_range] at hr
    have hblk := choose_two_mul_block_cube_mod_p2 p q r (by omega)
    rw [Nat.cast_pow, hblk]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have hS0 : (∑ r ∈ range (m + 1), (((2 * r).choose r : ℕ) ^ 3 : ZMod (p ^ 2))) = 0 := by
    simp_rw [← Nat.cast_pow]
    rw [← Nat.cast_sum]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_a_half hp)
  have hSh := sum_harmDiff_eq_zero_mod_p hp hp5
  rw [hS0, hSh, mul_zero, mul_zero, add_zero]

private lemma a_m2_mod_p4_ge5 {p : ℕ} [Fact p.Prime]
    (hp : OeisA3625.A p) (hp5 : 5 ≤ p) :
    OeisA79727.a ((p ^ 2 - 1) / 2) ≡ p ^ 2 [MOD p ^ 4] := by
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
  -- Step 1: Clausen at m2, x0 in ZOmega (ZMod (p^4))
  have hcl := shiftedLegendre_m2_eval_x0_sq_mod_p4 hp hp5
  rw [clausen_poly_identity m2, aeval_comp] at hcl
  have hz_val : aeval (ZOmega.x0 : ZOmega (ZMod (p ^ 4))) (X ^ 2 - X : ℤ[X]) =
      (-16 : ZOmega (ZMod (p ^ 4))) := by
    simp only [map_sub, map_pow, aeval_X, ZOmega.neg_x0_mul_one_sub]
  rw [hz_val, map_sum] at hcl
  have hsum_re : (∑ k ∈ range (m2 + 1),
      (((m2 + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k : ZMod (p ^ 4))) =
      (p : ZMod (p ^ 4)) ^ 2 := by
    have hre := congr_arg ZOmega.re hcl
    have hrhs : ((p : ZOmega (ZMod (p ^ 4))) ^ 2).re = (p : ZMod (p ^ 4)) ^ 2 := by
      simp [pow_two]
    rw [hrhs] at hre
    rw [← hre]
    have hre_sum : ∀ s : Finset ℕ, ∀ f : ℕ → ZOmega (ZMod (p ^ 4)),
        (∑ k ∈ s, f k).re = ∑ k ∈ s, (f k).re := by
      intro s f
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ZOmega.add_re, ih]
    rw [hre_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_mul, map_pow, aeval_C, aeval_X, eq_intCast]
    have hof : ((((m2 + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 : ℤ) : ZOmega (ZMod (p ^ 4))) *
          (-16 : ZOmega (ZMod (p ^ 4))) ^ k =
        ZOmega.of ((((m2 + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k : ZMod (p ^ 4))) := by
      simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_neg, Int.cast_ofNat,
        map_mul, map_pow, map_natCast, map_neg, map_ofNat]
    rw [hof, ZOmega.of_re]
  -- Helper: relate clausenTerm(k) to C(2k,k)^3 in ZMod (p^4) via clausen_term_prod_identity,
  -- cancelling the `cnt` factors j = i * p + m < k (cnt = q if r ≤ m, cnt = q + 1 if r > m)!
  have hterm_prod_rel : ∀ (k cnt : ℕ), k ≤ m2 →
      (∀ i, i < cnt ↔ i * p + m < k) →
      (∏ i ∈ range cnt, ((2 * (i : ZMod (p ^ 4)) + 1) ^ 2)) *
        (((m2 + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k : ZMod (p ^ 4)) =
      (∏ i ∈ range cnt, ((2 * (i : ZMod (p ^ 4)) + 1) ^ 2 - (p : ZMod (p ^ 4)) ^ 2)) *
        (((2 * k).choose k : ℕ) : ZMod (p ^ 4)) ^ 3 := by
    intro k cnt hk_le hcnt_iff
    have hprod := clausen_term_prod_identity m2 k hk_le
    set S : Finset ℕ := (range cnt).image (fun i => i * p + m)
    have hS_sub : S ⊆ range k := by
      intro j hj
      rw [Finset.mem_image] at hj
      rcases hj with ⟨i, hi, rfl⟩
      rw [Finset.mem_range] at hi ⊢
      exact (hcnt_iff i).mp hi
    have hS_inj : Set.InjOn (fun i => i * p + m) (range cnt : Set ℕ) := by
      intro a _ b _ hab
      dsimp only at hab
      exact Nat.eq_of_mul_eq_mul_right hp_pos (by omega)
    have hsplit_L : (∏ j ∈ range k, ((2 * (j : ℤ) + 1) ^ 2)) =
        (p : ℤ) ^ (2 * cnt) * (∏ i ∈ range cnt, ((2 * (i : ℤ) + 1) ^ 2)) *
        (∏ j ∈ range k \ S, ((2 * (j : ℤ) + 1) ^ 2)) := by
      rw [← Finset.prod_sdiff hS_sub, Finset.prod_image hS_inj]
      have hS_prod : (∏ i ∈ range cnt, ((2 * ((i * p + m : ℕ) : ℤ) + 1) ^ 2)) =
          (p : ℤ) ^ (2 * cnt) * (∏ i ∈ range cnt, ((2 * (i : ℤ) + 1) ^ 2)) := by
        have ht : ∀ i ∈ range cnt, ((2 * ((i * p + m : ℕ) : ℤ) + 1) ^ 2) =
            (p : ℤ) ^ 2 * ((2 * (i : ℤ) + 1) ^ 2) := by
          intro i _
          have hlin : (2 * ((i * p + m : ℕ) : ℤ) + 1) = (p : ℤ) * (2 * (i : ℤ) + 1) := by
            have : 2 * (i * p + m) + 1 = p * (2 * i + 1) := by nlinarith
            exact_mod_cast this
          rw [hlin, mul_pow]
        rw [Finset.prod_congr rfl ht, Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_range, ← pow_mul]
      rw [hS_prod]; ring
    have hsplit_R : (∏ j ∈ range k, ((2 * (j : ℤ) + 1) ^ 2 - (2 * (m2 : ℤ) + 1) ^ 2)) =
        (p : ℤ) ^ (2 * cnt) * (∏ i ∈ range cnt, ((2 * (i : ℤ) + 1) ^ 2 - (p : ℤ) ^ 2)) *
        (∏ j ∈ range k \ S, ((2 * (j : ℤ) + 1) ^ 2 - (p : ℤ) ^ 4)) := by
      rw [← Finset.prod_sdiff hS_sub, Finset.prod_image hS_inj]
      have h2m2z : (2 * (m2 : ℤ) + 1) = (p : ℤ) ^ 2 := by exact_mod_cast h2m2
      have hS_prod : (∏ i ∈ range cnt, ((2 * ((i * p + m : ℕ) : ℤ) + 1) ^ 2 - (2 * (m2 : ℤ) + 1) ^ 2)) =
          (p : ℤ) ^ (2 * cnt) * (∏ i ∈ range cnt, ((2 * (i : ℤ) + 1) ^ 2 - (p : ℤ) ^ 2)) := by
        have ht : ∀ i ∈ range cnt, ((2 * ((i * p + m : ℕ) : ℤ) + 1) ^ 2 - (2 * (m2 : ℤ) + 1) ^ 2) =
            (p : ℤ) ^ 2 * ((2 * (i : ℤ) + 1) ^ 2 - (p : ℤ) ^ 2) := by
          intro i _
          have hlin : (2 * ((i * p + m : ℕ) : ℤ) + 1) = (p : ℤ) * (2 * (i : ℤ) + 1) := by
            have : 2 * (i * p + m) + 1 = p * (2 * i + 1) := by nlinarith
            exact_mod_cast this
          rw [hlin, h2m2z]; ring
        rw [Finset.prod_congr rfl ht, Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_range, ← pow_mul]
      have hT_prod : (∏ j ∈ range k \ S, ((2 * (j : ℤ) + 1) ^ 2 - (2 * (m2 : ℤ) + 1) ^ 2)) =
          (∏ j ∈ range k \ S, ((2 * (j : ℤ) + 1) ^ 2 - (p : ℤ) ^ 4)) := by
        apply Finset.prod_congr rfl
        intro j _; rw [h2m2z]; ring
      rw [hS_prod, hT_prod]; ring
    rw [hsplit_L, hsplit_R] at hprod
    have hp2c_ne : ((p : ℤ) ^ (2 * cnt)) ≠ 0 := by positivity
    have hcancel_z : (∏ j ∈ range k \ S, ((2 * (j : ℤ) + 1) ^ 2)) *
          ((∏ i ∈ range cnt, ((2 * (i : ℤ) + 1) ^ 2)) *
            (((m2 + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k)) =
        (∏ j ∈ range k \ S, ((2 * (j : ℤ) + 1) ^ 2 - (p : ℤ) ^ 4)) *
          ((∏ i ∈ range cnt, ((2 * (i : ℤ) + 1) ^ 2 - (p : ℤ) ^ 2)) * ((2 * k).choose k : ℤ) ^ 3) := by
      apply mul_left_cancel₀ hp2c_ne
      linear_combination hprod
    have hcast := congr_arg (Int.castRingHom (ZMod (p ^ 4))) hcancel_z
    simp only [map_mul, map_prod, map_pow, map_sub, map_add, map_one, map_neg, map_ofNat,
      map_natCast] at hcast
    have hT_eq : (∏ j ∈ range k \ S, ((2 * (j : ZMod (p ^ 4)) + 1) ^ 2 - (p : ZMod (p ^ 4)) ^ 4)) =
        (∏ j ∈ range k \ S, ((2 * (j : ZMod (p ^ 4)) + 1) ^ 2)) := by
      apply Finset.prod_congr rfl
      intro j _
      have hp4z : (p : ZMod (p ^ 4)) ^ 4 = 0 := by
        rw [← Nat.cast_pow, ZMod.natCast_self]
      rw [hp4z, sub_zero]
    rw [hT_eq] at hcast
    have hT_unit : IsUnit (∏ j ∈ range k \ S, ((2 * (j : ZMod (p ^ 4)) + 1) ^ 2)) := by
      rw [IsUnit.prod_iff]
      intro j hj
      rw [Finset.mem_sdiff, Finset.mem_range] at hj
      refine (ZMod.isUnit_iff_coprime (2 * j + 1) (p ^ 4)).mpr ?_ |> fun h => by
        simpa [Nat.cast_add, Nat.cast_mul] using h.pow 2
      refine (hp_pr.coprime_iff_not_dvd.mpr (fun hd => ?_)).symm.pow_right 4
      rcases hd with ⟨t, ht⟩
      have ht_odd : Odd t := by
        by_contra hev
        rw [Nat.not_odd_iff_even] at hev
        rcases hev with ⟨s, hs⟩
        rw [hs] at ht
        have : 2 * j + 1 = 2 * (p * s) := by linarith
        omega
      rcases ht_odd with ⟨i, rfl⟩
      have hj_eq : j = i * p + m := by nlinarith
      have hi_lt : i < cnt := (hcnt_iff i).mpr (by omega)
      exact hj.2 (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi_lt, hj_eq.symm⟩)
    have hres := hT_unit.mul_left_cancel hcast
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_neg, Int.cast_ofNat] using hres
  have hM_unit : ∀ cnt : ℕ, cnt ≤ m →
      IsUnit (∏ i ∈ range cnt, ((2 * (i : ZMod (p ^ 4)) + 1) ^ 2)) := by
    intro cnt hcnt
    rw [IsUnit.prod_iff]
    intro i hi
    rw [Finset.mem_range] at hi
    refine (ZMod.isUnit_iff_coprime (2 * i + 1) (p ^ 4)).mpr ?_ |> fun h => by
      simpa [Nat.cast_add, Nat.cast_mul] using h.pow 2
    exact (hp_pr.coprime_iff_not_dvd.mpr (fun hd => by
      have := Nat.le_of_dvd (by omega) hd; omega)).symm.pow_right 4
  -- Step 2: For q < m and m < r < p, clausenTerm(p*q + r) = C(2(pq+r), pq+r)^3 INDIVIDUALLY in ZMod (p^4)!
  have hgt_eq : ∀ q r : ℕ, q < m → m < r → r < p →
      (((m2 + (p * q + r)).choose (2 * (p * q + r)) : ℤ) *
        ((2 * (p * q + r)).choose (p * q + r) : ℤ) ^ 2 * (-16 : ℤ) ^ (p * q + r) : ZMod (p ^ 4)) =
      (((2 * (p * q + r)).choose (p * q + r) : ℕ) : ZMod (p ^ 4)) ^ 3 := by
    intro q r hqm hrm hrp
    have hk_le : p * q + r ≤ m2 := by
      have : p * (q + 1) ≤ p * m := Nat.mul_le_mul_left p (by omega)
      nlinarith
    have hiff : ∀ i, i < q + 1 ↔ i * p + m < p * q + r := by
      intro i
      constructor
      · intro hi
        have : i * p ≤ q * p := Nat.mul_le_mul_right p (by omega)
        nlinarith
      · intro hi
        by_contra hge
        have : (q + 1) * p ≤ i * p := Nat.mul_le_mul_right p (by omega)
        nlinarith
    have hrel := hterm_prod_rel (p * q + r) (q + 1) hk_le hiff
    rcases prod_sub_p2_mod_p4 (p := p) (q + 1) (fun i => (2 * (i : ZMod (p ^ 4)) + 1) ^ 2) with ⟨c, hc⟩
    rw [hc, add_mul] at hrel
    have hd : p ∣ (2 * (p * q + r)).choose (p * q + r) :=
      choose_two_mul_dvd_p_of_gt_half p hp2 q r hrm hrp
    rcases hd with ⟨t, ht⟩
    have herr0 : (p : ZMod (p ^ 4)) ^ 2 * c *
        (((2 * (p * q + r)).choose (p * q + r) : ℕ) : ZMod (p ^ 4)) ^ 3 = 0 := by
      rw [ht, Nat.cast_mul, mul_pow]
      have : (p : ZMod (p ^ 4)) ^ 2 * c * ((p : ZMod (p ^ 4)) ^ 3 * (t : ZMod (p ^ 4)) ^ 3) =
          ((p ^ 4 : ℕ) : ZMod (p ^ 4)) * ((p : ZMod (p ^ 4)) * c * (t : ZMod (p ^ 4)) ^ 3) := by
        push_cast; ring
      rw [this, ZMod.natCast_self, zero_mul]
    rw [herr0, add_zero] at hrel
    exact (hM_unit (q + 1) (by omega)).mul_left_cancel hrel
  -- Step 3: For q ≤ m, summing over r ∈ range (m + 1) gives equality in ZMod (p^4)!
  have hle_eq : ∀ q : ℕ, q ≤ m →
      (∑ r ∈ range (m + 1),
        (((m2 + (p * q + r)).choose (2 * (p * q + r)) : ℤ) *
          ((2 * (p * q + r)).choose (p * q + r) : ℤ) ^ 2 * (-16 : ℤ) ^ (p * q + r) : ZMod (p ^ 4))) =
      (∑ r ∈ range (m + 1), (((2 * (p * q + r)).choose (p * q + r) : ℕ) : ZMod (p ^ 4)) ^ 3) := by
    intro q hqm
    have hsum_rel : (∏ i ∈ range q, ((2 * (i : ZMod (p ^ 4)) + 1) ^ 2)) *
          (∑ r ∈ range (m + 1),
            (((m2 + (p * q + r)).choose (2 * (p * q + r)) : ℤ) *
              ((2 * (p * q + r)).choose (p * q + r) : ℤ) ^ 2 * (-16 : ℤ) ^ (p * q + r) : ZMod (p ^ 4))) =
        (∏ i ∈ range q, ((2 * (i : ZMod (p ^ 4)) + 1) ^ 2 - (p : ZMod (p ^ 4)) ^ 2)) *
          (∑ r ∈ range (m + 1), (((2 * (p * q + r)).choose (p * q + r) : ℕ) : ZMod (p ^ 4)) ^ 3) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mem_range] at hr
      have hk_le : p * q + r ≤ m2 := by
        have : p * q ≤ p * m := Nat.mul_le_mul_left p hqm
        omega
      have hiff : ∀ i, i < q ↔ i * p + m < p * q + r := by
        intro i
        constructor
        · intro hi
          have : (i + 1) * p ≤ q * p := Nat.mul_le_mul_right p (by omega)
          nlinarith
        · intro hi
          by_contra hge
          have : q * p ≤ i * p := Nat.mul_le_mul_right p (by omega)
          nlinarith
      exact hterm_prod_rel (p * q + r) q hk_le hiff
    rcases prod_sub_p2_mod_p4 (p := p) q (fun i => (2 * (i : ZMod (p ^ 4)) + 1) ^ 2) with ⟨c, hc⟩
    rw [hc, add_mul] at hsum_rel
    rcases block_cube_sum_dvd_p2 hp hp5 q with ⟨s, hs⟩
    have hsum_p2 : (∑ r ∈ range (m + 1), (((2 * (p * q + r)).choose (p * q + r) : ℕ) : ZMod (p ^ 4)) ^ 3) =
        (p : ZMod (p ^ 4)) ^ 2 * (s : ZMod (p ^ 4)) := by
      have := congr_arg (Nat.cast (R := ZMod (p ^ 4))) hs
      simpa only [Nat.cast_sum, Nat.cast_pow, Nat.cast_mul] using this
    have herr0 : (p : ZMod (p ^ 4)) ^ 2 * c *
        (∑ r ∈ range (m + 1), (((2 * (p * q + r)).choose (p * q + r) : ℕ) : ZMod (p ^ 4)) ^ 3) = 0 := by
      rw [hsum_p2]
      have : (p : ZMod (p ^ 4)) ^ 2 * c * ((p : ZMod (p ^ 4)) ^ 2 * (s : ZMod (p ^ 4))) =
          ((p ^ 4 : ℕ) : ZMod (p ^ 4)) * (c * (s : ZMod (p ^ 4))) := by
        push_cast; ring
      rw [this, ZMod.natCast_self, zero_mul]
    rw [herr0, add_zero] at hsum_rel
    exact (hM_unit q hqm).mul_left_cancel hsum_rel
  -- Step 4: Split range (m2 + 1) = range (p * m) ∪ image (p * m + ·) (range (m + 1)) and compare!
  have hsplit_sum : ∀ F : ℕ → ZMod (p ^ 4),
      (∑ k ∈ range (m2 + 1), F k) =
        (∑ q ∈ range m, (∑ r ∈ range (m + 1), F (p * q + r))) +
        (∑ q ∈ range m, (∑ r ∈ Finset.Ico (m + 1) p, F (p * q + r))) +
        (∑ r ∈ range (m + 1), F (p * m + r)) := by
    intro F
    have h1 : m2 + 1 = p * m + (m + 1) := by omega
    rw [h1, Finset.sum_range_add]
    congr 1
    have hblocks : (∑ k ∈ range (p * m), F k) = ∑ q ∈ range m, ∑ r ∈ range p, F (p * q + r) := by
      induction m with
      | zero => simp
      | succ n ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    rw [hblocks, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    have hs : range p = range (m + 1) ∪ Finset.Ico (m + 1) p := by
      ext r; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hd : Disjoint (range (m + 1)) (Finset.Ico (m + 1) p) := by
      rw [Finset.disjoint_left]; intro r h1 h2
      rw [Finset.mem_range] at h1; rw [Finset.mem_Ico] at h2; omega
    rw [hs, Finset.sum_union hd]
  have ha_eq : ((OeisA79727.a m2 : ℕ) : ZMod (p ^ 4)) = ((p ^ 2 : ℕ) : ZMod (p ^ 4)) := by
    rw [OeisA79727.a, Nat.cast_sum, Nat.cast_pow]
    simp_rw [Nat.cast_pow]
    rw [← hsum_re, hsplit_sum, hsplit_sum]
    congr 1
    · congr 1
      · apply Finset.sum_congr rfl
        intro q hq
        exact (hle_eq q (by rw [Finset.mem_range] at hq; omega)).symm
      · apply Finset.sum_congr rfl
        intro q hq
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.mem_range] at hq
        rw [Finset.mem_Ico] at hr
        exact (hgt_eq q r hq (by omega) hr.2).symm
    · exact (hle_eq m le_rfl).symm
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp ha_eq

private lemma a_m2_mod_p4_three :
    OeisA79727.a ((3 ^ 2 - 1) / 2) ≡ 3 ^ 2 [MOD 3 ^ 4] := by
  decide +kernel

private lemma conjecture_main (p : ℕ) (hp : OeisA3625.A p) :
    OeisA79727.a ((p ^ 2 - 1) / 2) ≡ p ^ 2 [MOD p ^ 4] := by
  have : Fact p.Prime := ⟨hp.1⟩
  by_cases h3 : p = 3
  · subst h3; exact a_m2_mod_p4_three
  · have hp5 : 5 ≤ p := by
      have h3le := A3625_three_le hp
      have hne4 : p ≠ 4 := by intro h4; rw [h4] at hp; exact absurd hp.1 (by decide)
      omega
    exact a_m2_mod_p4_ge5 hp hp5

end OeisA79727Conjecture3

theorem OMA.solution : type_of% @OeisA79727.conjecture3 :=
  fun p hp => OeisA79727Conjecture3.conjecture_main p hp
