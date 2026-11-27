import FormalConjectures.Paper.ApproximatelyStableMatching
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Disproof of the Fanelli–Moscardelli stability threshold conjecture

We prove that for every `k ≥ 3`, every complete strict preference profile on `2 * k + 1`
agents admits a `k`-stable roommates matching, hence
`Roommates.stabilityThreshold (2 * k + 1) ≤ k < k + 1 = ((2 * k + 1) + 1) / 2`.
This refutes `FanelliMoscardelli.stability_threshold_tight`.
-/

open scoped BigOperators
open Roommates

namespace FMProof

section Helpers

variable {n : ℕ}

private def mkMatching (f : Fin n → Fin n) (hf : Function.Involutive f) : Matching (Fin n) :=
  ⟨hf.toPerm f, hf⟩

private lemma isAcceptable_top (μ : Matching (Fin n)) : IsAcceptable ⊤ μ := by
  intro i
  by_cases h : μ.val i = i
  · exact Or.inl h
  · exact Or.inr ((SimpleGraph.top_adj _ _).2 (Ne.symm h))

private lemma partnerRank_pos (p : CompleteProfile n) (i j : Fin n) : 1 ≤ p.partnerRank i j :=
  Nat.succ_le_succ (Nat.zero_le _)

private lemma partnerRank_inj (p : CompleteProfile n) (i : Fin n) {j₁ j₂ : Fin n}
    (h : p.partnerRank i j₁ = p.partnerRank i j₂) : j₁ = j₂ := by
  unfold CompleteProfile.partnerRank at h
  exact (p.rank i).injective (Fin.ext (Nat.succ.inj h))

private lemma partnerRank_lt_of_ne (p : CompleteProfile n) {i j : Fin n} (hij : j ≠ i) :
    p.partnerRank i j < n := by
  have hle := p.partnerRank_le i j
  have hne : p.partnerRank i j ≠ n := by
    intro heq
    exact hij (partnerRank_inj p i (heq.trans (p.partnerRank_self i).symm))
  omega

private lemma exists_unique_partnerRank (p : CompleteProfile n) (i : Fin n) (r : ℕ)
    (hr1 : 1 ≤ r) (hr2 : r ≤ n) : ∃! j : Fin n, p.partnerRank i j = r := by
  let r' : Fin n := ⟨r - 1, by omega⟩
  refine ⟨(p.rank i).symm r', ?_, ?_⟩
  · unfold CompleteProfile.partnerRank
    simp [r']
    omega
  · intro j hj
    exact partnerRank_inj p i (by
      unfold CompleteProfile.partnerRank at hj ⊢
      simp [r']
      omega)

private lemma card_partnerRank_le (p : CompleteProfile n) (i : Fin n) (r : ℕ) (hr : r ≤ n) :
    (Finset.univ.filter (fun j : Fin n => p.partnerRank i j ≤ r)).card = r := by
  have hbij : (Finset.univ.filter (fun j : Fin n => p.partnerRank i j ≤ r)).card =
      (Finset.univ.filter (fun x : Fin n => x.val < r)).card := by
    refine Finset.card_bij (fun j _ => p.rank i j) ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_filter] at hj ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have h1 : (p.rank i j).val + 1 ≤ r := hj.2
      omega
    · intro j₁ _ j₂ _ h
      exact (p.rank i).injective h
    · intro x hx
      rw [Finset.mem_filter] at hx
      refine ⟨(p.rank i).symm x, ?_, by simp⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      change ((p.rank i) ((p.rank i).symm x)).val + 1 ≤ r
      rw [Equiv.apply_symm_apply]
      omega
  rw [hbij]
  have hbij2 : (Finset.univ.filter (fun x : Fin n => x.val < r)).card = (Finset.range r).card := by
    refine Finset.card_bij (fun x _ => x.val) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx
      exact Finset.mem_range.2 hx.2
    · intro x₁ _ x₂ _ h
      exact Fin.ext h
    · intro m hm
      rw [Finset.mem_range] at hm
      exact ⟨⟨m, by omega⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hm⟩, rfl⟩
  rw [hbij2, Finset.card_range]

private lemma card_partnerRank_Ico (p : CompleteProfile n) (i : Fin n) (a b : ℕ)
    (ha1 : 1 ≤ a) (hab : a ≤ b) (hbn : b ≤ n + 1) :
    (Finset.univ.filter (fun j : Fin n => a ≤ p.partnerRank i j ∧ p.partnerRank i j < b)).card =
      b - a := by
  have h1 := card_partnerRank_le p i (b - 1) (by omega)
  have h2 := card_partnerRank_le p i (a - 1) (by omega)
  have hsplit : Finset.univ.filter (fun j : Fin n => p.partnerRank i j ≤ b - 1) =
      Finset.univ.filter (fun j : Fin n => p.partnerRank i j ≤ a - 1) ∪
      Finset.univ.filter (fun j : Fin n => a ≤ p.partnerRank i j ∧ p.partnerRank i j < b) := by
    ext j
    have hp := partnerRank_pos p i j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hdisj : Disjoint
      (Finset.univ.filter (fun j : Fin n => p.partnerRank i j ≤ a - 1))
      (Finset.univ.filter (fun j : Fin n => a ≤ p.partnerRank i j ∧ p.partnerRank i j < b)) := by
    rw [Finset.disjoint_filter]
    intro j _ hle hge
    omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj, h2] at h1
  omega

private lemma not_kBlocking_of_immune (p : CompleteProfile n) (k : ℕ) (μ : Matching (Fin n))
    {i j : Fin n} (hi : p.partnerRank i (μ.val i) ≤ k) :
    ¬ IsKBlockingPair ⊤ p.partnerRank k μ i j := by
  rintro ⟨_, _, h1, _⟩
  have := partnerRank_pos p i j
  omega

private lemma isKBlockingPair_symm (p : CompleteProfile n) (k : ℕ) (μ : Matching (Fin n)) {i j : Fin n}
    (h : IsKBlockingPair ⊤ p.partnerRank k μ i j) :
    IsKBlockingPair ⊤ p.partnerRank k μ j i := by
  rcases h with ⟨hadj, hne, h1, h2⟩
  refine ⟨hadj.symm, ?_, h2, h1⟩
  intro hji
  apply hne
  have := congrArg μ.val hji
  rw [μ.property] at this
  exact this.symm

end Helpers

section InvolutionHelpers

variable {α : Type*} [DecidableEq α]

private def swap2 (a b x : α) : α :=
  if x = a then b else if x = b then a else x

private lemma swap2_inv (a b : α) : Function.Involutive (swap2 a b) := by
  intro x; unfold swap2
  by_cases h1 : x = a
  · rw [h1, if_pos rfl]; by_cases h2 : b = a <;> simp [h2]
  · by_cases h2 : x = b
    · rw [h2]; have hba : b ≠ a := h2 ▸ h1; simp [hba]
    · simp [h1, h2]

private lemma swap2_left (a b : α) : swap2 a b a = b := by simp [swap2]

private lemma swap2_right (a b : α) : swap2 a b b = a := by
  unfold swap2; by_cases h : b = a <;> simp [h]

private lemma swap2_supp (a b : α) : ∀ x, x ∉ ({a, b} : Finset α) → swap2 a b x = x := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  simp [swap2, hx.1, hx.2]

private def glue (A : Finset α) (g₁ g₂ : α → α) (x : α) : α :=
  if x ∈ A then g₁ x else g₂ x

private lemma glue_involution {A B : Finset α} (hAB : Disjoint A B)
    {g₁ g₂ : α → α}
    (hg₁ : Function.Involutive g₁) (hsupp₁ : ∀ x, x ∉ A → g₁ x = x)
    (hg₂ : Function.Involutive g₂) (hsupp₂ : ∀ x, x ∉ B → g₂ x = x) :
    Function.Involutive (glue A g₁ g₂) ∧
    (∀ x ∈ A, glue A g₁ g₂ x = g₁ x) ∧
    (∀ x ∈ B, glue A g₁ g₂ x = g₂ x) ∧
    (∀ x, x ∉ A ∪ B → glue A g₁ g₂ x = x) := by
  have hmap₁ : ∀ x ∈ A, g₁ x ∈ A := by
    intro x hx; by_contra hnot
    have h1 := hsupp₁ (g₁ x) hnot; rw [hg₁ x] at h1; exact hnot (h1 ▸ hx)
  have hmap₂ : ∀ x ∈ B, g₂ x ∈ B := by
    intro x hx; by_contra hnot
    have h2 := hsupp₂ (g₂ x) hnot; rw [hg₂ x] at h2; exact hnot (h2 ▸ hx)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x; unfold glue
    by_cases hxA : x ∈ A
    · simp only [hxA, ite_true, hmap₁ x hxA, hg₁ x]
    · simp only [hxA, ite_false]
      by_cases hxB : x ∈ B
      · have hg2xB : g₂ x ∈ B := hmap₂ x hxB
        have hg2notA : g₂ x ∉ A := Finset.disjoint_right.1 hAB hg2xB
        simp only [hg2notA, ite_false, hg₂ x]
      · simp only [hsupp₂ x hxB, hxA, ite_false]
  · intro x hxA; simp [glue, hxA]
  · intro x hxB
    have hxnotA : x ∉ A := Finset.disjoint_right.1 hAB hxB
    simp [glue, hxnotA]
  · intro x hx
    rw [Finset.mem_union] at hx; push Not at hx
    simp [glue, hx.1, hsupp₂ x hx.2]

private def swap4 (a b c d : α) : α → α :=
  glue ({a, b} : Finset α) (swap2 a b) (swap2 c d)

private lemma swap4_spec {a b c d : α} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Function.Involutive (swap4 a b c d) ∧
    swap4 a b c d a = b ∧ swap4 a b c d b = a ∧
    swap4 a b c d c = d ∧ swap4 a b c d d = c ∧
    (∀ x, x ∉ ({a, b, c, d} : Finset α) → swap4 a b c d x = x) := by
  have hd : Disjoint ({a, b} : Finset α) ({c, d} : Finset α) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
    rcases hx1 with rfl | rfl <;> rcases hx2 with h | h
    · exact hac h
    · exact had h
    · exact hbc h
    · exact hbd h
  have hgl := glue_involution hd (swap2_inv a b) (swap2_supp a b) (swap2_inv c d) (swap2_supp c d)
  refine ⟨hgl.1, ?_, ?_, ?_, ?_, ?_⟩
  · unfold swap4; rw [hgl.2.1 a (by simp), swap2_left]
  · unfold swap4; rw [hgl.2.1 b (by simp), swap2_right]
  · unfold swap4; rw [hgl.2.2.1 c (by simp), swap2_left]
  · unfold swap4; rw [hgl.2.2.1 d (by simp), swap2_right]
  · intro x hx; unfold swap4; apply hgl.2.2.2
    intro h; apply hx
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with (rfl | rfl) | (rfl | rfl) <;> simp

private def restrictTo (S : Finset α) (M : α → α) (x : α) : α :=
  if x ∈ S then M x else x

private lemma restrict_inv {S : Finset α} {M : α → α} (hM : Function.Involutive M)
    (hS : ∀ x ∈ S, M x ∈ S) :
    Function.Involutive (restrictTo S M) ∧
    (∀ x ∈ S, restrictTo S M x = M x) ∧
    (∀ x, x ∉ S → restrictTo S M x = x) := by
  refine ⟨?_, fun x hx => by simp [restrictTo, hx], fun x hx => by simp [restrictTo, hx]⟩
  intro x; unfold restrictTo
  by_cases hx : x ∈ S
  · simp [hx, hS x hx, hM x]
  · simp [hx]

end InvolutionHelpers

section OrbitPairing

private lemma iter_succ {α : Type*} (f : α → α) (m : ℕ) (x : α) : f^[m + 1] x = f (f^[m] x) :=
  Function.iterate_succ_apply' f m x

variable {α : Type*} [DecidableEq α]

private lemma card_even_of_fpf_involutive {S : Finset α} {g : α → α}
    (hinv : Function.Involutive g) (hmem : ∀ x ∈ S, g x ∈ S ∧ g x ≠ x) : S.card % 2 = 0 := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ m ih =>
    by_cases hS : S = ∅
    · subst hS; rw [Finset.card_empty] at hn; omega
    · rcases Finset.nonempty_iff_ne_empty.2 hS with ⟨x, hx⟩
      let S' := (S.erase x).erase (g x)
      have hgx : g x ∈ S.erase x := Finset.mem_erase.2 ⟨(hmem x hx).2, (hmem x hx).1⟩
      have hcard : S'.card + 2 = S.card := by
        have h1 : (S.erase x).card + 1 = S.card := Finset.card_erase_add_one hx
        have h2 : S'.card + 1 = (S.erase x).card := Finset.card_erase_add_one hgx
        omega
      have hmem' : ∀ y ∈ S', g y ∈ S' ∧ g y ≠ y := by
        intro y hy
        have hy1 : y ≠ g x := (Finset.mem_erase.1 hy).1
        have hy2 : y ≠ x := (Finset.mem_erase.1 (Finset.mem_erase.1 hy).2).1
        have hyS : y ∈ S := (Finset.mem_erase.1 (Finset.mem_erase.1 hy).2).2
        refine ⟨Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨?_, (hmem y hyS).1⟩⟩, (hmem y hyS).2⟩
        · intro h; exact hy2 (hinv.injective h)
        · intro h; exact hy1 (by rw [← h, hinv y])
      have heven' := ih S'.card (by omega) hmem' rfl
      omega

private lemma exists_fpf_involutive_of_even {S : Finset α} (heven : S.card % 2 = 0) :
    ∃ g : α → α, Function.Involutive g ∧ (∀ x, x ∉ S → g x = x) ∧
      (∀ x ∈ S, g x ∈ S ∧ g x ≠ x) := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ m ih =>
    by_cases hS : S = ∅
    · subst hS; exact ⟨id, fun _ => rfl, fun _ _ => rfl, by simp⟩
    · rcases Finset.nonempty_iff_ne_empty.2 hS with ⟨x, hx⟩
      have hcard1 : (S.erase x).card + 1 = S.card := Finset.card_erase_add_one hx
      have hne1 : (S.erase x).Nonempty := Finset.card_pos.1 (by omega)
      rcases hne1 with ⟨y, hy⟩
      have hyx : y ≠ x := (Finset.mem_erase.1 hy).1
      have hyS : y ∈ S := (Finset.mem_erase.1 hy).2
      let S' := (S.erase x).erase y
      have hcard2 : S'.card + 2 = S.card := by
        have h2 : S'.card + 1 = (S.erase x).card := Finset.card_erase_add_one hy
        omega
      rcases ih S'.card (by omega) (by omega) rfl with ⟨g', hg'inv, hg'supp, hg'mem⟩
      have hd : Disjoint ({x, y} : Finset α) S' := by
        rw [Finset.disjoint_left]; intro z hz1 hz2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz1
        rcases hz1 with rfl | rfl
        · exact (Finset.mem_erase.1 (Finset.mem_erase.1 hz2).2).1 rfl
        · exact (Finset.mem_erase.1 hz2).1 rfl
      have hgl := glue_involution hd (swap2_inv x y) (swap2_supp x y) hg'inv hg'supp
      have hunion : ({x, y} : Finset α) ∪ S' = S := by
        ext z; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase, S']
        constructor
        · rintro ((rfl | rfl) | ⟨_, _, hzS⟩)
          · exact hx
          · exact hyS
          · exact hzS
        · intro hzS
          by_cases hzx : z = x; · exact Or.inl (Or.inl hzx)
          by_cases hzy : z = y; · exact Or.inl (Or.inr hzy)
          · exact Or.inr ⟨hzy, hzx, hzS⟩
      refine ⟨glue ({x, y} : Finset α) (swap2 x y) g', hgl.1,
        fun z hz => hgl.2.2.2 z (hunion.symm ▸ hz), ?_⟩
      intro z hzS
      by_cases hzx : z = x
      · rw [hzx, hgl.2.1 x (by simp), swap2_left]; exact ⟨hyS, hyx⟩
      by_cases hzy : z = y
      · rw [hzy, hgl.2.1 y (by simp), swap2_right]; exact ⟨hx, hyx.symm⟩
      · have hz' : z ∈ S' := Finset.mem_erase.2 ⟨hzy, Finset.mem_erase.2 ⟨hzx, hzS⟩⟩
        rw [hgl.2.2.1 z hz']
        exact ⟨(Finset.mem_erase.1 (Finset.mem_erase.1 (hg'mem z hz').1).2).2, (hg'mem z hz').2⟩

omit [DecidableEq α] in
private lemma exists_period {S : Finset α} {f : α → α} (hf : ∀ x ∈ S, f x ∈ S)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y) {x : α} (hx : x ∈ S) :
    ∃ m : ℕ, 0 < m ∧ f^[m] x = x := by
  have hiter : ∀ m : ℕ, f^[m] x ∈ S := by
    intro m; induction m with
    | zero => exact hx
    | succ m ih => rw [iter_succ]; exact hf _ ih
  have hnotinj : ¬ Function.Injective (fun m : Fin (S.card + 1) => (⟨f^[m.val] x, hiter m.val⟩ : S)) := by
    intro h; have hc := Fintype.card_le_of_injective _ h
    simp only [Fintype.card_fin, Fintype.card_coe] at hc; omega
  rw [Function.Injective] at hnotinj; push Not at hnotinj
  rcases hnotinj with ⟨a, b, hab, hne⟩
  have hval : f^[a.val] x = f^[b.val] x := congrArg Subtype.val hab
  have hne' : a.val ≠ b.val := fun h => hne (Fin.ext h)
  wlog hlt : a.val < b.val generalizing a b
  · exact this b a hab.symm hne.symm hval.symm hne'.symm (by omega)
  have hcancel : ∀ d a' : ℕ, f^[a' + d] x = f^[a'] x → f^[d] x = x := by
    intro d a'; induction a' with
    | zero => simp
    | succ a' ih =>
      intro heq; apply ih; apply hinj _ (hiter _) _ (hiter _)
      rw [← iter_succ f (a' + d) x, ← iter_succ f a' x]
      have h1 : a' + d + 1 = a' + 1 + d := by omega
      rw [h1]; exact heq
  refine ⟨b.val - a.val, by omega, hcancel (b.val - a.val) a.val ?_⟩
  have : a.val + (b.val - a.val) = b.val := by omega
  rw [this, hval.symm]

private lemma orbit_structure {S : Finset α} {f : α → α} (hf : ∀ x ∈ S, f x ∈ S)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y) {x : α} (hx : x ∈ S) :
    ∃ (L : ℕ) (C : Finset α),
      0 < L ∧ C ⊆ S ∧ C.card = L ∧
      (∀ i < L, f^[i] x ∈ C) ∧
      (∀ y ∈ C, ∃ i < L, f^[i] x = y) ∧
      (∀ i < L, ∀ j < L, f^[i] x = f^[j] x → i = j) ∧
      f^[L] x = x ∧
      (∀ y ∈ C, f y ∈ C) ∧
      (∀ y ∈ S \ C, f y ∈ S \ C) := by
  classical
  have hex := exists_period hf hinj hx
  let L := Nat.find hex
  have hL : 0 < L ∧ f^[L] x = x := Nat.find_spec hex
  have hmin : ∀ m < L, 0 < m → f^[m] x ≠ x := fun m hm hpos heq => Nat.find_min hex hm ⟨hpos, heq⟩
  have hiter : ∀ m : ℕ, f^[m] x ∈ S := by
    intro m; induction m with
    | zero => exact hx
    | succ m ih => rw [iter_succ]; exact hf _ ih
  have hdist : ∀ i < L, ∀ j < L, f^[i] x = f^[j] x → i = j := by
    intro i hi j hj heq; by_contra hne
    wlog hlt : i < j generalizing i j
    · exact this j hj i hi heq.symm (Ne.symm hne) (by omega)
    have hcancel : ∀ a d : ℕ, f^[a + d] x = f^[a] x → f^[d] x = x := by
      intro a d; induction a with
      | zero => simp
      | succ a ih =>
        intro h; apply ih; apply hinj _ (hiter _) _ (hiter _)
        rw [← iter_succ f (a + d) x, ← iter_succ f a x]
        have h1 : a + d + 1 = a + 1 + d := by omega
        rw [h1]; exact h
    have hd : f^[j - i] x = x := by
      apply hcancel i (j - i)
      have hji : i + (j - i) = j := by omega
      rw [hji]
      exact heq.symm
    exact hmin (j - i) (by omega) (by omega) hd
  let C : Finset α := (Finset.range L).image (fun i => f^[i] x)
  have hCsub : C ⊆ S := by
    intro y hy; rcases Finset.mem_image.1 hy with ⟨i, _, rfl⟩; exact hiter i
  have hCcard : C.card = L := by
    rw [Finset.card_image_of_injOn]
    · exact Finset.card_range L
    · intro i hi j hj heq; exact hdist i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) heq
  have hCclosed : ∀ y ∈ C, f y ∈ C := by
    intro y hy; rcases Finset.mem_image.1 hy with ⟨i, hi, rfl⟩
    rw [Finset.mem_range] at hi; rw [← iter_succ f i x]
    by_cases hlast : i + 1 = L
    · rw [hlast, hL.2]; exact Finset.mem_image.2 ⟨0, Finset.mem_range.2 hL.1, rfl⟩
    · exact Finset.mem_image.2 ⟨i + 1, Finset.mem_range.2 (by omega), rfl⟩
  have hRestClosed : ∀ y ∈ S \ C, f y ∈ S \ C := by
    intro y hy; rcases Finset.mem_sdiff.1 hy with ⟨hyS, hyC⟩
    refine Finset.mem_sdiff.2 ⟨hf y hyS, ?_⟩
    intro hfyC; rcases Finset.mem_image.1 hfyC with ⟨i, hi, heq⟩; rw [Finset.mem_range] at hi
    by_cases hi0 : i = 0
    · subst hi0
      have hprev : f (f^[L - 1] x) = x := by
        rw [← iter_succ f (L - 1) x]
        have h1 : L - 1 + 1 = L := by omega
        rw [h1, hL.2]
      have hy_eq : y = f^[L - 1] x := hinj y hyS _ (hiter _) (by simpa [hprev] using heq.symm)
      exact hyC (hy_eq ▸ Finset.mem_image.2 ⟨L - 1, Finset.mem_range.2 (by omega), rfl⟩)
    · have hprev : f (f^[i - 1] x) = f^[i] x := by
        rw [← iter_succ f (i - 1) x]
        have h1 : i - 1 + 1 = i := by omega
        rw [h1]
      have hy_eq : y = f^[i - 1] x := hinj y hyS _ (hiter _) (by rw [hprev, heq])
      exact hyC (hy_eq ▸ Finset.mem_image.2 ⟨i - 1, Finset.mem_range.2 (by omega), rfl⟩)
  refine ⟨L, C, hL.1, hCsub, hCcard, ?_, ?_, hdist, hL.2, hCclosed, hRestClosed⟩
  · intro i hi; exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩
  · intro y hy; rcases Finset.mem_image.1 hy with ⟨i, hi, rfl⟩; exact ⟨i, Finset.mem_range.1 hi, rfl⟩

private lemma reanchor_orbit {S C : Finset α} {f : α → α} {x u : α} {L : ℕ}
    (hf : ∀ y ∈ S, f y ∈ S) (hinj : ∀ y ∈ S, ∀ z ∈ S, f y = f z → y = z)
    (hCsub : C ⊆ S) (hCcard : C.card = L)
    (hsurj : ∀ y ∈ C, ∃ i < L, f^[i] x = y) (hper : f^[L] x = x) (hCcl : ∀ y ∈ C, f y ∈ C)
    (huC : u ∈ C) :
    (∀ i < L, f^[i] u ∈ C) ∧
    (∀ y ∈ C, ∃ i < L, f^[i] u = y) ∧
    (∀ i < L, ∀ j < L, f^[i] u = f^[j] u → i = j) ∧
    f^[L] u = u := by
  rcases orbit_structure hf hinj (hCsub huC) with
    ⟨Lu, Cu, hLupos, _, hCucard, hmemu, hsurju, hdistu, hperu, hCucl, _⟩
  have hCu_eq : Cu = C := by
    have hsub1 : Cu ⊆ C := by
      intro y hy; rcases hsurju y hy with ⟨i, hi, rfl⟩; clear hi hy
      induction i with
      | zero => exact huC
      | succ i ih => rw [iter_succ]; exact hCcl _ ih
    have hsub2 : C ⊆ Cu := by
      rcases hsurj u huC with ⟨iu, hiu, rfl⟩
      intro y hy; rcases hsurj y hy with ⟨iy, hiy, rfl⟩
      have hshift : ∀ d, f^[d] (f^[iu] x) ∈ Cu := by
        intro d; induction d with
        | zero => exact hmemu 0 hLupos
        | succ d ih => rw [iter_succ]; exact hCucl _ ih
      by_cases hle : iu ≤ iy
      · have h1 := hshift (iy - iu)
        rw [← Function.iterate_add_apply] at h1
        have he : iy - iu + iu = iy := by omega
        rw [he] at h1; exact h1
      · have h1 := hshift (L + iy - iu)
        rw [← Function.iterate_add_apply] at h1
        have he : L + iy - iu + iu = iy + L := by omega
        rw [he, Function.iterate_add_apply, hper] at h1; exact h1
    exact Finset.Subset.antisymm hsub1 hsub2
  have hLu_eq : Lu = L := by rw [← hCucard, hCu_eq, hCcard]
  subst hLu_eq; rw [hCu_eq] at hmemu hsurju
  exact ⟨hmemu, hsurju, hdistu, hperu⟩

private def pairSegment (f : α → α) (x : α) (a : ℕ) : ℕ → α → α
  | 0, y => y
  | t + 1, y =>
    if y = f^[a + 2 * t] x then f^[a + 2 * t + 1] x
    else if y = f^[a + 2 * t + 1] x then f^[a + 2 * t] x
    else pairSegment f x a t y

private lemma pairSegment_spec {f : α → α} {x : α} {L a t : ℕ}
    (hbound : a + 2 * t ≤ L)
    (hdist : ∀ i < L, ∀ j < L, f^[i] x = f^[j] x → i = j) :
    Function.Involutive (pairSegment f x a t) ∧
    (∀ y, y ∉ (Finset.range (2 * t)).image (fun d => f^[a + d] x) → pairSegment f x a t y = y) ∧
    (∀ j < t, pairSegment f x a t (f^[a + 2 * j] x) = f^[a + 2 * j + 1] x ∧
              pairSegment f x a t (f^[a + 2 * j + 1] x) = f^[a + 2 * j] x) := by
  induction t with
  | zero =>
    refine ⟨fun _ => rfl, fun _ _ => rfl, fun j hj => by omega⟩
  | succ t ih =>
    rcases ih (by omega) with ⟨hinv, hsupp, hvals⟩
    have hne : f^[a + 2 * t] x ≠ f^[a + 2 * t + 1] x := by
      intro h; have := hdist (a + 2 * t) (by omega) (a + 2 * t + 1) (by omega) h; omega
    have hnot1 : f^[a + 2 * t] x ∉ (Finset.range (2 * t)).image (fun d => f^[a + d] x) := by
      intro hm; rcases Finset.mem_image.1 hm with ⟨d, hd, heq⟩
      rw [Finset.mem_range] at hd
      have := hdist (a + d) (by omega) (a + 2 * t) (by omega) heq; omega
    have hnot2 : f^[a + 2 * t + 1] x ∉ (Finset.range (2 * t)).image (fun d => f^[a + d] x) := by
      intro hm; rcases Finset.mem_image.1 hm with ⟨d, hd, heq⟩
      rw [Finset.mem_range] at hd
      have := hdist (a + d) (by omega) (a + 2 * t + 1) (by omega) heq; omega
    have hmem_prev : ∀ y, y ≠ f^[a + 2 * t] x → y ≠ f^[a + 2 * t + 1] x →
        pairSegment f x a t y ≠ f^[a + 2 * t] x ∧
        pairSegment f x a t y ≠ f^[a + 2 * t + 1] x := by
      intro y hy1 hy2; constructor
      · intro h; have := congrArg (pairSegment f x a t) h
        rw [hinv y, hsupp _ hnot1] at this; exact hy1 this
      · intro h; have := congrArg (pairSegment f x a t) h
        rw [hinv y, hsupp _ hnot2] at this; exact hy2 this
    refine ⟨?_, ?_, ?_⟩
    · intro y
      simp only [pairSegment]
      by_cases hy1 : y = f^[a + 2 * t] x
      · rw [hy1]; simp only [ite_true, hne.symm, ite_false]
      by_cases hy2 : y = f^[a + 2 * t + 1] x
      · rw [hy2]; simp only [hne.symm, ite_false, ite_true]
      · have hm := hmem_prev y hy1 hy2
        simp only [hy1, hy2, hm.1, hm.2, ite_false, hinv y]
    · intro y hy
      simp only [pairSegment]
      have hy1 : y ≠ f^[a + 2 * t] x := fun h =>
        hy (Finset.mem_image.2 ⟨2 * t, Finset.mem_range.2 (by omega), h.symm⟩)
      have hy2 : y ≠ f^[a + 2 * t + 1] x := fun h =>
        hy (Finset.mem_image.2 ⟨2 * t + 1, Finset.mem_range.2 (by omega), by rw [← Nat.add_assoc]; exact h.symm⟩)
      have hyprev : y ∉ (Finset.range (2 * t)).image (fun d => f^[a + d] x) := by
        intro hm; rcases Finset.mem_image.1 hm with ⟨d, hd, rfl⟩
        rw [Finset.mem_range] at hd
        exact hy (Finset.mem_image.2 ⟨d, Finset.mem_range.2 (by omega), rfl⟩)
      simp only [hy1, hy2, ite_false, hsupp y hyprev]
    · intro j hj
      by_cases hjt : j = t
      · rw [hjt]; simp only [pairSegment, ite_true, hne.symm, ite_false, and_self]
      · have hlt : j < t := by omega
        have he1 : f^[a + 2 * j] x ≠ f^[a + 2 * t] x := fun h => by
          have := hdist (a + 2 * j) (by omega) (a + 2 * t) (by omega) h; omega
        have he2 : f^[a + 2 * j] x ≠ f^[a + 2 * t + 1] x := fun h => by
          have := hdist (a + 2 * j) (by omega) (a + 2 * t + 1) (by omega) h; omega
        have ho1 : f^[a + 2 * j + 1] x ≠ f^[a + 2 * t] x := fun h => by
          have := hdist (a + 2 * j + 1) (by omega) (a + 2 * t) (by omega) h; omega
        have ho2 : f^[a + 2 * j + 1] x ≠ f^[a + 2 * t + 1] x := fun h => by
          have := hdist (a + 2 * j + 1) (by omega) (a + 2 * t + 1) (by omega) h; omega
        simp only [pairSegment, he1, he2, ho1, ho2, ite_false]
        exact hvals j hlt

private lemma exists_odd_orbit {S : Finset α} {f : α → α} (hf : ∀ x ∈ S, f x ∈ S)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y) (hodd : S.card % 2 = 1) :
    ∃ (x : α) (L : ℕ) (C : Finset α),
      x ∈ S ∧ L % 2 = 1 ∧ 0 < L ∧ C ⊆ S ∧ C.card = L ∧
      (∀ i < L, f^[i] x ∈ C) ∧
      (∀ y ∈ C, ∃ i < L, f^[i] x = y) ∧
      (∀ i < L, ∀ j < L, f^[i] x = f^[j] x → i = j) ∧
      f^[L] x = x ∧
      (∀ y ∈ C, f y ∈ C) ∧
      (∀ y ∈ S \ C, f y ∈ S \ C) := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ m ih =>
    have hne : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty; rw [hempty, Finset.card_empty] at hodd; omega
    rcases hne with ⟨x, hx⟩
    rcases orbit_structure hf hinj hx with
      ⟨L, C, hLpos, hCsub, hCcard, hmem, hsurj, hdist, hper, hCcl, hRcl⟩
    by_cases hLodd : L % 2 = 1
    · exact ⟨x, L, C, hx, hLodd, hLpos, hCsub, hCcard, hmem, hsurj, hdist, hper, hCcl, hRcl⟩
    · have hCle : L ≤ S.card := hCcard ▸ Finset.card_le_card hCsub
      have hcard_sdiff : (S \ C).card = S.card - L := by rw [Finset.card_sdiff_of_subset hCsub, hCcard]
      have hcard_lt : (S \ C).card < m := by omega
      have hodd' : (S \ C).card % 2 = 1 := by omega
      have hinj' : ∀ y ∈ S \ C, ∀ z ∈ S \ C, f y = f z → y = z := fun y hy z hz =>
        hinj y (Finset.mem_sdiff.1 hy).1 z (Finset.mem_sdiff.1 hz).1
      rcases ih (S \ C).card hcard_lt hRcl hinj' hodd' rfl with
        ⟨x', L', C', hx', hL'odd, hL'pos, hC'sub, hC'card, hmem', hsurj', hdist', hper', hC'cl, _⟩
      have hC'subS : C' ⊆ S := hC'sub.trans Finset.sdiff_subset
      have hR'cl : ∀ y ∈ S \ C', f y ∈ S \ C' := by
        intro y hy; rcases Finset.mem_sdiff.1 hy with ⟨hyS, hyC'⟩
        refine Finset.mem_sdiff.2 ⟨hf y hyS, ?_⟩
        intro hfyC'; rcases hsurj' (f y) hfyC' with ⟨i, hi, heq⟩
        by_cases hi0 : i = 0
        · subst hi0
          have hprev : f (f^[L' - 1] x') = x' := by
            rw [← iter_succ f (L' - 1) x']
            have h1 : L' - 1 + 1 = L' := by omega
            rw [h1, hper']
          have hmemprev : f^[L' - 1] x' ∈ S := hC'subS (hmem' (L' - 1) (by omega))
          have hy_eq : y = f^[L' - 1] x' := hinj y hyS _ hmemprev (by simpa [hprev] using heq.symm)
          exact hyC' (hy_eq ▸ hmem' (L' - 1) (by omega))
        · have hprev : f (f^[i - 1] x') = f^[i] x' := by
            rw [← iter_succ f (i - 1) x']
            have h1 : i - 1 + 1 = i := by omega
            rw [h1]
          have hmemprev : f^[i - 1] x' ∈ S := hC'subS (hmem' (i - 1) (by omega))
          have hy_eq : y = f^[i - 1] x' := hinj y hyS _ hmemprev (by rw [hprev, heq])
          exact hyC' (hy_eq ▸ hmem' (i - 1) (by omega))
      exact ⟨x', L', C', (Finset.mem_sdiff.1 hx').1, hL'odd, hL'pos, hC'subS, hC'card,
        hmem', hsurj', hdist', hper', hC'cl, hR'cl⟩

private lemma pair_even_invariant {S : Finset α} {f : α → α} (hf : ∀ x ∈ S, f x ∈ S)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y)
    (hno1 : ∀ x ∈ S, f x ≠ x) (hno2 : ∀ x ∈ S, f (f x) ≠ x)
    (heven : S.card % 2 = 0) (bad : α) :
    ∃ g : α → α,
      Function.Involutive g ∧
      (∀ x, x ∉ S → g x = x) ∧
      (∀ x ∈ S, g x ∈ S ∧ g x ≠ x) ∧
      (∀ x ∈ S, g x = f x ∨ f (g x) = x ∨
        (x ≠ bad ∧ ∀ y ∈ S, f y = x → f (g y) = y)) := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ m ih =>
    by_cases hS : S = ∅
    · subst hS; exact ⟨id, fun _ => rfl, fun _ _ => rfl, by simp, by simp⟩
    · rcases Finset.nonempty_iff_ne_empty.2 hS with ⟨x, hx⟩
      rcases orbit_structure hf hinj hx with
        ⟨L, C, hLpos, hCsub, hCcard, hmem, hsurj, hdist, hper, hCcl, hRcl⟩
      have hLge3 : 3 ≤ L := by
        by_contra hlt; have h12 : L = 1 ∨ L = 2 := by omega
        rcases h12 with rfl | rfl
        · exact hno1 x hx (by simpa using hper)
        · exact hno2 x hx (by rw [iter_succ] at hper; simpa using hper)
      by_cases hLeven : L % 2 = 0
      · let t := L / 2
        have hspec := pairSegment_spec (f := f) (x := x) (L := L) (a := 0) (t := t) (by omega) hdist
        have hseg_eq : (Finset.range (2 * t)).image (fun d => f^[0 + d] x) = C := by
          ext y; simp only [Finset.mem_image, Finset.mem_range, zero_add]
          constructor
          · rintro ⟨d, hd, rfl⟩; exact hmem d (by omega)
          · intro hy; rcases hsurj y hy with ⟨d, hd, rfl⟩; exact ⟨d, by omega, rfl⟩
        have hCle : L ≤ S.card := hCcard ▸ Finset.card_le_card hCsub
        have hcard_lt : (S \ C).card < m := by rw [Finset.card_sdiff_of_subset hCsub, hCcard]; omega
        have heven' : (S \ C).card % 2 = 0 := by rw [Finset.card_sdiff_of_subset hCsub, hCcard]; omega
        have hinj' : ∀ u ∈ S \ C, ∀ v ∈ S \ C, f u = f v → u = v := fun u hu v hv =>
          hinj u (Finset.mem_sdiff.1 hu).1 v (Finset.mem_sdiff.1 hv).1
        rcases ih (S \ C).card hcard_lt hRcl hinj'
            (fun u hu => hno1 u (Finset.mem_sdiff.1 hu).1)
            (fun u hu => hno2 u (Finset.mem_sdiff.1 hu).1) heven' rfl with
          ⟨g₂, hg₂inv, hg₂supp, hg₂in, hg₂good⟩
        have hdisj : Disjoint C (S \ C) := Finset.disjoint_sdiff
        have hg1supp : ∀ y, y ∉ C → pairSegment f x 0 t y = y := fun y hy => hspec.2.1 y (hseg_eq.symm ▸ hy)
        have hgl := glue_involution hdisj hspec.1 hg1supp hg₂inv hg₂supp
        refine ⟨glue C (pairSegment f x 0 t) g₂, hgl.1, ?_, ?_, ?_⟩
        · intro y hy; apply hgl.2.2.2; rw [Finset.union_sdiff_of_subset hCsub]; exact hy
        · intro y hyS
          by_cases hyC : y ∈ C
          · rw [hgl.2.1 y hyC]; rcases hsurj y hyC with ⟨d, hd, rfl⟩
            have hdiv : d = 2 * (d / 2) ∨ d = 2 * (d / 2) + 1 := by omega
            rcases hdiv with h | h
            · have hv := (hspec.2.2 (d / 2) (by omega)).1; rw [Nat.zero_add] at hv
              rw [h, hv]; refine ⟨hCsub (hmem _ (by omega)), ?_⟩
              intro heq; have := hdist (2 * (d / 2) + 1) (by omega) (2 * (d / 2)) (by omega) heq; omega
            · have hv := (hspec.2.2 (d / 2) (by omega)).2; rw [Nat.zero_add] at hv
              rw [h, hv]; refine ⟨hCsub (hmem _ (by omega)), ?_⟩
              intro heq; have := hdist (2 * (d / 2)) (by omega) (2 * (d / 2) + 1) (by omega) heq; omega
          · have hySC : y ∈ S \ C := Finset.mem_sdiff.2 ⟨hyS, hyC⟩
            rw [hgl.2.2.1 y hySC]; exact ⟨Finset.sdiff_subset (hg₂in y hySC).1, (hg₂in y hySC).2⟩
        · intro y hyS
          by_cases hyC : y ∈ C
          · rw [hgl.2.1 y hyC]; rcases hsurj y hyC with ⟨d, hd, rfl⟩
            have hdiv : d = 2 * (d / 2) ∨ d = 2 * (d / 2) + 1 := by omega
            rcases hdiv with h | h
            · left; have hv := (hspec.2.2 (d / 2) (by omega)).1; rw [Nat.zero_add] at hv
              rw [h, hv, iter_succ]
            · right; left; have hv := (hspec.2.2 (d / 2) (by omega)).2; rw [Nat.zero_add] at hv
              rw [h, hv, ← iter_succ f (2 * (d / 2)) x]
          · have hySC : y ∈ S \ C := Finset.mem_sdiff.2 ⟨hyS, hyC⟩
            rw [hgl.2.2.1 y hySC]
            rcases hg₂good y hySC with h1 | h2 | ⟨hnebad, hprev⟩
            · exact Or.inl h1
            · exact Or.inr (Or.inl h2)
            · right; right; refine ⟨hnebad, ?_⟩
              intro z hzS hfz
              have hzSC : z ∈ S \ C := Finset.mem_sdiff.2 ⟨hzS, fun hzC => hyC (hfz ▸ hCcl z hzC)⟩
              rw [hgl.2.2.1 z hzSC]; exact hprev z hzSC hfz
      · have hLodd : L % 2 = 1 := by omega
        have hCle : L ≤ S.card := hCcard ▸ Finset.card_le_card hCsub
        have hodd_rest : (S \ C).card % 2 = 1 := by rw [Finset.card_sdiff_of_subset hCsub, hCcard]; omega
        have hinj' : ∀ u ∈ S \ C, ∀ v ∈ S \ C, f u = f v → u = v := fun u hu v hv =>
          hinj u (Finset.mem_sdiff.1 hu).1 v (Finset.mem_sdiff.1 hv).1
        rcases exists_odd_orbit hRcl hinj' hodd_rest with
          ⟨x', L', C', hx', hL'odd, hL'pos, hC'sub, hC'card, hmem', hsurj', hdist', hper', hC'cl, hR'cl⟩
        have hL'ge3 : 3 ≤ L' := by
          by_contra hlt; have h12 : L' = 1 ∨ L' = 2 := by omega
          rcases h12 with rfl | rfl
          · exact hno1 x' (Finset.mem_sdiff.1 hx').1 (by simpa using hper')
          · exact hno2 x' (Finset.mem_sdiff.1 hx').1 (by rw [iter_succ] at hper'; simpa using hper')
        have hex_u : ∃ u ∈ C, u ≠ bad := by
          by_cases h1 : x ≠ bad
          · exact ⟨x, hmem 0 hLpos, h1⟩
          · exact ⟨f x, hmem 1 (by omega), fun h2 => hno1 x hx (h2.trans (not_ne_iff.1 h1).symm)⟩
        have hex_v : ∃ v ∈ C', v ≠ bad := by
          by_cases h1 : x' ≠ bad
          · exact ⟨x', hmem' 0 hL'pos, h1⟩
          · exact ⟨f x', hmem' 1 (by omega), fun h2 => hno1 x' (Finset.mem_sdiff.1 hx').1 (h2.trans (not_ne_iff.1 h1).symm)⟩
        rcases hex_u with ⟨u, huC, hubad⟩
        rcases hex_v with ⟨v, hvC', hvbad⟩
        rcases reanchor_orbit hf hinj hCsub hCcard hsurj hper hCcl huC with
          ⟨hmemu, hsurju, hdistu, hperu⟩
        rcases reanchor_orbit hRcl hinj' hC'sub hC'card hsurj' hper' hC'cl hvC' with
          ⟨hmemv, hsurjv, hdistv, hperv⟩
        let t := L / 2; let t' := L' / 2
        have hspecC := pairSegment_spec (f := f) (x := u) (L := L) (a := 1) (t := t) (by omega) hdistu
        have hsegC : (Finset.range (2 * t)).image (fun d => f^[1 + d] u) = C.erase u := by
          ext y; simp only [Finset.mem_image, Finset.mem_range, Finset.mem_erase]
          constructor
          · rintro ⟨d, hd, rfl⟩
            refine ⟨?_, hmemu (1 + d) (by omega)⟩
            intro heq; have := hdistu (1 + d) (by omega) 0 hLpos (by simpa using heq); omega
          · rintro ⟨hne, hyC⟩; rcases hsurju y hyC with ⟨i, hi, rfl⟩
            have hi0 : i ≠ 0 := fun h => hne (by simp [h])
            exact ⟨i - 1, by omega, by congr 1; omega⟩
        have hspecC' := pairSegment_spec (f := f) (x := v) (L := L') (a := 1) (t := t') (by omega) hdistv
        have hsegC' : (Finset.range (2 * t')).image (fun d => f^[1 + d] v) = C'.erase v := by
          ext y; simp only [Finset.mem_image, Finset.mem_range, Finset.mem_erase]
          constructor
          · rintro ⟨d, hd, rfl⟩
            refine ⟨?_, hmemv (1 + d) (by omega)⟩
            intro heq; have := hdistv (1 + d) (by omega) 0 hL'pos (by simpa using heq); omega
          · rintro ⟨hne, hyC'⟩; rcases hsurjv y hyC' with ⟨i, hi, rfl⟩
            have hi0 : i ≠ 0 := fun h => hne (by simp [h])
            exact ⟨i - 1, by omega, by congr 1; omega⟩
        have hCC'disj : Disjoint C C' := Finset.disjoint_of_subset_right hC'sub Finset.disjoint_sdiff
        have huv : u ≠ v := fun h => Finset.disjoint_left.1 hCC'disj huC (h ▸ hvC')
        have hd1 : Disjoint ({u, v} : Finset α) (C.erase u) := by
          rw [Finset.disjoint_left]; intro y hy1 hy2
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy1
          rcases hy1 with rfl | rfl
          · exact (Finset.mem_erase.1 hy2).1 rfl
          · exact Finset.disjoint_right.1 hCC'disj hvC' (Finset.mem_erase.1 hy2).2
        have hgCsupp : ∀ y, y ∉ C.erase u → pairSegment f u 1 t y = y := fun y hy => hspecC.2.1 y (hsegC.symm ▸ hy)
        have hgl1 := glue_involution hd1 (swap2_inv u v) (swap2_supp u v) hspecC.1 hgCsupp
        have hd2 : Disjoint ({u, v} ∪ C.erase u) (C'.erase v) := by
          rw [Finset.disjoint_left]; intro y hy1 hy2; rw [Finset.mem_union] at hy1
          rcases hy1 with hyuv | hyCu
          · simp only [Finset.mem_insert, Finset.mem_singleton] at hyuv
            rcases hyuv with rfl | rfl
            · exact Finset.disjoint_left.1 hCC'disj huC (Finset.mem_erase.1 hy2).2
            · exact (Finset.mem_erase.1 hy2).1 rfl
          · exact Finset.disjoint_left.1 hCC'disj (Finset.mem_erase.1 hyCu).2 (Finset.mem_erase.1 hy2).2
        have hgC'supp : ∀ y, y ∉ C'.erase v → pairSegment f v 1 t' y = y := fun y hy => hspecC'.2.1 y (hsegC'.symm ▸ hy)
        have hgl2 := glue_involution hd2 hgl1.1 hgl1.2.2.2 hspecC'.1 hgC'supp
        have hunion_eq : ({u, v} ∪ C.erase u) ∪ C'.erase v = C ∪ C' := by
          ext y; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
          constructor
          · rintro (((rfl | rfl) | ⟨_, hyC⟩) | ⟨_, hyC'⟩)
            · exact Or.inl huC
            · exact Or.inr hvC'
            · exact Or.inl hyC
            · exact Or.inr hyC'
          · rintro (hyC | hyC')
            · by_cases hyu : y = u
              · exact Or.inl (Or.inl (Or.inl hyu))
              · exact Or.inl (Or.inr ⟨hyu, hyC⟩)
            · by_cases hyv : y = v
              · exact Or.inl (Or.inl (Or.inr hyv))
              · exact Or.inr ⟨hyv, hyC'⟩
        let S' := (S \ C) \ C'
        have hS'_eq : S' = S \ (C ∪ C') := by
          ext y; simp only [S', Finset.mem_sdiff, Finset.mem_union, not_or]; exact and_assoc
        have hCC'sub : C ∪ C' ⊆ S := Finset.union_subset hCsub (hC'sub.trans Finset.sdiff_subset)
        have hleCC' : L + L' ≤ S.card := by
          have := Finset.card_le_card hCC'sub
          rw [Finset.card_union_of_disjoint hCC'disj, hCcard, hC'card] at this; exact this
        have hS'card : S'.card = S.card - (L + L') := by
          rw [hS'_eq, Finset.card_sdiff_of_subset hCC'sub, Finset.card_union_of_disjoint hCC'disj, hCcard, hC'card]
        have hS'inj : ∀ a ∈ S', ∀ b ∈ S', f a = f b → a = b := fun a ha b hb =>
          hinj a (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 ha).1).1
               b (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 hb).1).1
        have hS'even : S'.card % 2 = 0 := by rw [hS'card]; omega
        rcases ih S'.card (by omega) hR'cl hS'inj
            (fun a ha => hno1 a (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 ha).1).1)
            (fun a ha => hno2 a (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 ha).1).1)
            hS'even rfl with ⟨gR, hgR_inv, hgR_supp, hgR_in, hgR_good⟩
        have hdisj_all : Disjoint (C ∪ C') S' := by rw [hS'_eq]; exact Finset.disjoint_sdiff
        let g12 := glue ({u, v} ∪ C.erase u) (glue ({u, v} : Finset α) (swap2 u v) (pairSegment f u 1 t)) (pairSegment f v 1 t')
        have hg12supp : ∀ y, y ∉ C ∪ C' → g12 y = y := fun y hy => hgl2.2.2.2 y (hunion_eq.symm ▸ hy)
        have hgl_all := glue_involution hdisj_all hgl2.1 hg12supp hgR_inv hgR_supp
        let g := glue (C ∪ C') g12 gR
        have hg_u : g u = v := by
          show glue (C ∪ C') g12 gR u = v
          rw [hgl_all.2.1 u (Finset.mem_union_left _ huC)]
          show glue ({u, v} ∪ C.erase u) (glue ({u, v} : Finset α) (swap2 u v) (pairSegment f u 1 t)) (pairSegment f v 1 t') u = v
          rw [hgl2.2.1 u (Finset.mem_union_left _ (by simp)), hgl1.2.1 u (by simp), swap2_left]
        have hg_v : g v = u := by
          show glue (C ∪ C') g12 gR v = u
          rw [hgl_all.2.1 v (Finset.mem_union_right _ hvC')]
          show glue ({u, v} ∪ C.erase u) (glue ({u, v} : Finset α) (swap2 u v) (pairSegment f u 1 t)) (pairSegment f v 1 t') v = u
          rw [hgl2.2.1 v (Finset.mem_union_left _ (by simp)), hgl1.2.1 v (by simp), swap2_right]
        have hg_Cu : ∀ y ∈ C.erase u, g y = pairSegment f u 1 t y := by
          intro y hy
          show glue (C ∪ C') g12 gR y = pairSegment f u 1 t y
          rw [hgl_all.2.1 y (Finset.mem_union_left _ (Finset.mem_erase.1 hy).2)]
          show glue ({u, v} ∪ C.erase u) (glue ({u, v} : Finset α) (swap2 u v) (pairSegment f u 1 t)) (pairSegment f v 1 t') y = pairSegment f u 1 t y
          rw [hgl2.2.1 y (Finset.mem_union_right _ hy), hgl1.2.2.1 y hy]
        have hg_C'v : ∀ y ∈ C'.erase v, g y = pairSegment f v 1 t' y := by
          intro y hy
          show glue (C ∪ C') g12 gR y = pairSegment f v 1 t' y
          rw [hgl_all.2.1 y (Finset.mem_union_right _ (Finset.mem_erase.1 hy).2)]
          show glue ({u, v} ∪ C.erase u) (glue ({u, v} : Finset α) (swap2 u v) (pairSegment f u 1 t)) (pairSegment f v 1 t') y = pairSegment f v 1 t' y
          rw [hgl2.2.2.1 y hy]
        have hg_R : ∀ y ∈ S', g y = gR y := hgl_all.2.2.1
        refine ⟨g, hgl_all.1, ?_, ?_, ?_⟩
        · intro y hy; apply hgl_all.2.2.2; rw [hS'_eq, Finset.union_sdiff_of_subset hCC'sub]; exact hy
        · intro y hyS
          by_cases hyu : y = u
          · rw [hyu, hg_u]; exact ⟨(hC'sub.trans Finset.sdiff_subset) hvC', huv.symm⟩
          by_cases hyv : y = v
          · rw [hyv, hg_v]; exact ⟨hCsub huC, huv⟩
          by_cases hyC : y ∈ C
          · have hyCu : y ∈ C.erase u := Finset.mem_erase.2 ⟨hyu, hyC⟩
            rw [hg_Cu y hyCu]; rcases hsurju y hyC with ⟨i, hi, rfl⟩
            have hi0 : i ≠ 0 := fun h => hyu (by simp [h])
            have hdiv : i - 1 = 2 * ((i - 1) / 2) ∨ i - 1 = 2 * ((i - 1) / 2) + 1 := by omega
            rcases hdiv with h | h
            · have hi_eq : i = 1 + 2 * ((i - 1) / 2) := by omega
              have hv := (hspecC.2.2 ((i - 1) / 2) (by omega)).1
              rw [hi_eq, hv]; refine ⟨hCsub (hmemu _ (by omega)), ?_⟩
              intro heq; have := hdistu (1 + 2 * ((i - 1) / 2) + 1) (by omega) (1 + 2 * ((i - 1) / 2)) (by omega) heq; omega
            · have hi_eq : i = 1 + 2 * ((i - 1) / 2) + 1 := by omega
              have hv := (hspecC.2.2 ((i - 1) / 2) (by omega)).2
              rw [hi_eq, hv]; refine ⟨hCsub (hmemu _ (by omega)), ?_⟩
              intro heq; have := hdistu (1 + 2 * ((i - 1) / 2)) (by omega) (1 + 2 * ((i - 1) / 2) + 1) (by omega) heq; omega
          by_cases hyC' : y ∈ C'
          · have hyC'v : y ∈ C'.erase v := Finset.mem_erase.2 ⟨hyv, hyC'⟩
            rw [hg_C'v y hyC'v]; rcases hsurjv y hyC' with ⟨i, hi, rfl⟩
            have hi0 : i ≠ 0 := fun h => hyv (by simp [h])
            have hdiv : i - 1 = 2 * ((i - 1) / 2) ∨ i - 1 = 2 * ((i - 1) / 2) + 1 := by omega
            rcases hdiv with h | h
            · have hi_eq : i = 1 + 2 * ((i - 1) / 2) := by omega
              have hv := (hspecC'.2.2 ((i - 1) / 2) (by omega)).1
              rw [hi_eq, hv]; refine ⟨(hC'sub.trans Finset.sdiff_subset) (hmemv _ (by omega)), ?_⟩
              intro heq; have := hdistv (1 + 2 * ((i - 1) / 2) + 1) (by omega) (1 + 2 * ((i - 1) / 2)) (by omega) heq; omega
            · have hi_eq : i = 1 + 2 * ((i - 1) / 2) + 1 := by omega
              have hv := (hspecC'.2.2 ((i - 1) / 2) (by omega)).2
              rw [hi_eq, hv]; refine ⟨(hC'sub.trans Finset.sdiff_subset) (hmemv _ (by omega)), ?_⟩
              intro heq; have := hdistv (1 + 2 * ((i - 1) / 2)) (by omega) (1 + 2 * ((i - 1) / 2) + 1) (by omega) heq; omega
          · have hyS' : y ∈ S' := by rw [hS'_eq]; exact Finset.mem_sdiff.2 ⟨hyS, by simp [hyC, hyC']⟩
            rw [hg_R y hyS']
            have hsub : S' ⊆ S := by rw [hS'_eq]; exact Finset.sdiff_subset
            exact ⟨hsub (hgR_in y hyS').1, (hgR_in y hyS').2⟩
        · intro y hyS
          by_cases hyu : y = u
          · rw [hyu]; right; right; refine ⟨hubad, ?_⟩
            intro z hzS hfz
            have hprev_eq : f (f^[2 * t] u) = u := by
              rw [← iter_succ f (2 * t) u]
              have h1 : 2 * t + 1 = L := by omega
              rw [h1, hperu]
            have hz_eq : z = f^[2 * t] u := hinj z hzS _ (hCsub (hmemu (2 * t) (by omega))) (hfz.trans hprev_eq.symm)
            rw [hz_eq]
            have hzCu : f^[2 * t] u ∈ C.erase u := Finset.mem_erase.2 ⟨by
              intro h; have := hdistu (2 * t) (by omega) 0 hLpos (by simpa using h); omega,
              hmemu (2 * t) (by omega)⟩
            rw [hg_Cu _ hzCu]
            have hidx : 2 * t = 1 + 2 * (t - 1) + 1 := by omega
            have hv := (hspecC.2.2 (t - 1) (by omega)).2
            rw [hidx, hv, ← iter_succ f (1 + 2 * (t - 1)) u]
          by_cases hyv : y = v
          · rw [hyv]; right; right; refine ⟨hvbad, ?_⟩
            intro z hzS hfz
            have hprev_eq : f (f^[2 * t'] v) = v := by
              rw [← iter_succ f (2 * t') v]
              have h1 : 2 * t' + 1 = L' := by omega
              rw [h1, hperv]
            have hz_eq : z = f^[2 * t'] v := hinj z hzS _ ((hC'sub.trans Finset.sdiff_subset) (hmemv (2 * t') (by omega))) (hfz.trans hprev_eq.symm)
            rw [hz_eq]
            have hzC'v : f^[2 * t'] v ∈ C'.erase v := Finset.mem_erase.2 ⟨by
              intro h; have := hdistv (2 * t') (by omega) 0 hL'pos (by simpa using h); omega,
              hmemv (2 * t') (by omega)⟩
            rw [hg_C'v _ hzC'v]
            have hidx : 2 * t' = 1 + 2 * (t' - 1) + 1 := by omega
            have hv := (hspecC'.2.2 (t' - 1) (by omega)).2
            rw [hidx, hv, ← iter_succ f (1 + 2 * (t' - 1)) v]
          by_cases hyC : y ∈ C
          · have hyCu : y ∈ C.erase u := Finset.mem_erase.2 ⟨hyu, hyC⟩
            rw [hg_Cu y hyCu]; rcases hsurju y hyC with ⟨i, hi, rfl⟩
            have hi0 : i ≠ 0 := fun h => hyu (by simp [h])
            have hdiv : i - 1 = 2 * ((i - 1) / 2) ∨ i - 1 = 2 * ((i - 1) / 2) + 1 := by omega
            rcases hdiv with h | h
            · left; have hi_eq : i = 1 + 2 * ((i - 1) / 2) := by omega
              have hv := (hspecC.2.2 ((i - 1) / 2) (by omega)).1; rw [hi_eq, hv, iter_succ]
            · right; left; have hi_eq : i = 1 + 2 * ((i - 1) / 2) + 1 := by omega
              have hv := (hspecC.2.2 ((i - 1) / 2) (by omega)).2; rw [hi_eq, hv, ← iter_succ f (1 + 2 * ((i - 1) / 2)) u]
          by_cases hyC' : y ∈ C'
          · have hyC'v : y ∈ C'.erase v := Finset.mem_erase.2 ⟨hyv, hyC'⟩
            rw [hg_C'v y hyC'v]; rcases hsurjv y hyC' with ⟨i, hi, rfl⟩
            have hi0 : i ≠ 0 := fun h => hyv (by simp [h])
            have hdiv : i - 1 = 2 * ((i - 1) / 2) ∨ i - 1 = 2 * ((i - 1) / 2) + 1 := by omega
            rcases hdiv with h | h
            · left; have hi_eq : i = 1 + 2 * ((i - 1) / 2) := by omega
              have hv := (hspecC'.2.2 ((i - 1) / 2) (by omega)).1; rw [hi_eq, hv, iter_succ]
            · right; left; have hi_eq : i = 1 + 2 * ((i - 1) / 2) + 1 := by omega
              have hv := (hspecC'.2.2 ((i - 1) / 2) (by omega)).2; rw [hi_eq, hv, ← iter_succ f (1 + 2 * ((i - 1) / 2)) v]
          · have hyS' : y ∈ S' := by rw [hS'_eq]; exact Finset.mem_sdiff.2 ⟨hyS, by simp [hyC, hyC']⟩
            rw [hg_R y hyS']
            rcases hgR_good y hyS' with h1 | h2 | ⟨hnebad, hprev⟩
            · exact Or.inl h1
            · exact Or.inr (Or.inl h2)
            · right; right; refine ⟨hnebad, ?_⟩
              intro z hzS hfz
              have hznotC : z ∉ C := fun hzC => hyC (hfz ▸ hCcl z hzC)
              have hznotC' : z ∉ C' := fun hzC' => hyC' (hfz ▸ hC'cl z hzC')
              have hzS' : z ∈ S' := by rw [hS'_eq]; exact Finset.mem_sdiff.2 ⟨hzS, by simp [hznotC, hznotC']⟩
              rw [hg_R z hzS']; exact hprev z hzS' hfz

private lemma pair_odd_punctured {U : Finset α} {f : α → α} (hf : ∀ x ∈ U, f x ∈ U)
    (hinj : ∀ x ∈ U, ∀ y ∈ U, f x = f y → x = y)
    (hno1 : ∀ x ∈ U, f x ≠ x) (hno2 : ∀ x ∈ U, f (f x) ≠ x)
    (hodd : U.card % 2 = 1) {c : α} (hc : c ∈ U) (bad : α) :
    ∃ g : α → α,
      Function.Involutive g ∧
      (∀ x, x ∉ U.erase c → g x = x) ∧
      (∀ x ∈ U.erase c, g x ∈ U.erase c ∧ g x ≠ x) ∧
      (∀ x ∈ U.erase c, g x = f x ∨ f (g x) = x ∨
        (x ≠ bad ∧ ∀ y ∈ U, f y = x → y = c ∨ f (g y) = y)) := by
  rcases orbit_structure hf hinj hc with
    ⟨L, C, hLpos, hCsub, hCcard, hmem, hsurj, hdist, hper, hCcl, hRcl⟩
  have hLge3 : 3 ≤ L := by
    by_contra hlt; have h12 : L = 1 ∨ L = 2 := by omega
    rcases h12 with rfl | rfl
    · exact hno1 c hc (by simpa using hper)
    · exact hno2 c hc (by rw [iter_succ] at hper; simpa using hper)
  by_cases hLodd : L % 2 = 1
  · let t := L / 2
    have hspecC := pairSegment_spec (f := f) (x := c) (L := L) (a := 1) (t := t) (by omega) hdist
    have hsegC : (Finset.range (2 * t)).image (fun d => f^[1 + d] c) = C.erase c := by
      ext y; simp only [Finset.mem_image, Finset.mem_range, Finset.mem_erase]
      constructor
      · rintro ⟨d, hd, rfl⟩
        refine ⟨?_, hmem (1 + d) (by omega)⟩
        intro heq; have := hdist (1 + d) (by omega) 0 hLpos (by simpa using heq); omega
      · rintro ⟨hne, hyC⟩; rcases hsurj y hyC with ⟨i, hi, rfl⟩
        have hi0 : i ≠ 0 := fun h => hne (by simp [h])
        exact ⟨i - 1, by omega, by congr 1; omega⟩
    have hCle : L ≤ U.card := hCcard ▸ Finset.card_le_card hCsub
    have heven_rest : (U \ C).card % 2 = 0 := by rw [Finset.card_sdiff_of_subset hCsub, hCcard]; omega
    have hinj' : ∀ u ∈ U \ C, ∀ v ∈ U \ C, f u = f v → u = v := fun u hu v hv =>
      hinj u (Finset.mem_sdiff.1 hu).1 v (Finset.mem_sdiff.1 hv).1
    rcases pair_even_invariant hRcl hinj'
        (fun u hu => hno1 u (Finset.mem_sdiff.1 hu).1)
        (fun u hu => hno2 u (Finset.mem_sdiff.1 hu).1) heven_rest bad with
      ⟨gR, hgR_inv, hgR_supp, hgR_in, hgR_good⟩
    have hdisj : Disjoint (C.erase c) (U \ C) :=
      Finset.disjoint_of_subset_left (Finset.erase_subset _ _) Finset.disjoint_sdiff
    have hgCsupp : ∀ y, y ∉ C.erase c → pairSegment f c 1 t y = y := fun y hy => hspecC.2.1 y (hsegC.symm ▸ hy)
    have hgl := glue_involution hdisj hspecC.1 hgCsupp hgR_inv hgR_supp
    have hunion : C.erase c ∪ (U \ C) = U.erase c := by
      ext y; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, hCsub h2⟩
        · exact ⟨fun heq => h2 (heq ▸ hmem 0 hLpos), h1⟩
      · rintro ⟨hne, hyU⟩
        by_cases hyC : y ∈ C
        · exact Or.inl ⟨hne, hyC⟩
        · exact Or.inr ⟨hyU, hyC⟩
    refine ⟨glue (C.erase c) (pairSegment f c 1 t) gR, hgl.1, fun y hy => hgl.2.2.2 y (hunion.symm ▸ hy), ?_, ?_⟩
    · intro y hy; rcases Finset.mem_erase.1 hy with ⟨hyc, hyU⟩
      by_cases hyC : y ∈ C
      · have hyCc : y ∈ C.erase c := Finset.mem_erase.2 ⟨hyc, hyC⟩
        rw [hgl.2.1 y hyCc]; rcases hsurj y hyC with ⟨i, hi, rfl⟩
        have hi0 : i ≠ 0 := fun h => hyc (by simp [h])
        have hdiv : i - 1 = 2 * ((i - 1) / 2) ∨ i - 1 = 2 * ((i - 1) / 2) + 1 := by omega
        rcases hdiv with h | h
        · have hi_eq : i = 1 + 2 * ((i - 1) / 2) := by omega
          have hv := (hspecC.2.2 ((i - 1) / 2) (by omega)).1
          rw [hi_eq, hv]
          refine ⟨Finset.mem_erase.2 ⟨?_, hCsub (hmem _ (by omega))⟩, ?_⟩
          · intro heq; have := hdist (1 + 2 * ((i - 1) / 2) + 1) (by omega) 0 hLpos (by simpa using heq); omega
          · intro heq; have := hdist (1 + 2 * ((i - 1) / 2) + 1) (by omega) (1 + 2 * ((i - 1) / 2)) (by omega) heq; omega
        · have hi_eq : i = 1 + 2 * ((i - 1) / 2) + 1 := by omega
          have hv := (hspecC.2.2 ((i - 1) / 2) (by omega)).2
          rw [hi_eq, hv]
          refine ⟨Finset.mem_erase.2 ⟨?_, hCsub (hmem _ (by omega))⟩, ?_⟩
          · intro heq; have := hdist (1 + 2 * ((i - 1) / 2)) (by omega) 0 hLpos (by simpa using heq); omega
          · intro heq; have := hdist (1 + 2 * ((i - 1) / 2)) (by omega) (1 + 2 * ((i - 1) / 2) + 1) (by omega) heq; omega
      · have hyUC : y ∈ U \ C := Finset.mem_sdiff.2 ⟨hyU, hyC⟩
        rw [hgl.2.2.1 y hyUC]
        have hgy := hgR_in y hyUC
        exact ⟨Finset.mem_erase.2 ⟨fun heq => (Finset.mem_sdiff.1 hgy.1).2 (heq ▸ hmem 0 hLpos),
          (Finset.mem_sdiff.1 hgy.1).1⟩, hgy.2⟩
    · intro y hy; rcases Finset.mem_erase.1 hy with ⟨hyc, hyU⟩
      by_cases hyC : y ∈ C
      · have hyCc : y ∈ C.erase c := Finset.mem_erase.2 ⟨hyc, hyC⟩
        rw [hgl.2.1 y hyCc]; rcases hsurj y hyC with ⟨i, hi, rfl⟩
        have hi0 : i ≠ 0 := fun h => hyc (by simp [h])
        have hdiv : i - 1 = 2 * ((i - 1) / 2) ∨ i - 1 = 2 * ((i - 1) / 2) + 1 := by omega
        rcases hdiv with h | h
        · left; have hi_eq : i = 1 + 2 * ((i - 1) / 2) := by omega
          have hv := (hspecC.2.2 ((i - 1) / 2) (by omega)).1; rw [hi_eq, hv, iter_succ]
        · right; left; have hi_eq : i = 1 + 2 * ((i - 1) / 2) + 1 := by omega
          have hv := (hspecC.2.2 ((i - 1) / 2) (by omega)).2; rw [hi_eq, hv, ← iter_succ f (1 + 2 * ((i - 1) / 2)) c]
      · have hyUC : y ∈ U \ C := Finset.mem_sdiff.2 ⟨hyU, hyC⟩
        rw [hgl.2.2.1 y hyUC]
        rcases hgR_good y hyUC with h1 | h2 | ⟨hnebad, hprev⟩
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · right; right; refine ⟨hnebad, ?_⟩
          intro z hzU hfz
          have hzUC : z ∈ U \ C := Finset.mem_sdiff.2 ⟨hzU, fun hzC => hyC (hfz ▸ hCcl z hzC)⟩
          right; rw [hgl.2.2.1 z hzUC]; exact hprev z hzUC hfz
  · let q := L / 2
    have hqge2 : 2 ≤ q := by omega
    have hCle : L ≤ U.card := hCcard ▸ Finset.card_le_card hCsub
    have hodd_rest : (U \ C).card % 2 = 1 := by rw [Finset.card_sdiff_of_subset hCsub, hCcard]; omega
    have hinj' : ∀ u ∈ U \ C, ∀ v ∈ U \ C, f u = f v → u = v := fun u hu v hv =>
      hinj u (Finset.mem_sdiff.1 hu).1 v (Finset.mem_sdiff.1 hv).1
    rcases exists_odd_orbit hRcl hinj' hodd_rest with
      ⟨x', L', C', hx', hL'odd, hL'pos, hC'sub, hC'card, hmem', hsurj', hdist', hper', hC'cl, hR'cl⟩
    have hL'ge3 : 3 ≤ L' := by
      by_contra hlt; have h12 : L' = 1 ∨ L' = 2 := by omega
      rcases h12 with rfl | rfl
      · exact hno1 x' (Finset.mem_sdiff.1 hx').1 (by simpa using hper')
      · exact hno2 x' (Finset.mem_sdiff.1 hx').1 (by rw [iter_succ] at hper'; simpa using hper')
    have hex_v : ∃ v ∈ C', v ≠ bad := by
      by_cases h1 : x' ≠ bad
      · exact ⟨x', hmem' 0 hL'pos, h1⟩
      · exact ⟨f x', hmem' 1 (by omega), fun h2 => hno1 x' (Finset.mem_sdiff.1 hx').1 (h2.trans (not_ne_iff.1 h1).symm)⟩
    rcases hex_v with ⟨v, hvC', hvbad⟩
    rcases reanchor_orbit hRcl hinj' hC'sub hC'card hsurj' hper' hC'cl hvC' with
      ⟨hmemv, hsurjv, hdistv, hperv⟩
    have hf1_ne_f3 : f^[1] c ≠ f^[3] c := fun h => by have := hdist 1 (by omega) 3 (by omega) h; omega
    have hku : ∃ ku : ℕ, (ku = 1 ∨ ku = 3) ∧ f^[ku] c ≠ bad := by
      by_cases h1 : f^[1] c ≠ bad
      · exact ⟨1, Or.inl rfl, h1⟩
      · exact ⟨3, Or.inr rfl, fun h3 => hf1_ne_f3 ((not_ne_iff.1 h1).trans h3.symm)⟩
    rcases hku with ⟨ku, hku_val, hubad⟩
    let u := f^[ku] c
    have huC : u ∈ C := hmem ku (by omega)
    have huc : u ≠ c := fun h => by have := hdist ku (by omega) 0 hLpos (by simpa using h); omega
    have hspecL := pairSegment_spec (f := f) (x := c) (L := L) (a := 1)
      (t := if ku = 1 then 0 else 1) (by split_ifs <;> omega) hdist
    have hspecR := pairSegment_spec (f := f) (x := c) (L := L) (a := ku + 1)
      (t := if ku = 1 then q - 1 else q - 2) (by split_ifs <;> omega) hdist
    let segL := (Finset.range (2 * (if ku = 1 then 0 else 1))).image (fun d => f^[1 + d] c)
    let segR := (Finset.range (2 * (if ku = 1 then q - 1 else q - 2))).image (fun d => f^[ku + 1 + d] c)
    have hdLR : Disjoint segL segR := by
      rw [Finset.disjoint_left]; intro y hyL hyR
      rcases Finset.mem_image.1 hyL with ⟨d1, hd1, rfl⟩
      rcases Finset.mem_image.1 hyR with ⟨d2, hd2, heq⟩
      rw [Finset.mem_range] at hd1 hd2
      have := hdist (1 + d1) (by split_ifs at hd1 <;> omega) (ku + 1 + d2) (by split_ifs at hd2 <;> omega) heq.symm
      split_ifs at hd1 hd2 <;> omega
    have hglC := glue_involution hdLR hspecL.1 hspecL.2.1 hspecR.1 hspecR.2.1
    have hsegLR_eq : segL ∪ segR = (C.erase c).erase u := by
      ext y; simp only [Finset.mem_union, Finset.mem_erase, segL, segR, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro (⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩)
        · refine ⟨?_, ?_, hmem (1 + d) (by split_ifs at hd <;> omega)⟩
          · intro h; have := hdist (1 + d) (by split_ifs at hd <;> omega) ku (by omega) h; split_ifs at hd <;> omega
          · intro h; have := hdist (1 + d) (by split_ifs at hd <;> omega) 0 hLpos (by simpa using h); split_ifs at hd <;> omega
        · refine ⟨?_, ?_, hmem (ku + 1 + d) (by split_ifs at hd <;> omega)⟩
          · intro h; have := hdist (ku + 1 + d) (by split_ifs at hd <;> omega) ku (by omega) h; split_ifs at hd <;> omega
          · intro h; have := hdist (ku + 1 + d) (by split_ifs at hd <;> omega) 0 hLpos (by simpa using h); split_ifs at hd <;> omega
      · rintro ⟨hyu, hyc, hyC⟩; rcases hsurj y hyC with ⟨i, hi, rfl⟩
        have hi0 : i ≠ 0 := fun h => hyc (by simp [h])
        have hiku : i ≠ ku := fun h => hyu (by simp [u, h])
        rcases hku_val with rfl | rfl
        · right; exact ⟨i - 2, by simp; omega, by congr 1; omega⟩
        · by_cases hlt : i < 3
          · left; exact ⟨i - 1, by simp; omega, by congr 1; omega⟩
          · right; exact ⟨i - 4, by simp; omega, by congr 1; omega⟩
    let t' := L' / 2
    have hspecC' := pairSegment_spec (f := f) (x := v) (L := L') (a := 1) (t := t') (by omega) hdistv
    have hsegC' : (Finset.range (2 * t')).image (fun d => f^[1 + d] v) = C'.erase v := by
      ext y; simp only [Finset.mem_image, Finset.mem_range, Finset.mem_erase]
      constructor
      · rintro ⟨d, hd, rfl⟩
        refine ⟨?_, hmemv (1 + d) (by omega)⟩
        intro heq; have := hdistv (1 + d) (by omega) 0 hL'pos (by simpa using heq); omega
      · rintro ⟨hne, hyC'⟩; rcases hsurjv y hyC' with ⟨i, hi, rfl⟩
        have hi0 : i ≠ 0 := fun h => hne (by simp [h])
        exact ⟨i - 1, by omega, by congr 1; omega⟩
    have hCC'disj : Disjoint C C' := Finset.disjoint_of_subset_right hC'sub Finset.disjoint_sdiff
    have huv : u ≠ v := fun h => Finset.disjoint_left.1 hCC'disj huC (h ▸ hvC')
    have hd1 : Disjoint ({u, v} : Finset α) ((C.erase c).erase u) := by
      rw [Finset.disjoint_left]; intro y hy1 hy2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy1
      rcases hy1 with rfl | rfl
      · exact (Finset.mem_erase.1 hy2).1 rfl
      · exact Finset.disjoint_right.1 hCC'disj hvC' (Finset.mem_erase.1 (Finset.mem_erase.1 hy2).2).2
    have hgCsupp : ∀ y, y ∉ (C.erase c).erase u →
        glue segL (pairSegment f c 1 (if ku = 1 then 0 else 1)) (pairSegment f c (ku + 1) (if ku = 1 then q - 1 else q - 2)) y = y :=
      fun y hy => hglC.2.2.2 y (hsegLR_eq.symm ▸ hy)
    have hgl1 := glue_involution hd1 (swap2_inv u v) (swap2_supp u v) hglC.1 hgCsupp
    have hd2 : Disjoint ({u, v} ∪ (C.erase c).erase u) (C'.erase v) := by
      rw [Finset.disjoint_left]; intro y hy1 hy2; rw [Finset.mem_union] at hy1
      rcases hy1 with hyuv | hyCu
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hyuv
        rcases hyuv with rfl | rfl
        · exact Finset.disjoint_left.1 hCC'disj huC (Finset.mem_erase.1 hy2).2
        · exact (Finset.mem_erase.1 hy2).1 rfl
      · exact Finset.disjoint_left.1 hCC'disj (Finset.mem_erase.1 (Finset.mem_erase.1 hyCu).2).2 (Finset.mem_erase.1 hy2).2
    have hgC'supp : ∀ y, y ∉ C'.erase v → pairSegment f v 1 t' y = y := fun y hy => hspecC'.2.1 y (hsegC'.symm ▸ hy)
    have hgl2 := glue_involution hd2 hgl1.1 hgl1.2.2.2 hspecC'.1 hgC'supp
    have hunion_eq : ({u, v} ∪ (C.erase c).erase u) ∪ C'.erase v = (C ∪ C').erase c := by
      ext y; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
      constructor
      · rintro (((rfl | rfl) | ⟨_, hyc, hyC⟩) | ⟨_, hyC'⟩)
        · exact ⟨huc, Or.inl huC⟩
        · exact ⟨fun h => Finset.disjoint_right.1 hCC'disj hvC' (h ▸ hmem 0 hLpos), Or.inr hvC'⟩
        · exact ⟨hyc, Or.inl hyC⟩
        · exact ⟨fun h => Finset.disjoint_right.1 hCC'disj hyC' (h ▸ hmem 0 hLpos), Or.inr hyC'⟩
      · rintro ⟨hyc, hyC | hyC'⟩
        · by_cases hyu : y = u
          · exact Or.inl (Or.inl (Or.inl hyu))
          · exact Or.inl (Or.inr ⟨hyu, hyc, hyC⟩)
        · by_cases hyv : y = v
          · exact Or.inl (Or.inl (Or.inr hyv))
          · exact Or.inr ⟨hyv, hyC'⟩
    let U' := (U \ C) \ C'
    have hU'_eq : U' = U \ (C ∪ C') := by
      ext y; simp only [U', Finset.mem_sdiff, Finset.mem_union, not_or]; exact and_assoc
    have hCC'sub : C ∪ C' ⊆ U := Finset.union_subset hCsub (hC'sub.trans Finset.sdiff_subset)
    have hleCC' : L + L' ≤ U.card := by
      have := Finset.card_le_card hCC'sub
      rw [Finset.card_union_of_disjoint hCC'disj, hCcard, hC'card] at this; exact this
    have hU'even : U'.card % 2 = 0 := by
      rw [hU'_eq, Finset.card_sdiff_of_subset hCC'sub, Finset.card_union_of_disjoint hCC'disj, hCcard, hC'card]; omega
    have hU'inj : ∀ a ∈ U', ∀ b ∈ U', f a = f b → a = b := fun a ha b hb =>
      hinj a (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 ha).1).1
           b (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 hb).1).1
    rcases pair_even_invariant hR'cl hU'inj
        (fun a ha => hno1 a (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 ha).1).1)
        (fun a ha => hno2 a (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 ha).1).1)
        hU'even bad with ⟨gR, hgR_inv, hgR_supp, hgR_in, hgR_good⟩
    have hdisj_all : Disjoint ((C ∪ C').erase c) U' := by
      rw [hU'_eq]
      exact Finset.disjoint_of_subset_left (Finset.erase_subset _ _) Finset.disjoint_sdiff
    let g12 := glue ({u, v} ∪ (C.erase c).erase u) (glue ({u, v} : Finset α) (swap2 u v) (glue segL (pairSegment f c 1 (if ku = 1 then 0 else 1)) (pairSegment f c (ku + 1) (if ku = 1 then q - 1 else q - 2)))) (pairSegment f v 1 t')
    have hg12supp : ∀ y, y ∉ (C ∪ C').erase c → g12 y = y := fun y hy => hgl2.2.2.2 y (hunion_eq.symm ▸ hy)
    have hgl_all := glue_involution hdisj_all hgl2.1 hg12supp hgR_inv hgR_supp
    let g := glue ((C ∪ C').erase c) g12 gR
    have hunion_all : (C ∪ C').erase c ∪ U' = U.erase c := by
      ext y; simp only [Finset.mem_union, Finset.mem_erase, hU'_eq, Finset.mem_sdiff]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, hCC'sub (Finset.mem_union.2 h2)⟩
        · exact ⟨fun h => h2 (Or.inl (h ▸ hmem 0 hLpos)), h1⟩
      · rintro ⟨hyc, hyU⟩
        by_cases hyCC' : y ∈ C ∪ C'
        · exact Or.inl ⟨hyc, Finset.mem_union.1 hyCC'⟩
        · exact Or.inr ⟨hyU, fun h => hyCC' (Finset.mem_union.2 h)⟩
    have hg_u : g u = v := by
      show glue ((C ∪ C').erase c) g12 gR u = v
      rw [hgl_all.2.1 u (Finset.mem_erase.2 ⟨huc, Finset.mem_union_left _ huC⟩)]
      show glue ({u, v} ∪ (C.erase c).erase u) _ _ u = v
      rw [hgl2.2.1 u (Finset.mem_union_left _ (by simp)), hgl1.2.1 u (by simp), swap2_left]
    have hg_v : g v = u := by
      have hvc : v ≠ c := fun h => Finset.disjoint_right.1 hCC'disj hvC' (h ▸ hmem 0 hLpos)
      show glue ((C ∪ C').erase c) g12 gR v = u
      rw [hgl_all.2.1 v (Finset.mem_erase.2 ⟨hvc, Finset.mem_union_right _ hvC'⟩)]
      show glue ({u, v} ∪ (C.erase c).erase u) _ _ v = u
      rw [hgl2.2.1 v (Finset.mem_union_left _ (by simp)), hgl1.2.1 v (by simp), swap2_right]
    have hg_C : ∀ y ∈ (C.erase c).erase u, g y = glue segL (pairSegment f c 1 (if ku = 1 then 0 else 1)) (pairSegment f c (ku + 1) (if ku = 1 then q - 1 else q - 2)) y := by
      intro y hy
      have hy1 : y ∈ (C ∪ C').erase c := Finset.mem_erase.2
        ⟨(Finset.mem_erase.1 (Finset.mem_erase.1 hy).2).1,
         Finset.mem_union_left _ (Finset.mem_erase.1 (Finset.mem_erase.1 hy).2).2⟩
      show glue ((C ∪ C').erase c) g12 gR y = _
      rw [hgl_all.2.1 y hy1]
      show glue ({u, v} ∪ (C.erase c).erase u) _ _ y = _
      rw [hgl2.2.1 y (Finset.mem_union_right _ hy), hgl1.2.2.1 y hy]
    have hg_C' : ∀ y ∈ C'.erase v, g y = pairSegment f v 1 t' y := by
      intro y hy
      have hyc : y ≠ c := fun h => Finset.disjoint_right.1 hCC'disj (Finset.mem_erase.1 hy).2 (h ▸ hmem 0 hLpos)
      show glue ((C ∪ C').erase c) g12 gR y = _
      rw [hgl_all.2.1 y (Finset.mem_erase.2 ⟨hyc, Finset.mem_union_right _ (Finset.mem_erase.1 hy).2⟩)]
      show glue ({u, v} ∪ (C.erase c).erase u) _ _ y = _
      rw [hgl2.2.2.1 y hy]
    have hg_R : ∀ y ∈ U', g y = gR y := hgl_all.2.2.1
    refine ⟨g, hgl_all.1, fun y hy => hgl_all.2.2.2 y (hunion_all.symm ▸ hy), ?_, ?_⟩
    · intro y hy; rcases Finset.mem_erase.1 hy with ⟨hyc, hyU⟩
      by_cases hyu : y = u
      · rw [hyu, hg_u]
        have hvc : v ≠ c := fun h => Finset.disjoint_right.1 hCC'disj hvC' (h ▸ hmem 0 hLpos)
        exact ⟨Finset.mem_erase.2 ⟨hvc, (hC'sub.trans Finset.sdiff_subset) hvC'⟩, huv.symm⟩
      by_cases hyv : y = v
      · rw [hyv, hg_v]; exact ⟨Finset.mem_erase.2 ⟨huc, hCsub huC⟩, huv⟩
      by_cases hyC : y ∈ C
      · have hyCu : y ∈ (C.erase c).erase u := Finset.mem_erase.2 ⟨hyu, Finset.mem_erase.2 ⟨hyc, hyC⟩⟩
        rw [hg_C y hyCu]
        have hyLR : y ∈ segL ∪ segR := hsegLR_eq.symm ▸ hyCu
        rw [Finset.mem_union] at hyLR
        rcases hyLR with hyL | hyR
        · rw [hglC.2.1 y hyL]
          rcases Finset.mem_image.1 hyL with ⟨d, hd, rfl⟩; rw [Finset.mem_range] at hd
          have hdiv : d = 2 * (d / 2) ∨ d = 2 * (d / 2) + 1 := by omega
          rcases hdiv with h | h
          · have hv := (hspecL.2.2 (d / 2) (by omega)).1; have hidx : 1 + d = 1 + 2 * (d / 2) := by omega
            rw [hidx, hv]
            refine ⟨Finset.mem_erase.2 ⟨?_, hCsub (hmem _ (by split_ifs at hd <;> omega))⟩, ?_⟩
            · intro heq; have := hdist (1 + 2 * (d / 2) + 1) (by split_ifs at hd <;> omega) 0 hLpos (by simpa using heq); omega
            · intro heq; have := hdist (1 + 2 * (d / 2) + 1) (by split_ifs at hd <;> omega) (1 + 2 * (d / 2)) (by split_ifs at hd <;> omega) heq; omega
          · have hv := (hspecL.2.2 (d / 2) (by omega)).2; have hidx : 1 + d = 1 + 2 * (d / 2) + 1 := by omega
            rw [hidx, hv]
            refine ⟨Finset.mem_erase.2 ⟨?_, hCsub (hmem _ (by split_ifs at hd <;> omega))⟩, ?_⟩
            · intro heq; have := hdist (1 + 2 * (d / 2)) (by split_ifs at hd <;> omega) 0 hLpos (by simpa using heq); omega
            · intro heq; have := hdist (1 + 2 * (d / 2)) (by split_ifs at hd <;> omega) (1 + 2 * (d / 2) + 1) (by split_ifs at hd <;> omega) heq; omega
        · rw [hglC.2.2.1 y hyR]
          rcases Finset.mem_image.1 hyR with ⟨d, hd, rfl⟩; rw [Finset.mem_range] at hd
          have hdiv : d = 2 * (d / 2) ∨ d = 2 * (d / 2) + 1 := by omega
          rcases hdiv with h | h
          · have hv := (hspecR.2.2 (d / 2) (by omega)).1; have hidx : ku + 1 + d = ku + 1 + 2 * (d / 2) := by omega
            rw [hidx, hv]
            refine ⟨Finset.mem_erase.2 ⟨?_, hCsub (hmem _ (by split_ifs at hd <;> omega))⟩, ?_⟩
            · intro heq; have := hdist (ku + 1 + 2 * (d / 2) + 1) (by split_ifs at hd <;> omega) 0 hLpos (by simpa using heq); omega
            · intro heq; have := hdist (ku + 1 + 2 * (d / 2) + 1) (by split_ifs at hd <;> omega) (ku + 1 + 2 * (d / 2)) (by split_ifs at hd <;> omega) heq; omega
          · have hv := (hspecR.2.2 (d / 2) (by omega)).2; have hidx : ku + 1 + d = ku + 1 + 2 * (d / 2) + 1 := by omega
            rw [hidx, hv]
            refine ⟨Finset.mem_erase.2 ⟨?_, hCsub (hmem _ (by split_ifs at hd <;> omega))⟩, ?_⟩
            · intro heq; have := hdist (ku + 1 + 2 * (d / 2)) (by split_ifs at hd <;> omega) 0 hLpos (by simpa using heq); omega
            · intro heq; have := hdist (ku + 1 + 2 * (d / 2)) (by split_ifs at hd <;> omega) (ku + 1 + 2 * (d / 2) + 1) (by split_ifs at hd <;> omega) heq; omega
      by_cases hyC' : y ∈ C'
      · have hyC'v : y ∈ C'.erase v := Finset.mem_erase.2 ⟨hyv, hyC'⟩
        rw [hg_C' y hyC'v]; rcases hsurjv y hyC' with ⟨i, hi, rfl⟩
        have hi0 : i ≠ 0 := fun h => hyv (by simp [h])
        have hdiv : i - 1 = 2 * ((i - 1) / 2) ∨ i - 1 = 2 * ((i - 1) / 2) + 1 := by omega
        rcases hdiv with h | h
        · have hi_eq : i = 1 + 2 * ((i - 1) / 2) := by omega
          have hv := (hspecC'.2.2 ((i - 1) / 2) (by omega)).1; rw [hi_eq, hv]
          have hm := hmemv (1 + 2 * ((i - 1) / 2) + 1) (by omega)
          refine ⟨Finset.mem_erase.2 ⟨fun heq => Finset.disjoint_right.1 hCC'disj hm (heq ▸ hmem 0 hLpos),
            (hC'sub.trans Finset.sdiff_subset) hm⟩, ?_⟩
          intro heq; have := hdistv (1 + 2 * ((i - 1) / 2) + 1) (by omega) (1 + 2 * ((i - 1) / 2)) (by omega) heq; omega
        · have hi_eq : i = 1 + 2 * ((i - 1) / 2) + 1 := by omega
          have hv := (hspecC'.2.2 ((i - 1) / 2) (by omega)).2; rw [hi_eq, hv]
          have hm := hmemv (1 + 2 * ((i - 1) / 2)) (by omega)
          refine ⟨Finset.mem_erase.2 ⟨fun heq => Finset.disjoint_right.1 hCC'disj hm (heq ▸ hmem 0 hLpos),
            (hC'sub.trans Finset.sdiff_subset) hm⟩, ?_⟩
          intro heq; have := hdistv (1 + 2 * ((i - 1) / 2)) (by omega) (1 + 2 * ((i - 1) / 2) + 1) (by omega) heq; omega
      · have hyU' : y ∈ U' := by rw [hU'_eq]; exact Finset.mem_sdiff.2 ⟨hyU, by simp [hyC, hyC']⟩
        rw [hg_R y hyU']
        have hgy := hgR_in y hyU'
        have hgyU : gR y ∈ U := (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 hgy.1).1).1
        have hgyc : gR y ≠ c := fun h =>
          (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 hgy.1).1).2 (h ▸ hmem 0 hLpos)
        exact ⟨Finset.mem_erase.2 ⟨hgyc, hgyU⟩, hgy.2⟩
    · intro y hy; rcases Finset.mem_erase.1 hy with ⟨hyc, hyU⟩
      by_cases hyu : y = u
      · rw [hyu]; right; right; refine ⟨hubad, ?_⟩
        intro z hzU hfz
        rcases hku_val with rfl | rfl
        · left; exact hinj z hzU c hc (by simpa [u] using hfz)
        · right
          have hprev_eq : f (f^[2] c) = u := by rw [← iter_succ f 2 c]
          have hz_eq : z = f^[2] c := hinj z hzU _ (hCsub (hmem 2 (by omega))) (hfz.trans hprev_eq.symm)
          rw [hz_eq]
          have hzCu : f^[2] c ∈ (C.erase c).erase u := Finset.mem_erase.2 ⟨
            fun h => by have := hdist 2 (by omega) 3 (by omega) h; omega,
            Finset.mem_erase.2 ⟨fun h => by have := hdist 2 (by omega) 0 hLpos (by simpa using h); omega,
              hmem 2 (by omega)⟩⟩
          rw [hg_C _ hzCu]
          have hzL : f^[2] c ∈ segL := Finset.mem_image.2 ⟨1, by simp, rfl⟩
          rw [hglC.2.1 _ hzL]
          have hv := (hspecL.2.2 0 (by simp)).2
          change f (pairSegment f c 1 (if 3 = 1 then 0 else 1) (f^[1 + 2 * 0 + 1] c)) = f^[1 + 2 * 0 + 1] c
          rw [hv, ← iter_succ f 1 c]
      by_cases hyv : y = v
      · rw [hyv]; right; right; refine ⟨hvbad, ?_⟩
        intro z hzU hfz; right
        have hprev_eq : f (f^[2 * t'] v) = v := by
          rw [← iter_succ f (2 * t') v]
          have h1 : 2 * t' + 1 = L' := by omega
          rw [h1, hperv]
        have hz_eq : z = f^[2 * t'] v := hinj z hzU _ ((hC'sub.trans Finset.sdiff_subset) (hmemv (2 * t') (by omega))) (hfz.trans hprev_eq.symm)
        rw [hz_eq]
        have hzC'v : f^[2 * t'] v ∈ C'.erase v := Finset.mem_erase.2 ⟨by
          intro h; have := hdistv (2 * t') (by omega) 0 hL'pos (by simpa using h); omega,
          hmemv (2 * t') (by omega)⟩
        rw [hg_C' _ hzC'v]
        have hidx : 2 * t' = 1 + 2 * (t' - 1) + 1 := by omega
        have hv := (hspecC'.2.2 (t' - 1) (by omega)).2
        rw [hidx, hv, ← iter_succ f (1 + 2 * (t' - 1)) v]
      by_cases hyC : y ∈ C
      · have hyCu : y ∈ (C.erase c).erase u := Finset.mem_erase.2 ⟨hyu, Finset.mem_erase.2 ⟨hyc, hyC⟩⟩
        rw [hg_C y hyCu]
        have hyLR : y ∈ segL ∪ segR := hsegLR_eq.symm ▸ hyCu
        rw [Finset.mem_union] at hyLR
        rcases hyLR with hyL | hyR
        · rw [hglC.2.1 y hyL]
          rcases Finset.mem_image.1 hyL with ⟨d, hd, rfl⟩; rw [Finset.mem_range] at hd
          have hdiv : d = 2 * (d / 2) ∨ d = 2 * (d / 2) + 1 := by omega
          rcases hdiv with h | h
          · left; have hidx : 1 + d = 1 + 2 * (d / 2) := by omega
            have hv := (hspecL.2.2 (d / 2) (by omega)).1; rw [hidx, hv, iter_succ]
          · right; left; have hidx : 1 + d = 1 + 2 * (d / 2) + 1 := by omega
            have hv := (hspecL.2.2 (d / 2) (by omega)).2; rw [hidx, hv, ← iter_succ f (1 + 2 * (d / 2)) c]
        · rw [hglC.2.2.1 y hyR]
          rcases Finset.mem_image.1 hyR with ⟨d, hd, rfl⟩; rw [Finset.mem_range] at hd
          have hdiv : d = 2 * (d / 2) ∨ d = 2 * (d / 2) + 1 := by omega
          rcases hdiv with h | h
          · left; have hidx : ku + 1 + d = ku + 1 + 2 * (d / 2) := by omega
            have hv := (hspecR.2.2 (d / 2) (by omega)).1; rw [hidx, hv, iter_succ]
          · right; left; have hidx : ku + 1 + d = ku + 1 + 2 * (d / 2) + 1 := by omega
            have hv := (hspecR.2.2 (d / 2) (by omega)).2; rw [hidx, hv, ← iter_succ f (ku + 1 + 2 * (d / 2)) c]
      by_cases hyC' : y ∈ C'
      · have hyC'v : y ∈ C'.erase v := Finset.mem_erase.2 ⟨hyv, hyC'⟩
        rw [hg_C' y hyC'v]; rcases hsurjv y hyC' with ⟨i, hi, rfl⟩
        have hi0 : i ≠ 0 := fun h => hyv (by simp [h])
        have hdiv : i - 1 = 2 * ((i - 1) / 2) ∨ i - 1 = 2 * ((i - 1) / 2) + 1 := by omega
        rcases hdiv with h | h
        · left; have hi_eq : i = 1 + 2 * ((i - 1) / 2) := by omega
          have hv := (hspecC'.2.2 ((i - 1) / 2) (by omega)).1; rw [hi_eq, hv, iter_succ]
        · right; left; have hi_eq : i = 1 + 2 * ((i - 1) / 2) + 1 := by omega
          have hv := (hspecC'.2.2 ((i - 1) / 2) (by omega)).2; rw [hi_eq, hv, ← iter_succ f (1 + 2 * ((i - 1) / 2)) v]
      · have hyU' : y ∈ U' := by rw [hU'_eq]; exact Finset.mem_sdiff.2 ⟨hyU, by simp [hyC, hyC']⟩
        rw [hg_R y hyU']
        rcases hgR_good y hyU' with h1 | h2 | ⟨hnebad, hprev⟩
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · right; right; refine ⟨hnebad, ?_⟩
          intro z hzU hfz
          have hznotC : z ∉ C := fun hzC => hyC (hfz ▸ hCcl z hzC)
          have hznotC' : z ∉ C' := fun hzC' => hyC' (hfz ▸ hC'cl z hzC')
          have hzU' : z ∈ U' := by rw [hU'_eq]; exact Finset.mem_sdiff.2 ⟨hzU, by simp [hznotC, hznotC']⟩
          right; rw [hg_R z hzU']; exact hprev z hzU' hfz

end OrbitPairing

section CounterexampleCtx

/-- A hypothetical counterexample on `2*k + 1` agents (`k ≥ 3`) together with a maximum matching `M` of `H_k`. -/
private structure Ctx (k : ℕ) where
  hk : 3 ≤ k
  p : CompleteProfile (2 * k + 1)
  hblk : ∀ μ : Matching (Fin (2 * k + 1)), ∃ i j, IsKBlockingPair ⊤ p.partnerRank k μ i j
  M : Matching (Fin (2 * k + 1))
  hM_hm : ∀ i, M.val i = i ∨ (i ≠ M.val i ∧ p.partnerRank i (M.val i) ≤ k ∧ p.partnerRank (M.val i) i ≤ k)
  hM_max : ∀ μ : Matching (Fin (2 * k + 1)),
    (∀ i, μ.val i = i ∨ (i ≠ μ.val i ∧ p.partnerRank i (μ.val i) ≤ k ∧ p.partnerRank (μ.val i) i ≤ k)) →
    (Finset.univ.filter (fun i => μ.val i ≠ i)).card ≤ (Finset.univ.filter (fun i => M.val i ≠ i)).card

namespace Ctx

variable {k : ℕ} (C : Ctx k)

private abbrev Hadj (i j : Fin (2 * k + 1)) : Prop :=
  i ≠ j ∧ C.p.partnerRank i j ≤ k ∧ C.p.partnerRank j i ≤ k

private lemma Hadj_symm {i j} (h : C.Hadj i j) : C.Hadj j i := ⟨h.1.symm, h.2.2, h.2.1⟩

private def V : Finset (Fin (2 * k + 1)) := Finset.univ.filter (fun i => C.M.val i ≠ i)
private def U : Finset (Fin (2 * k + 1)) := Finset.univ \ C.V

private lemma M_in_V {v} (hv : v ∈ C.V) :
    C.M.val v ∈ C.V ∧ C.M.val v ≠ v ∧ C.Hadj v (C.M.val v) := by
  have hvne : C.M.val v ≠ v := (Finset.mem_filter.1 hv).2
  have hMvne : C.M.val (C.M.val v) ≠ C.M.val v := by rw [C.M.property v]; exact hvne.symm
  have hadj : C.Hadj v (C.M.val v) := (C.hM_hm v).resolve_left hvne
  exact ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hMvne⟩, hvne, hadj⟩

private lemma U_fix {x} (hx : x ∈ C.U) : C.M.val x = x := by
  have hnotV : x ∉ C.V := (Finset.mem_sdiff.1 hx).2
  simp only [V, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hnotV
  exact hnotV

private lemma mem_V_or_U (x : Fin (2 * k + 1)) : x ∈ C.V ∨ x ∈ C.U := by
  by_cases h : x ∈ C.V
  · exact Or.inl h
  · exact Or.inr (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, h⟩)

private lemma VU_disj : Disjoint C.V C.U := Finset.disjoint_sdiff

private lemma VU_card : C.V.card + C.U.card = 2 * k + 1 := by
  have h1 : C.V ∪ C.U = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have h2 := Finset.card_union_of_disjoint C.VU_disj
  rw [h1, Finset.card_univ, Fintype.card_fin] at h2
  exact h2.symm

private lemma V_even : C.V.card % 2 = 0 :=
  card_even_of_fpf_involutive C.M.property (fun _ hv => ⟨(C.M_in_V hv).1, (C.M_in_V hv).2.1⟩)

private lemma U_odd : C.U.card % 2 = 1 := by
  have := C.VU_card; have := C.V_even; omega

private lemma U_ge3 : 3 ≤ C.U.card := by
  by_contra hlt
  have hU1 : C.U.card ≤ 1 := by have := C.U_odd; omega
  rcases C.hblk C.M with ⟨i, j, hij⟩
  have hiU : i ∈ C.U := by
    rcases C.mem_V_or_U i with h | h
    · exact False.elim (not_kBlocking_of_immune C.p k C.M (C.M_in_V h).2.2.2.1 hij)
    · exact h
  have hjU : j ∈ C.U := by
    rcases C.mem_V_or_U j with h | h
    · exact False.elim (not_kBlocking_of_immune C.p k C.M (C.M_in_V h).2.2.2.1 (isKBlockingPair_symm C.p k C.M hij))
    · exact h
  exact hij.1.ne (Finset.card_le_one.1 hU1 i hiU j hjU)

private lemma no_H_U {x y} (hx : x ∈ C.U) (hy : y ∈ C.U) : ¬ C.Hadj x y := by
  intro hxy
  have hd : Disjoint ({x, y} : Finset _) C.V := by
    rw [Finset.disjoint_left]; intro z hz1 hz2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz1
    rcases hz1 with rfl | rfl
    · exact Finset.disjoint_right.1 C.VU_disj hx hz2
    · exact Finset.disjoint_right.1 C.VU_disj hy hz2
  have hMsupp : ∀ z, z ∉ C.V → C.M.val z = z := fun z hz => C.U_fix (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hz⟩)
  have hgl := glue_involution hd (swap2_inv x y) (swap2_supp x y) C.M.property hMsupp
  let g := glue ({x, y} : Finset _) (swap2 x y) C.M.val
  let M' := mkMatching g hgl.1
  have hM'hm : ∀ z, M'.val z = z ∨ C.Hadj z (M'.val z) := by
    intro z; change glue ({x, y} : Finset _) (swap2 x y) C.M.val z = z ∨
      C.Hadj z (glue ({x, y} : Finset _) (swap2 x y) C.M.val z)
    by_cases hzx : z = x
    · rw [hzx, hgl.2.1 x (by simp), swap2_left]; exact Or.inr hxy
    by_cases hzy : z = y
    · rw [hzy, hgl.2.1 y (by simp), swap2_right]; exact Or.inr (C.Hadj_symm hxy)
    · have hznot : z ∉ ({x, y} : Finset _) := by simp [hzx, hzy]
      have hgz : glue ({x, y} : Finset _) (swap2 x y) C.M.val z = C.M.val z := by simp [glue, hznot]
      rw [hgz]; exact C.hM_hm z
  have hsub : insert x (insert y C.V) ⊆ Finset.univ.filter (fun z => M'.val z ≠ z) := by
    intro z hz; refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    change glue ({x, y} : Finset _) (swap2 x y) C.M.val z ≠ z
    simp only [Finset.mem_insert] at hz
    rcases hz with rfl | rfl | hzV
    · rw [hgl.2.1 z (by simp), swap2_left]; exact hxy.1.symm
    · rw [hgl.2.1 z (by simp), swap2_right]; exact hxy.1
    · rw [hgl.2.2.1 z hzV]; exact (C.M_in_V hzV).2.1
  have h1 : y ∉ C.V := (Finset.mem_sdiff.1 hy).2
  have h2 : x ∉ insert y C.V := by simp [hxy.1, (Finset.mem_sdiff.1 hx).2]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h1] at hcard
  have hmax := C.hM_max M' hM'hm
  change _ ≤ C.V.card at hmax
  omega

private noncomputable def f (x : Fin (2 * k + 1)) : Fin (2 * k + 1) :=
  Classical.choose (exists_unique_partnerRank C.p x (k + 1) (by omega) (by have := C.hk; omega))

private lemma f_rank (x : Fin (2 * k + 1)) : C.p.partnerRank x (C.f x) = k + 1 :=
  (Classical.choose_spec (exists_unique_partnerRank C.p x (k + 1) (by omega) (by have := C.hk; omega))).1

private lemma f_uniq (x y : Fin (2 * k + 1)) (h : C.p.partnerRank x y = k + 1) : y = C.f x :=
  (Classical.choose_spec (exists_unique_partnerRank C.p x (k + 1) (by omega) (by have := C.hk; omega))).2 y h

private lemma T0_obstruct {s} (hs : s ∈ C.U) {gU : Fin (2 * k + 1) → Fin (2 * k + 1)}
    (hgUinv : Function.Involutive gU) (hgUsupp : ∀ x, x ∉ C.U.erase s → gU x = x)
    (hgUin : ∀ x ∈ C.U.erase s, gU x ∈ C.U.erase s ∧ gU x ≠ x) :
    C.f s ∈ C.U.erase s ∧ C.p.partnerRank (C.f s) s + k ≤ C.p.partnerRank (C.f s) (gU (C.f s)) := by
  have hdisj : Disjoint C.V (C.U.erase s) := Finset.disjoint_of_subset_right (Finset.erase_subset _ _) C.VU_disj
  have hMsupp : ∀ x, x ∉ C.V → C.M.val x = x := fun x hx => C.U_fix (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hx⟩)
  have hgl := glue_involution hdisj C.M.property hMsupp hgUinv hgUsupp
  let μ := mkMatching (glue C.V C.M.val gU) hgl.1
  rcases C.hblk μ with ⟨i, j, hij⟩
  have hiU : i ∈ C.U := by
    rcases C.mem_V_or_U i with h | h
    · exact False.elim (not_kBlocking_of_immune C.p k μ (by change C.p.partnerRank i (glue C.V C.M.val gU i) ≤ k; rw [hgl.2.1 i h]; exact (C.M_in_V h).2.2.2.1) hij)
    · exact h
  have hjU : j ∈ C.U := by
    rcases C.mem_V_or_U j with h | h
    · exact False.elim (not_kBlocking_of_immune C.p k μ (by change C.p.partnerRank j (glue C.V C.M.val gU j) ≤ k; rw [hgl.2.1 j h]; exact (C.M_in_V h).2.2.2.1) (isKBlockingPair_symm C.p k μ hij))
    · exact h
  have hnot_both : ¬ (i ∈ C.U.erase s ∧ j ∈ C.U.erase s) := by
    rintro ⟨hi', hj'⟩
    have hmi : μ.val i = gU i := hgl.2.2.1 i hi'
    have hmj : μ.val j = gU j := hgl.2.2.1 j hj'
    have hri : C.p.partnerRank i (μ.val i) ≤ 2 * k := by have := partnerRank_lt_of_ne C.p (hmi ▸ (hgUin i hi').2); omega
    have hrj : C.p.partnerRank j (μ.val j) ≤ 2 * k := by have := partnerRank_lt_of_ne C.p (hmj ▸ (hgUin j hj').2); omega
    rcases hij with ⟨hadj, _, h1, h2⟩
    exact C.no_H_U hiU hjU ⟨hadj.ne, by omega, by omega⟩
  have hfrom : ∀ y ∈ C.U.erase s, IsKBlockingPair ⊤ C.p.partnerRank k μ s y →
      C.f s ∈ C.U.erase s ∧ C.p.partnerRank (C.f s) s + k ≤ C.p.partnerRank (C.f s) (gU (C.f s)) := by
    intro y hy hsy
    have hms : μ.val s = s := hgl.2.2.2 s (by
      simp only [Finset.mem_union, Finset.mem_erase, not_or]
      exact ⟨Finset.disjoint_right.1 C.VU_disj hs, fun h => h.1 rfl⟩)
    have hmy : μ.val y = gU y := hgl.2.2.1 y hy
    have hry : C.p.partnerRank y (gU y) ≤ 2 * k := by have := partnerRank_lt_of_ne C.p (hgUin y hy).2; omega
    rcases hsy with ⟨hadj, _, h1, h2⟩
    rw [hms, C.p.partnerRank_self s] at h1
    rw [hmy] at h2
    have hry_le : C.p.partnerRank y s ≤ k := by omega
    have hrs_ge : k + 1 ≤ C.p.partnerRank s y := by
      by_contra hlt; exact C.no_H_U hs (Finset.mem_erase.1 hy).2 ⟨hadj.ne, by omega, hry_le⟩
    have hy_eq : y = C.f s := C.f_uniq s y (by omega)
    rw [hy_eq] at hy h2; exact ⟨hy, h2⟩
  by_cases his : i = s
  · rw [his] at hij; exact hfrom j (Finset.mem_erase.2 ⟨hij.1.ne.symm, hjU⟩) hij
  · by_cases hjs : j = s
    · rw [hjs] at hij; exact hfrom i (Finset.mem_erase.2 ⟨his, hiU⟩) (isKBlockingPair_symm C.p k μ hij)
    · exact False.elim (hnot_both ⟨Finset.mem_erase.2 ⟨his, hiU⟩, Finset.mem_erase.2 ⟨hjs, hjU⟩⟩)

private lemma f_mem_U {s} (hs : s ∈ C.U) : C.f s ∈ C.U ∧ C.f s ≠ s := by
  have heven : (C.U.erase s).card % 2 = 0 := by have := Finset.card_erase_add_one hs; have := C.U_odd; omega
  rcases exists_fpf_involutive_of_even heven with ⟨gU, hgUinv, hgUsupp, hgUin⟩
  have h := (C.T0_obstruct hs hgUinv hgUsupp hgUin).1
  exact ⟨(Finset.mem_erase.1 h).2, (Finset.mem_erase.1 h).1⟩

private lemma f_step {s z} (hs : s ∈ C.U) (hz : z ∈ C.U) (hzs : z ≠ s) (hzf : z ≠ C.f s) :
    C.p.partnerRank (C.f s) s + k ≤ C.p.partnerRank (C.f s) z := by
  let U' := ((C.U.erase s).erase (C.f s)).erase z
  have hfmem : C.f s ∈ C.U.erase s := Finset.mem_erase.2 ⟨(C.f_mem_U hs).2, (C.f_mem_U hs).1⟩
  have hzmem : z ∈ (C.U.erase s).erase (C.f s) := Finset.mem_erase.2 ⟨hzf, Finset.mem_erase.2 ⟨hzs, hz⟩⟩
  have hcard : U'.card + 3 = C.U.card := by
    have h1 : (C.U.erase s).card + 1 = C.U.card := Finset.card_erase_add_one hs
    have h2 : ((C.U.erase s).erase (C.f s)).card + 1 = (C.U.erase s).card := Finset.card_erase_add_one hfmem
    have h3 : U'.card + 1 = ((C.U.erase s).erase (C.f s)).card := Finset.card_erase_add_one hzmem
    omega
  have heven' : U'.card % 2 = 0 := by have := C.U_odd; omega
  rcases exists_fpf_involutive_of_even heven' with ⟨g', hg'inv, hg'supp, hg'in⟩
  have hd : Disjoint ({C.f s, z} : Finset _) U' := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx1
    rcases hx1 with rfl | rfl
    · exact (Finset.mem_erase.1 (Finset.mem_erase.1 hx2).2).1 rfl
    · exact (Finset.mem_erase.1 hx2).1 rfl
  have hgl := glue_involution hd (swap2_inv (C.f s) z) (swap2_supp (C.f s) z) hg'inv hg'supp
  have hunion : ({C.f s, z} : Finset _) ∪ U' = C.U.erase s := by
    ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase, U']
    constructor
    · rintro ((rfl | rfl) | ⟨_, _, hxs, hxU⟩)
      · exact ⟨(C.f_mem_U hs).2, (C.f_mem_U hs).1⟩
      · exact ⟨hzs, hz⟩
      · exact ⟨hxs, hxU⟩
    · rintro ⟨hxs, hxU⟩
      by_cases hx1 : x = C.f s; · exact Or.inl (Or.inl hx1)
      by_cases hx2 : x = z; · exact Or.inl (Or.inr hx2)
      · exact Or.inr ⟨hx2, hx1, hxs, hxU⟩
  have hgUin : ∀ x ∈ C.U.erase s, glue ({C.f s, z} : Finset _) (swap2 (C.f s) z) g' x ∈ C.U.erase s ∧
      glue ({C.f s, z} : Finset _) (swap2 (C.f s) z) g' x ≠ x := by
    intro x hx
    by_cases hx1 : x = C.f s
    · rw [hx1, hgl.2.1 (C.f s) (by simp), swap2_left]; exact ⟨Finset.mem_erase.2 ⟨hzs, hz⟩, hzf⟩
    by_cases hx2 : x = z
    · rw [hx2, hgl.2.1 z (by simp), swap2_right]; exact ⟨hfmem, hzf.symm⟩
    · have hxU' : x ∈ U' := Finset.mem_erase.2 ⟨hx2, Finset.mem_erase.2 ⟨hx1, hx⟩⟩
      rw [hgl.2.2.1 x hxU']
      have h := hg'in x hxU'
      exact ⟨(Finset.mem_erase.1 (Finset.mem_erase.1 h.1).2).2, h.2⟩
  have hres := (C.T0_obstruct hs hgl.1 (fun x hx => hgl.2.2.2 x (hunion.symm ▸ hx)) hgUin).2
  have hgf : glue ({C.f s, z} : Finset _) (swap2 (C.f s) z) g' (C.f s) = z := by
    rw [hgl.2.1 (C.f s) (by simp), swap2_left]
  rwa [hgf] at hres

private lemma f_no2 {s} (hs : s ∈ C.U) : C.f (C.f s) ≠ s := by
  intro heq
  have hcard_rem : ((C.U.erase s).erase (C.f s)).card = C.U.card - 2 := by
    have h1 := Finset.card_erase_add_one hs
    have h2 := Finset.card_erase_add_one (Finset.mem_erase.2 ⟨(C.f_mem_U hs).2, (C.f_mem_U hs).1⟩)
    omega
  have hge3 := C.U_ge3
  rcases Finset.card_pos.1 (show 0 < ((C.U.erase s).erase (C.f s)).card by omega) with ⟨z, hz⟩
  have hzf : z ≠ C.f s := (Finset.mem_erase.1 hz).1
  have hzs : z ≠ s := (Finset.mem_erase.1 (Finset.mem_erase.1 hz).2).1
  have hzU : z ∈ C.U := (Finset.mem_erase.1 (Finset.mem_erase.1 hz).2).2
  have h1 := C.f_step hs hzU hzs hzf
  have h2 : C.p.partnerRank (C.f s) s = k + 1 := by have := C.f_rank (C.f s); rwa [heq] at this
  have h3 : C.p.partnerRank (C.f s) z ≤ 2 * k := by have := partnerRank_lt_of_ne C.p hzf; omega
  omega

private lemma f_rank1 {s} (hs : s ∈ C.U) : C.p.partnerRank (C.f s) s = 1 := by
  have h1 := C.f_step hs (C.f_mem_U (C.f_mem_U hs).1).1 (C.f_no2 hs) (C.f_mem_U (C.f_mem_U hs).1).2
  rw [C.f_rank (C.f s)] at h1
  have hpos := partnerRank_pos C.p (C.f s) s
  omega

private lemma f_inj {x y} (hx : x ∈ C.U) (hy : y ∈ C.U) (h : C.f x = C.f y) : x = y := by
  have h1 := C.f_rank1 hx; have h2 := C.f_rank1 hy; rw [← h] at h2
  exact partnerRank_inj C.p (C.f x) (h1.trans h2.symm)

private lemma f_surj {y} (hy : y ∈ C.U) : ∃ x ∈ C.U, C.f x = y := by
  have hsub : C.U.image C.f ⊆ C.U := by
    intro z hz; rcases Finset.mem_image.1 hz with ⟨x, hx, rfl⟩; exact (C.f_mem_U hx).1
  have hcard : (C.U.image C.f).card = C.U.card := Finset.card_image_of_injOn (fun x hx y hy => C.f_inj hx hy)
  have heq : C.U.image C.f = C.U := Finset.eq_of_subset_of_card_le hsub (by omega)
  rw [← heq] at hy; exact Finset.mem_image.1 hy

private lemma f_other_ge {x z} (hx : x ∈ C.U) (hz : z ∈ C.U) (hne : C.f z ≠ x) :
    k + 1 ≤ C.p.partnerRank x z := by
  by_cases hzx : z = x
  · rw [hzx, C.p.partnerRank_self x]; omega
  · rcases C.f_surj hx with ⟨s, hs, rfl⟩
    have hzs : z ≠ s := fun h => hne (by rw [h])
    have h1 := C.f_step hs hz hzs hzx
    rw [C.f_rank1 hs] at h1; omega

private lemma V_ge_k_sub_1 : k - 1 ≤ C.V.card := by
  have hge3 := C.U_ge3
  rcases Finset.card_pos.1 (show 0 < C.U.card by omega) with ⟨x, hx⟩
  rcases C.f_surj hx with ⟨s, hs, hfs⟩
  let topK := Finset.univ.filter (fun z => C.p.partnerRank x z ≤ k)
  have htopK_card : topK.card = k := card_partnerRank_le C.p x k (by omega)
  have hsub : topK.erase s ⊆ C.V := by
    intro z hz; rcases Finset.mem_erase.1 hz with ⟨hzs, hztop⟩
    have hrz : C.p.partnerRank x z ≤ k := (Finset.mem_filter.1 hztop).2
    rcases C.mem_V_or_U z with hzV | hzU
    · exact hzV
    · have hfz : C.f z ≠ x := fun h => hzs (C.f_inj hzU hs (h.trans hfs.symm))
      have := C.f_other_ge hx hzU hfz; omega
  have hle := Finset.card_le_card hsub
  have hcard_er : topK.card - 1 ≤ (topK.erase s).card := Finset.pred_card_le_card_erase
  omega

/-- Unified U-cleanup lemma (Theorem 0 + Lemma 2 engine). -/
private lemma U_cleanup {c s : Fin (2 * k + 1)} (hc : c ∈ C.U) (hs : s ∈ C.V)
    {μV : Fin (2 * k + 1) → Fin (2 * k + 1)}
    (hμVinv : Function.Involutive μV)
    (hμVsupp : ∀ x, x ∉ insert c C.V → μV x = x)
    (hμVs : μV s = s) (hμVc : μV c ∈ C.V)
    (hμVw : ∀ w ∈ C.V.erase s, μV w ∈ insert c C.V ∧ μV w ≠ w)
    (hclean_w : ∀ w ∈ C.V.erase s, C.p.partnerRank w (μV w) ≤ k ∨ ∀ x ∈ C.U.erase c, ¬ C.Hadj w x)
    (hclean_s : ∀ x ∈ C.U.erase c, ¬ C.Hadj s x) :
    ∃ i ∈ insert c C.V, ∃ j ∈ insert c C.V,
      i ≠ j ∧ μV i ≠ j ∧
      C.p.partnerRank i j + k ≤ C.p.partnerRank i (μV i) ∧
      C.p.partnerRank j i + k ≤ C.p.partnerRank j (μV j) := by
  rcases pair_odd_punctured (fun _ hx => (C.f_mem_U hx).1) (fun _ hx _ hy => C.f_inj hx hy)
      (fun _ hx => (C.f_mem_U hx).2) (fun _ hx => C.f_no2 hx) C.U_odd hc (C.f s) with
    ⟨gU, hgUinv, hgUsupp, hgUin, hgUgood⟩
  have hdisj : Disjoint (insert c C.V) (C.U.erase c) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    rcases Finset.mem_insert.1 hx1 with rfl | hxV
    · exact (Finset.mem_erase.1 hx2).1 rfl
    · exact Finset.disjoint_left.1 C.VU_disj hxV (Finset.mem_erase.1 hx2).2
  have hgl := glue_involution hdisj hμVinv hμVsupp hgUinv hgUsupp
  let μ := mkMatching (glue (insert c C.V) μV gU) hgl.1
  have hμ_Vc : ∀ x ∈ insert c C.V, μ.val x = μV x := hgl.2.1
  have hμ_Uc : ∀ x ∈ C.U.erase c, μ.val x = gU x := hgl.2.2.1
  have hmc_le : C.p.partnerRank c (μ.val c) ≤ 2 * k := by
    have hmc_ne : μ.val c ≠ c := by
      rw [hμ_Vc c (Finset.mem_insert_self _ _)]
      intro h; exact Finset.disjoint_left.1 C.VU_disj hμVc (by rw [h]; exact hc)
    have := partnerRank_lt_of_ne C.p hmc_ne; omega
  have hno_Uc : ∀ x ∈ C.U.erase c, ∀ y, ¬ IsKBlockingPair ⊤ C.p.partnerRank k μ x y := by
    intro x hx y hxy
    have hxU : x ∈ C.U := (Finset.mem_erase.1 hx).2
    have hμx : μ.val x = gU x := hμ_Uc x hx
    have hgx_in := hgUin x hx
    have hrx_le : C.p.partnerRank x (μ.val x) ≤ 2 * k := by
      have := partnerRank_lt_of_ne C.p (hμx ▸ hgx_in.2); omega
    rcases hgUgood x hx with hgf | hfg | ⟨hnebad, hprev⟩
    · have hrx_eq : C.p.partnerRank x (μ.val x) = k + 1 := by rw [hμx, hgf, C.f_rank]
      have hry_eq : C.p.partnerRank x y = 1 := by
        have := hxy.2.2.1; have := partnerRank_pos C.p x y; omega
      rcases C.f_surj hxU with ⟨z, hzU, hfz⟩
      have hy_eq : y = z := partnerRank_inj C.p x (hry_eq.trans (by rw [← hfz, C.f_rank1 hzU]))
      rw [hy_eq] at hxy
      have hmy_le : C.p.partnerRank z (μ.val z) ≤ 2 * k := by
        by_cases hzc : z = c
        · rw [hzc]; exact hmc_le
        · have hzUc : z ∈ C.U.erase c := Finset.mem_erase.2 ⟨hzc, hzU⟩
          have := partnerRank_lt_of_ne C.p ((hμ_Uc z hzUc) ▸ (hgUin z hzUc).2); omega
      have hrzx : C.p.partnerRank z x = k + 1 := by rw [← hfz, C.f_rank]
      have := hxy.2.2.2; omega
    · have hgxU : gU x ∈ C.U := (Finset.mem_erase.1 hgx_in.1).2
      have hrx1 : C.p.partnerRank x (μ.val x) = 1 := by
        rw [hμx]; have := C.f_rank1 hgxU; rwa [hfg] at this
      have := C.hk; exact not_kBlocking_of_immune C.p k μ (by omega) hxy
    · have hrxy_le : C.p.partnerRank x y ≤ k := by have := hxy.2.2.1; omega
      by_cases hyU : y ∈ C.U
      · have hfy : C.f y = x := by
          by_contra hne; have := C.f_other_ge hxU hyU hne; omega
        rcases hprev y hyU hfy with rfl | hfgy
        · have hrcx : C.p.partnerRank y x = k + 1 := by rw [← hfy, C.f_rank]
          have := hxy.2.2.2; omega
        · by_cases hyc : y = c
          · rw [hyc] at hxy hfy
            have hrcx : C.p.partnerRank c x = k + 1 := by rw [← hfy, C.f_rank]
            have := hxy.2.2.2; omega
          · have hyUc : y ∈ C.U.erase c := Finset.mem_erase.2 ⟨hyc, hyU⟩
            have hgyU : gU y ∈ C.U := (Finset.mem_erase.1 (hgUin y hyUc).1).2
            have hry1 : C.p.partnerRank y (μ.val y) = 1 := by
              rw [hμ_Uc y hyUc]; have := C.f_rank1 hgyU; rwa [hfgy] at this
            have := C.hk; exact not_kBlocking_of_immune C.p k μ (by omega) (isKBlockingPair_symm C.p k μ hxy)
      · have hyV : y ∈ C.V := (C.mem_V_or_U y).resolve_right hyU
        by_cases hys : y = s
        · rw [hys] at hxy hrxy_le
          have hms : μ.val s = s := by rw [hμ_Vc s (Finset.mem_insert_of_mem hs)]; exact hμVs
          have hrsx_le : C.p.partnerRank s x ≤ k + 1 := by
            have := hxy.2.2.2; rw [hms, C.p.partnerRank_self s] at this; omega
          have hrsx_ne : C.p.partnerRank s x ≠ k + 1 := fun h => hnebad (C.f_uniq s x h)
          exact hclean_s x hx ⟨hxy.1.ne.symm, by omega, hrxy_le⟩
        · have hyVs : y ∈ C.V.erase s := Finset.mem_erase.2 ⟨hys, hyV⟩
          have hmy : μ.val y = μV y := hμ_Vc y (Finset.mem_insert_of_mem hyV)
          rcases hclean_w y hyVs with himm | hnoH
          · exact not_kBlocking_of_immune C.p k μ (hmy ▸ himm) (isKBlockingPair_symm C.p k μ hxy)
          · have hmy_le : C.p.partnerRank y (μ.val y) ≤ 2 * k := by
              have := partnerRank_lt_of_ne C.p (hmy ▸ (hμVw y hyVs).2); omega
            have hryx_le : C.p.partnerRank y x ≤ k := by have := hxy.2.2.2; omega
            exact hnoH x hx ⟨hxy.1.ne.symm, hryx_le, hrxy_le⟩
  rcases C.hblk μ with ⟨i, j, hij⟩
  have hiVc : i ∈ insert c C.V := by
    rcases C.mem_V_or_U i with h | h
    · exact Finset.mem_insert_of_mem h
    · by_cases hic : i = c
      · exact hic ▸ Finset.mem_insert_self _ _
      · exact False.elim (hno_Uc i (Finset.mem_erase.2 ⟨hic, h⟩) j hij)
  have hjVc : j ∈ insert c C.V := by
    rcases C.mem_V_or_U j with h | h
    · exact Finset.mem_insert_of_mem h
    · by_cases hjc : j = c
      · exact hjc ▸ Finset.mem_insert_self _ _
      · exact False.elim (hno_Uc j (Finset.mem_erase.2 ⟨hjc, h⟩) i (isKBlockingPair_symm C.p k μ hij))
  refine ⟨i, hiVc, j, hjVc, hij.1.ne, ?_, ?_, ?_⟩
  · rw [← hμ_Vc i hiVc]; exact hij.2.1
  · rw [← hμ_Vc i hiVc]; exact hij.2.2.1
  · rw [← hμ_Vc j hjVc]; exact hij.2.2.2

/-- Lemma 2: No H-edges between V and U. -/
private lemma no_H_VU {a c} (ha : a ∈ C.V) (hc : c ∈ C.U) : ¬ C.Hadj a c := by
  intro hac
  let b := C.M.val a
  have hbV : b ∈ C.V := (C.M_in_V ha).1
  have hba : b ≠ a := (C.M_in_V ha).2.1
  have hca : c ≠ a := hac.1.symm
  have hcb : c ≠ b := fun h => Finset.disjoint_left.1 C.VU_disj hbV (h ▸ hc)
  have hb_no_H : ∀ x ∈ C.U.erase c, ¬ C.Hadj b x := by
    intro x hx hbx
    have hxU : x ∈ C.U := (Finset.mem_erase.1 hx).2
    have hxc : x ≠ c := (Finset.mem_erase.1 hx).1
    have hxa : x ≠ a := fun h => Finset.disjoint_left.1 C.VU_disj ha (h ▸ hxU)
    have hxb : x ≠ b := hbx.1.symm
    let W := (C.V.erase a).erase b
    have hMW : ∀ z ∈ W, C.M.val z ∈ W := by
      intro z hz; simp only [W, Finset.mem_erase] at hz ⊢
      refine ⟨fun h => hz.2.1 (C.M.property.injective h),
              fun h => hz.1 (by dsimp only [b]; rw [← h, C.M.property z]), (C.M_in_V hz.2.2).1⟩
    have hs4 := swap4_spec hba.symm hxa.symm hcb hxc.symm
    have hres := restrict_inv C.M.property hMW
    have hd : Disjoint ({a, c, b, x} : Finset _) W := by
      rw [Finset.disjoint_left]; intro z hz1 hz2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz1
      simp only [W, Finset.mem_erase] at hz2
      rcases hz1 with rfl | rfl | rfl | rfl
      · exact hz2.2.1 rfl
      · exact Finset.disjoint_left.1 C.VU_disj hz2.2.2 hc
      · exact hz2.1 rfl
      · exact Finset.disjoint_left.1 C.VU_disj hz2.2.2 hxU
    have hgl := glue_involution hd hs4.1 hs4.2.2.2.2.2 hres.1 hres.2.2
    let g := glue ({a, c, b, x} : Finset _) (swap4 a c b x) (restrictTo W C.M.val)
    let M' := mkMatching g hgl.1
    have hga : g a = c := by dsimp only [g]; rw [hgl.2.1 a (by simp)]; exact hs4.2.1
    have hgc : g c = a := by dsimp only [g]; rw [hgl.2.1 c (by simp)]; exact hs4.2.2.1
    have hgb : g b = x := by dsimp only [g]; rw [hgl.2.1 b (by simp)]; exact hs4.2.2.2.1
    have hgx : g x = b := by dsimp only [g]; rw [hgl.2.1 x (by simp)]; exact hs4.2.2.2.2.1
    have hM'hm : ∀ z, M'.val z = z ∨ C.Hadj z (M'.val z) := by
      intro z; change g z = z ∨ C.Hadj z (g z)
      by_cases h1 : z = a; · rw [h1, hga]; exact Or.inr hac
      by_cases h2 : z = c; · rw [h2, hgc]; exact Or.inr (C.Hadj_symm hac)
      by_cases h3 : z = b; · rw [h3, hgb]; exact Or.inr hbx
      by_cases h4 : z = x; · rw [h4, hgx]; exact Or.inr (C.Hadj_symm hbx)
      by_cases hzW : z ∈ W
      · dsimp only [g]; rw [hgl.2.2.1 z hzW, hres.2.1 z hzW]; exact Or.inr (C.M_in_V (Finset.mem_erase.1 (Finset.mem_erase.1 hzW).2).2).2.2
      · left; exact hgl.2.2.2 z (by simp [h1, h2, h3, h4, hzW])
    have hsub : insert c (insert x C.V) ⊆ Finset.univ.filter (fun z => M'.val z ≠ z) := by
      intro z hz; refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩; change g z ≠ z
      simp only [Finset.mem_insert] at hz
      rcases hz with rfl | rfl | hzV
      · rw [hgc]; exact hca.symm
      · rw [hgx]; exact hxb.symm
      · by_cases h1 : z = a; · rw [h1, hga]; exact hca
        by_cases h2 : z = b; · rw [h2, hgb]; exact hxb
        · have hzW : z ∈ W := Finset.mem_erase.2 ⟨h2, Finset.mem_erase.2 ⟨h1, hzV⟩⟩
          dsimp only [g]; rw [hgl.2.2.1 z hzW, hres.2.1 z hzW]; exact (C.M_in_V hzV).2.1
    have h1 : x ∉ C.V := (Finset.mem_sdiff.1 hxU).2
    have h2 : c ∉ insert x C.V := by simp [hxc.symm, (Finset.mem_sdiff.1 hc).2]
    have hle := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h1] at hle
    have hmax := C.hM_max M' hM'hm; change _ ≤ C.V.card at hmax; omega
  let W := (C.V.erase a).erase b
  have hMW : ∀ z ∈ W, C.M.val z ∈ W := by
    intro z hz; simp only [W, Finset.mem_erase] at hz ⊢
    refine ⟨fun h => hz.2.1 (C.M.property.injective h),
            fun h => hz.1 (by dsimp only [b]; rw [← h, C.M.property z]), (C.M_in_V hz.2.2).1⟩
  have hres := restrict_inv C.M.property hMW
  have hd : Disjoint ({a, c} : Finset _) W := by
    rw [Finset.disjoint_left]; intro z hz1 hz2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz1
    rcases hz1 with rfl | rfl
    · exact (Finset.mem_erase.1 (Finset.mem_erase.1 hz2).2).1 rfl
    · exact Finset.disjoint_left.1 C.VU_disj (Finset.mem_erase.1 (Finset.mem_erase.1 hz2).2).2 hc
  have hgl := glue_involution hd (swap2_inv a c) (swap2_supp a c) hres.1 hres.2.2
  let μV := glue ({a, c} : Finset _) (swap2 a c) (restrictTo W C.M.val)
  have hμa : μV a = c := by dsimp only [μV]; rw [hgl.2.1 a (by simp), swap2_left]
  have hμc : μV c = a := by dsimp only [μV]; rw [hgl.2.1 c (by simp), swap2_right]
  have hμb : μV b = b := hgl.2.2.2 b (by simp [W, hba, hcb.symm])
  have hμsupp : ∀ z, z ∉ insert c C.V → μV z = z := by
    intro z hz; apply hgl.2.2.2
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, W, Finset.mem_erase, not_or] at hz ⊢
    exact ⟨⟨fun h => hz.2 (h ▸ ha), hz.1⟩, fun h => hz.2 h.2.2⟩
  have hμw : ∀ w ∈ C.V.erase b, μV w ∈ insert c C.V ∧ μV w ≠ w := by
    intro w hw; rcases Finset.mem_erase.1 hw with ⟨hwb, hwV⟩
    by_cases hwa : w = a
    · rw [hwa, hμa]; exact ⟨Finset.mem_insert_self _ _, hca⟩
    · have hwW : w ∈ W := Finset.mem_erase.2 ⟨hwb, Finset.mem_erase.2 ⟨hwa, hwV⟩⟩
      dsimp only [μV]; rw [hgl.2.2.1 w hwW, hres.2.1 w hwW]
      exact ⟨Finset.mem_insert_of_mem (C.M_in_V hwV).1, (C.M_in_V hwV).2.1⟩
  have himm : ∀ w ∈ insert c C.V, w ≠ b → C.p.partnerRank w (μV w) ≤ k := by
    intro w hw hwb
    by_cases hwc : w = c
    · rw [hwc, hμc]; exact hac.2.2
    · have hwV : w ∈ C.V := (Finset.mem_insert.1 hw).resolve_left hwc
      by_cases hwa : w = a
      · rw [hwa, hμa]; exact hac.2.1
      · have hwW : w ∈ W := Finset.mem_erase.2 ⟨hwb, Finset.mem_erase.2 ⟨hwa, hwV⟩⟩
        dsimp only [μV]; rw [hgl.2.2.1 w hwW, hres.2.1 w hwW]; exact (C.M_in_V hwV).2.2.2.1
  rcases C.U_cleanup (μV := μV) hc hbV hgl.1 hμsupp hμb (by rw [hμc]; exact ha) hμw
      (fun w hw => Or.inl (himm w (Finset.mem_insert_of_mem (Finset.mem_erase.1 hw).2) (Finset.mem_erase.1 hw).1))
      hb_no_H with ⟨i, hi, j, hj, hij_ne, _, h1, h2⟩
  have hib : i = b := by by_contra hne; have := himm i hi hne; have := partnerRank_pos C.p i j; omega
  have hjb : j = b := by by_contra hne; have := himm j hj hne; have := partnerRank_pos C.p j i; omega
  exact hij_ne (hib.trans hjb.symm)

/-- Theorem 0: Clean U-cleanup (now `no_H_VU` is unconditional!). -/
private lemma clean_Vc {c s : Fin (2 * k + 1)} (hc : c ∈ C.U) (hs : s ∈ C.V)
    {μV : Fin (2 * k + 1) → Fin (2 * k + 1)}
    (hμVinv : Function.Involutive μV)
    (hμVsupp : ∀ x, x ∉ insert c C.V → μV x = x)
    (hμVs : μV s = s) (hμVc : μV c ∈ C.V)
    (hμVw : ∀ w ∈ C.V.erase s, μV w ∈ insert c C.V ∧ μV w ≠ w) :
    ∃ i ∈ insert c C.V, ∃ j ∈ insert c C.V,
      i ≠ j ∧ μV i ≠ j ∧
      C.p.partnerRank i j + k ≤ C.p.partnerRank i (μV i) ∧
      C.p.partnerRank j i + k ≤ C.p.partnerRank j (μV j) :=
  C.U_cleanup hc hs hμVinv hμVsupp hμVs hμVc hμVw
    (fun _ hw => Or.inr (fun _ hx => C.no_H_VU (Finset.mem_erase.1 hw).2 (Finset.mem_erase.1 hx).2))
    (fun _ hx => C.no_H_VU hs (Finset.mem_erase.1 hx).2)

private def HasHPM (W : Finset (Fin (2 * k + 1))) : Prop :=
  ∃ g : Fin (2 * k + 1) → Fin (2 * k + 1), Function.Involutive g ∧
    (∀ x, x ∉ W → g x = x) ∧ (∀ x ∈ W, g x ∈ W ∧ C.Hadj x (g x))

private lemma T1_obstruct {a b} (ha : a ∈ C.V) (hb : b ∈ C.V) (hab : a ≠ b)
    (hpm : C.HasHPM ((C.V.erase a).erase b)) {c} (hc : c ∈ C.U) :
    (C.p.partnerRank b a ≤ k + 1 ∧ C.p.partnerRank a b + k ≤ C.p.partnerRank a c) ∨
    (C.p.partnerRank b c = k + 1 ∧ C.p.partnerRank c b + k ≤ C.p.partnerRank c a) := by
  rcases hpm with ⟨g, hginv, hgsupp, hgin⟩
  have hac : a ≠ c := fun h => Finset.disjoint_left.1 C.VU_disj ha (h ▸ hc)
  have hbc : b ≠ c := fun h => Finset.disjoint_left.1 C.VU_disj hb (h ▸ hc)
  let W := (C.V.erase a).erase b
  have hd : Disjoint ({a, c} : Finset _) W := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx1
    rcases hx1 with rfl | rfl
    · exact (Finset.mem_erase.1 (Finset.mem_erase.1 hx2).2).1 rfl
    · exact Finset.disjoint_left.1 C.VU_disj (Finset.mem_erase.1 (Finset.mem_erase.1 hx2).2).2 hc
  have hgl := glue_involution hd (swap2_inv a c) (swap2_supp a c) hginv hgsupp
  let μV := glue ({a, c} : Finset _) (swap2 a c) g
  have hμa : μV a = c := by dsimp only [μV]; rw [hgl.2.1 a (by simp), swap2_left]
  have hμc : μV c = a := by dsimp only [μV]; rw [hgl.2.1 c (by simp), swap2_right]
  have hμb : μV b = b := hgl.2.2.2 b (by simp [W, hab.symm, hbc])
  have hμW : ∀ w ∈ W, μV w = g w := hgl.2.2.1
  have hμsupp : ∀ z, z ∉ insert c C.V → μV z = z := by
    intro z hz; apply hgl.2.2.2
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, W, Finset.mem_erase, not_or] at hz ⊢
    exact ⟨⟨fun h => hz.2 (h ▸ ha), hz.1⟩, fun h => hz.2 h.2.2⟩
  have hμw : ∀ w ∈ C.V.erase b, μV w ∈ insert c C.V ∧ μV w ≠ w := by
    intro w hw; rcases Finset.mem_erase.1 hw with ⟨hwb, hwV⟩
    by_cases hwa : w = a
    · rw [hwa, hμa]; exact ⟨Finset.mem_insert_self _ _, hac.symm⟩
    · have hwW : w ∈ W := Finset.mem_erase.2 ⟨hwb, Finset.mem_erase.2 ⟨hwa, hwV⟩⟩
      rw [hμW w hwW]; have hgw := hgin w hwW
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_erase.1 (Finset.mem_erase.1 hgw.1).2).2, hgw.2.1.symm⟩
  rcases C.clean_Vc (μV := μV) hc hb hgl.1 hμsupp hμb (by rw [hμc]; exact ha) hμw with
    ⟨i, hi, j, hj, hij_ne, hμij, h1, h2⟩
  have hnotW : ∀ x ∈ W, ∀ y, ¬ (C.p.partnerRank x y + k ≤ C.p.partnerRank x (μV x)) := by
    intro x hx y hle; rw [hμW x hx] at hle
    have := (hgin x hx).2.2.1; have := partnerRank_pos C.p x y; omega
  have hi_abc : i = a ∨ i = b ∨ i = c := by
    by_contra h; push Not at h
    exact hnotW i (Finset.mem_erase.2 ⟨h.2.1, Finset.mem_erase.2 ⟨h.1, (Finset.mem_insert.1 hi).resolve_left h.2.2⟩⟩) j h1
  have hj_abc : j = a ∨ j = b ∨ j = c := by
    by_contra h; push Not at h
    exact hnotW j (Finset.mem_erase.2 ⟨h.2.1, Finset.mem_erase.2 ⟨h.1, (Finset.mem_insert.1 hj).resolve_left h.2.2⟩⟩) i h2
  have hpair_bc : C.p.partnerRank b c + k ≤ C.p.partnerRank b b →
      C.p.partnerRank c b + k ≤ C.p.partnerRank c a →
      C.p.partnerRank b c = k + 1 ∧ C.p.partnerRank c b + k ≤ C.p.partnerRank c a := by
    intro hbc1 hcb1; rw [C.p.partnerRank_self b] at hbc1
    have hrca : C.p.partnerRank c a ≤ 2 * k := by have := partnerRank_lt_of_ne C.p hac; omega
    have hrcb_le : C.p.partnerRank c b ≤ k := by omega
    have hrbc_ge : k + 1 ≤ C.p.partnerRank b c := by
      by_contra hlt; exact C.no_H_VU hb hc ⟨hbc, by omega, hrcb_le⟩
    exact ⟨by omega, hcb1⟩
  rcases hi_abc with rfl | rfl | rfl <;> rcases hj_abc with rfl | rfl | rfl
  · exact False.elim (hij_ne rfl)
  · rw [hμa] at h1; rw [hμb, C.p.partnerRank_self _] at h2; exact Or.inl ⟨by omega, h1⟩
  · rw [hμa] at hμij; exact False.elim (hμij rfl)
  · rw [hμb, C.p.partnerRank_self _] at h1; rw [hμa] at h2; exact Or.inl ⟨by omega, h2⟩
  · exact False.elim (hij_ne rfl)
  · rw [hμb] at h1; rw [hμc] at h2; exact Or.inr (hpair_bc h1 h2)
  · rw [hμc] at hμij; exact False.elim (hμij rfl)
  · rw [hμc] at h1; rw [hμb] at h2; exact Or.inr (hpair_bc h2 h1)
  · exact False.elim (hij_ne rfl)

private lemma closure_prop {a b} (ha : a ∈ C.V) (hb : b ∈ C.V) (hab : a ≠ b)
    (hpm : C.HasHPM ((C.V.erase a).erase b)) : C.Hadj a b := by
  have hdir : ∀ {x y}, x ∈ C.V → y ∈ C.V → x ≠ y → C.HasHPM ((C.V.erase x).erase y) →
      C.p.partnerRank x y ≤ k := by
    intro x y hx hy hxy hpm'
    have hpos : 0 < (C.U.erase (C.f y)).card := by
      have := Finset.pred_card_le_card_erase (s := C.U) (a := C.f y); have := C.U_ge3; omega
    rcases Finset.card_pos.1 hpos with ⟨c, hc⟩
    have hcU := (Finset.mem_erase.1 hc).2; have hcf := (Finset.mem_erase.1 hc).1
    rcases C.T1_obstruct hx hy hxy hpm' hcU with ⟨_, h1⟩ | ⟨h2, _⟩
    · have hcx : c ≠ x := fun h => Finset.disjoint_left.1 C.VU_disj hx (by rw [← h]; exact hcU)
      have hrxc : C.p.partnerRank x c ≤ 2 * k := by have := partnerRank_lt_of_ne C.p hcx; omega
      omega
    · exact False.elim (hcf (C.f_uniq y c h2))
  have hpm_sym : C.HasHPM ((C.V.erase b).erase a) := by rw [Finset.erase_right_comm]; exact hpm
  exact ⟨hab, hdir ha hb hab hpm, hdir hb ha hab.symm hpm_sym⟩

private lemma swap_adj {a b} (ha : a ∈ C.V) (hb : b ∈ C.V) (hab : C.Hadj a b) :
    C.Hadj (C.M.val a) (C.M.val b) := by
  by_cases hbm : b = C.M.val a
  · rw [hbm, C.M.property a]; exact C.Hadj_symm (hbm ▸ hab)
  · have hMaV := (C.M_in_V ha).1; have hMbV := (C.M_in_V hb).1
    have hMaMb : C.M.val a ≠ C.M.val b := fun h => hab.1 (C.M.property.injective h)
    have hMb_ne_a : C.M.val b ≠ a := fun h => hbm (by rw [← C.M.property b, h])
    apply C.closure_prop hMaV hMbV hMaMb
    let W := (C.V.erase (C.M.val a)).erase (C.M.val b)
    let W' := (W.erase a).erase b
    have hMW' : ∀ z ∈ W', C.M.val z ∈ W' := by
      intro z hz; simp only [W', W, Finset.mem_erase] at hz ⊢
      refine ⟨fun h => hz.2.2.1 (by rw [← h, C.M.property z]),
              fun h => hz.2.2.2.1 (by rw [← h, C.M.property z]),
              fun h => hz.1 (C.M.property.injective h),
              fun h => hz.2.1 (C.M.property.injective h),
              (C.M_in_V hz.2.2.2.2).1⟩
    have hres := restrict_inv C.M.property hMW'
    have hd : Disjoint ({a, b} : Finset _) W' := by
      rw [Finset.disjoint_left]; intro z hz1 hz2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz1
      simp only [W', Finset.mem_erase] at hz2
      rcases hz1 with rfl | rfl; exact hz2.2.1 rfl; exact hz2.1 rfl
    have hgl := glue_involution hd (swap2_inv a b) (swap2_supp a b) hres.1 hres.2.2
    have haW : a ∈ W := Finset.mem_erase.2 ⟨hMb_ne_a.symm, Finset.mem_erase.2 ⟨(C.M_in_V ha).2.1.symm, ha⟩⟩
    have hbW : b ∈ W := Finset.mem_erase.2 ⟨(C.M_in_V hb).2.1.symm, Finset.mem_erase.2 ⟨hbm, hb⟩⟩
    have hunion : ({a, b} : Finset _) ∪ W' = W := by
      ext z; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, W', Finset.mem_erase]
      constructor
      · rintro ((rfl | rfl) | ⟨_, _, hzW⟩); exact haW; exact hbW; exact hzW
      · intro hzW
        by_cases h1 : z = a; · exact Or.inl (Or.inl h1)
        by_cases h2 : z = b; · exact Or.inl (Or.inr h2)
        · exact Or.inr ⟨h2, h1, hzW⟩
    let g := glue ({a, b} : Finset _) (swap2 a b) (restrictTo W' C.M.val)
    refine ⟨g, hgl.1, fun z hz => hgl.2.2.2 z (hunion.symm ▸ hz), ?_⟩
    intro z hzW
    by_cases h1 : z = a
    · rw [h1]; dsimp only [g]; rw [hgl.2.1 a (by simp), swap2_left]; exact ⟨hbW, hab⟩
    by_cases h2 : z = b
    · rw [h2]; dsimp only [g]; rw [hgl.2.1 b (by simp), swap2_right]; exact ⟨haW, C.Hadj_symm hab⟩
    · have hzW' : z ∈ W' := Finset.mem_erase.2 ⟨h2, Finset.mem_erase.2 ⟨h1, hzW⟩⟩
      dsimp only [g]; rw [hgl.2.2.1 z hzW', hres.2.1 z hzW']
      exact ⟨(Finset.mem_erase.1 (Finset.mem_erase.1 (hMW' z hzW')).2).2,
        (C.M_in_V (Finset.mem_erase.1 (Finset.mem_erase.1 hzW).2).2).2.2⟩

private lemma pm_erase_adj {a b} (ha : a ∈ C.V) (hb : b ∈ C.V) (hab : C.Hadj a b) :
    C.HasHPM ((C.V.erase a).erase b) := by
  let W := (C.V.erase a).erase b
  by_cases hbm : b = C.M.val a
  · have hMW : ∀ z ∈ W, C.M.val z ∈ W := by
      intro z hz; simp only [W, Finset.mem_erase] at hz ⊢
      refine ⟨fun h => hz.2.1 (by rw [hbm] at h; exact C.M.property.injective h),
              fun h => hz.1 (by rw [hbm, ← h, C.M.property z]), (C.M_in_V hz.2.2).1⟩
    have hres := restrict_inv C.M.property hMW
    exact ⟨restrictTo W C.M.val, hres.1, hres.2.2,
      fun z hz => by rw [hres.2.1 z hz]; exact ⟨hMW z hz, (C.M_in_V (Finset.mem_erase.1 (Finset.mem_erase.1 hz).2).2).2.2⟩⟩
  · have hMaMb := C.swap_adj ha hb hab
    have hMaW : C.M.val a ∈ W := Finset.mem_erase.2 ⟨Ne.symm hbm, Finset.mem_erase.2 ⟨(C.M_in_V ha).2.1, (C.M_in_V ha).1⟩⟩
    have hMbW : C.M.val b ∈ W := Finset.mem_erase.2 ⟨(C.M_in_V hb).2.1, Finset.mem_erase.2 ⟨fun h => hbm (by rw [← C.M.property b, h]), (C.M_in_V hb).1⟩⟩
    let W' := (W.erase (C.M.val a)).erase (C.M.val b)
    have hMW' : ∀ z ∈ W', C.M.val z ∈ W' := by
      intro z hz; simp only [W', W, Finset.mem_erase] at hz ⊢
      refine ⟨fun h => hz.2.2.1 (C.M.property.injective h),
              fun h => hz.2.2.2.1 (C.M.property.injective h),
              fun h => hz.1 (by rw [← h, C.M.property z]),
              fun h => hz.2.1 (by rw [← h, C.M.property z]),
              (C.M_in_V hz.2.2.2.2).1⟩
    have hres := restrict_inv C.M.property hMW'
    have hd : Disjoint ({C.M.val a, C.M.val b} : Finset _) W' := by
      rw [Finset.disjoint_left]; intro z hz1 hz2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz1
      simp only [W', Finset.mem_erase] at hz2
      rcases hz1 with rfl | rfl; exact hz2.2.1 rfl; exact hz2.1 rfl
    have hgl := glue_involution hd (swap2_inv (C.M.val a) (C.M.val b)) (swap2_supp _ _) hres.1 hres.2.2
    have hunion : ({C.M.val a, C.M.val b} : Finset _) ∪ W' = W := by
      ext z; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, W', Finset.mem_erase]
      constructor
      · rintro ((rfl | rfl) | ⟨_, _, hzW⟩); exact hMaW; exact hMbW; exact hzW
      · intro hzW
        by_cases h1 : z = C.M.val a; · exact Or.inl (Or.inl h1)
        by_cases h2 : z = C.M.val b; · exact Or.inl (Or.inr h2)
        · exact Or.inr ⟨h2, h1, hzW⟩
    let g := glue ({C.M.val a, C.M.val b} : Finset _) (swap2 (C.M.val a) (C.M.val b)) (restrictTo W' C.M.val)
    refine ⟨g, hgl.1, fun z hz => hgl.2.2.2 z (hunion.symm ▸ hz), ?_⟩
    intro z hzW
    by_cases h1 : z = C.M.val a
    · rw [h1]; dsimp only [g]; rw [hgl.2.1 (C.M.val a) (by simp), swap2_left]; exact ⟨hMbW, hMaMb⟩
    by_cases h2 : z = C.M.val b
    · rw [h2]; dsimp only [g]; rw [hgl.2.1 (C.M.val b) (by simp), swap2_right]; exact ⟨hMaW, C.Hadj_symm hMaMb⟩
    · have hzW' : z ∈ W' := Finset.mem_erase.2 ⟨h2, Finset.mem_erase.2 ⟨h1, hzW⟩⟩
      dsimp only [g]; rw [hgl.2.2.1 z hzW', hres.2.1 z hzW']
      exact ⟨(Finset.mem_erase.1 (Finset.mem_erase.1 (hMW' z hzW')).2).2,
        (C.M_in_V (Finset.mem_erase.1 (Finset.mem_erase.1 hzW).2).2).2.2⟩

private lemma closure_of_three_M_edges {r1 r2 u1 u2 u3 u4 : Fin (2 * k + 1)}
    (hr1 : r1 ∈ C.V) (hr2 : r2 ∈ C.V) (hr12 : r1 ≠ r2)
    (hu1 : u1 ∈ (C.V.erase r1).erase r2) (hu2 : u2 ∈ (C.V.erase r1).erase r2)
    (hu3 : u3 ∈ (C.V.erase r1).erase r2) (hu4 : u4 ∈ (C.V.erase r1).erase r2)
    (h13 : u1 ≠ u3) (h14 : u1 ≠ u4) (h23 : u2 ≠ u3) (h24 : u2 ≠ u4)
    (hclosed : ∀ z ∈ ({r1, r2, u1, u2, u3, u4} : Finset _), C.M.val z ∈ ({r1, r2, u1, u2, u3, u4} : Finset _))
    (he1 : C.Hadj u1 u2) (he2 : C.Hadj u3 u4) : C.Hadj r1 r2 := by
  apply C.closure_prop hr1 hr2 hr12
  let W := (C.V.erase r1).erase r2
  let S4 : Finset (Fin (2 * k + 1)) := {u1, u2, u3, u4}
  let W' := W \ S4
  have hS4_sub : S4 ⊆ W := by
    intro z hz; simp only [S4, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  have hMW' : ∀ z ∈ W', C.M.val z ∈ W' := by
    intro z hz; rcases Finset.mem_sdiff.1 hz with ⟨hzW, hznot4⟩
    have hzV := (Finset.mem_erase.1 (Finset.mem_erase.1 hzW).2).2
    have hnot6 : z ∉ ({r1, r2, u1, u2, u3, u4} : Finset _) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      have hzr2 := (Finset.mem_erase.1 hzW).1
      have hzr1 := (Finset.mem_erase.1 (Finset.mem_erase.1 hzW).2).1
      simp only [S4, Finset.mem_insert, Finset.mem_singleton, not_or] at hznot4
      exact ⟨hzr1, hzr2, hznot4⟩
    have hMznot6 : C.M.val z ∉ ({r1, r2, u1, u2, u3, u4} : Finset _) := fun hm =>
      hnot6 (by rw [← C.M.property z]; exact hclosed _ hm)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hMznot6
    refine Finset.mem_sdiff.2 ⟨Finset.mem_erase.2 ⟨hMznot6.2.1, Finset.mem_erase.2 ⟨hMznot6.1, (C.M_in_V hzV).1⟩⟩, ?_⟩
    simp only [S4, Finset.mem_insert, Finset.mem_singleton, not_or]; exact hMznot6.2.2
  have hs4 := swap4_spec h13 h14 h23 h24
  have hres := restrict_inv C.M.property hMW'
  have hd_S4W' : Disjoint S4 W' := Finset.disjoint_sdiff
  have hgl := glue_involution hd_S4W' hs4.1 hs4.2.2.2.2.2 hres.1 hres.2.2
  have hunion : S4 ∪ W' = W := Finset.union_sdiff_of_subset hS4_sub
  let g := glue S4 (swap4 u1 u2 u3 u4) (restrictTo W' C.M.val)
  refine ⟨g, hgl.1, fun z hz => hgl.2.2.2 z (hunion.symm ▸ hz), ?_⟩
  intro z hzW
  by_cases hz4 : z ∈ S4
  · dsimp only [g]; rw [hgl.2.1 z hz4]
    simp only [S4, Finset.mem_insert, Finset.mem_singleton] at hz4
    rcases hz4 with rfl | rfl | rfl | rfl
    · rw [hs4.2.1]; exact ⟨hu2, he1⟩
    · rw [hs4.2.2.1]; exact ⟨hu1, C.Hadj_symm he1⟩
    · rw [hs4.2.2.2.1]; exact ⟨hu4, he2⟩
    · rw [hs4.2.2.2.2.1]; exact ⟨hu3, C.Hadj_symm he2⟩
  · have hzW' : z ∈ W' := Finset.mem_sdiff.2 ⟨hzW, hz4⟩
    dsimp only [g]; rw [hgl.2.2.1 z hzW', hres.2.1 z hzW']
    exact ⟨Finset.sdiff_subset (hMW' z hzW'), (C.M_in_V (Finset.mem_erase.1 (Finset.mem_erase.1 hzW).2).2).2.2⟩

private lemma trans_adj {x y z} (hx : x ∈ C.V) (hy : y ∈ C.V) (hz : z ∈ C.V)
    (hxy : C.Hadj (C.M.val x) y) (hyz : C.Hadj (C.M.val y) z) (hzMx : z ≠ C.M.val x) :
    C.Hadj (C.M.val x) z := by
  by_cases hzx : z = x; · rw [hzx]; exact C.Hadj_symm (C.M_in_V hx).2.2
  by_cases hzy : z = y; · rw [hzy]; exact hxy
  by_cases hyx : y = x; · rw [← hyx]; exact hyz
  have hMxV := (C.M_in_V hx).1; have hMyV := (C.M_in_V hy).1; have hMzV := (C.M_in_V hz).1
  have hxMz : x ≠ C.M.val z := fun h => hzMx (by rw [← C.M.property z, ← h])
  have hxMz_adj : C.Hadj x (C.M.val z) := C.closure_of_three_M_edges hx hMzV hxMz
    (Finset.mem_erase.2 ⟨fun h => hzx (C.M.property.injective h).symm, Finset.mem_erase.2 ⟨(C.M_in_V hx).2.1, hMxV⟩⟩)
    (Finset.mem_erase.2 ⟨fun h => hyz.1 (by rw [← C.M.property z, ← h]), Finset.mem_erase.2 ⟨hyx, hy⟩⟩)
    (Finset.mem_erase.2 ⟨fun h => hzy (C.M.property.injective h).symm, Finset.mem_erase.2 ⟨fun h => hxy.1.symm (by rw [← C.M.property y, h]), hMyV⟩⟩)
    (Finset.mem_erase.2 ⟨(C.M_in_V hz).2.1.symm, Finset.mem_erase.2 ⟨hzx, hz⟩⟩)
    (fun h => hyx (C.M.property.injective h).symm) hzMx.symm
    (C.M_in_V hy).2.1.symm (Ne.symm hzy)
    (by intro w hw; have hMx := C.M.property x; have hMy := C.M.property y; have hMz := C.M.property z
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hMx, hMy, hMz])
    hxy hyz
  have := C.swap_adj hx hMzV hxMz_adj
  rwa [C.M.property z] at this

private lemma clique_step {a2 w y} (ha2 : a2 ∈ C.V) (hw : w ∈ C.V) (hy : y ∈ C.V)
    (ha2w : C.Hadj a2 w) (hMa2w : C.Hadj (C.M.val a2) w) (hMa2y : C.Hadj (C.M.val a2) y)
    (hya2 : y ≠ a2) : C.Hadj a2 y := by
  by_cases hyw : y = w; · rw [hyw]; exact ha2w
  by_cases hyMw : y = C.M.val w
  · rw [hyMw]; have := C.swap_adj (C.M_in_V ha2).1 hw hMa2w; rwa [C.M.property a2] at this
  have hMa2V := (C.M_in_V ha2).1; have hMwV := (C.M_in_V hw).1; have hMyV := (C.M_in_V hy).1
  have hw_ne_a2 : w ≠ a2 := ha2w.1.symm
  have hw_ne_Ma2 : w ≠ C.M.val a2 := hMa2w.1.symm
  have hy_ne_Ma2 : y ≠ C.M.val a2 := hMa2y.1.symm
  have ha2_ne_Ma2 : a2 ≠ C.M.val a2 := (C.M_in_V ha2).2.1.symm
  have hw_ne_Mw : w ≠ C.M.val w := (C.M_in_V hw).2.1.symm
  have hy_ne_My : y ≠ C.M.val y := (C.M_in_V hy).2.1.symm
  have ha2_ne_Mw : a2 ≠ C.M.val w := fun h => hw_ne_Ma2 (by rw [← C.M.property w, ← h])
  have ha2_ne_My : a2 ≠ C.M.val y := fun h => hy_ne_Ma2 (by rw [← C.M.property y, ← h])
  have hMa2_ne_Mw : C.M.val a2 ≠ C.M.val w := fun h => hw_ne_a2 (C.M.property.injective h).symm
  have hMa2_ne_My : C.M.val a2 ≠ C.M.val y := fun h => hya2 (C.M.property.injective h).symm
  have hw_ne_My : w ≠ C.M.val y := fun h => hyMw (by rw [← C.M.property y, ← h])
  have hMw_ne_My : C.M.val w ≠ C.M.val y := fun h => hyw (C.M.property.injective h).symm
  have ha2Mw : C.Hadj a2 (C.M.val w) := by
    have := C.swap_adj hMa2V hw hMa2w; rwa [C.M.property a2] at this
  have hMa2Mw : C.Hadj (C.M.val a2) (C.M.val w) := C.swap_adj ha2 hw ha2w
  have hwMy : C.Hadj w (C.M.val y) := C.closure_of_three_M_edges hw hMyV hw_ne_My
    (Finset.mem_erase.2 ⟨ha2_ne_My, Finset.mem_erase.2 ⟨hw_ne_a2.symm, ha2⟩⟩)
    (Finset.mem_erase.2 ⟨hMw_ne_My, Finset.mem_erase.2 ⟨hw_ne_Mw.symm, hMwV⟩⟩)
    (Finset.mem_erase.2 ⟨hMa2_ne_My, Finset.mem_erase.2 ⟨hw_ne_Ma2.symm, hMa2V⟩⟩)
    (Finset.mem_erase.2 ⟨hy_ne_My, Finset.mem_erase.2 ⟨hyw, hy⟩⟩)
    ha2_ne_Ma2 hya2.symm hMa2_ne_Mw.symm (Ne.symm hyMw)
    (by intro z hz; have hMa2 := C.M.property a2; have hMw := C.M.property w; have hMy := C.M.property y
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hMa2, hMw, hMy])
    ha2Mw hMa2y
  exact C.closure_of_three_M_edges ha2 hy hya2.symm
    (Finset.mem_erase.2 ⟨hy_ne_Ma2.symm, Finset.mem_erase.2 ⟨ha2_ne_Ma2.symm, hMa2V⟩⟩)
    (Finset.mem_erase.2 ⟨Ne.symm hyMw, Finset.mem_erase.2 ⟨ha2_ne_Mw.symm, hMwV⟩⟩)
    (Finset.mem_erase.2 ⟨Ne.symm hyw, Finset.mem_erase.2 ⟨hw_ne_a2, hw⟩⟩)
    (Finset.mem_erase.2 ⟨hy_ne_My.symm, Finset.mem_erase.2 ⟨ha2_ne_My.symm, hMyV⟩⟩)
    hw_ne_Ma2.symm hMa2_ne_My hw_ne_Mw.symm hMw_ne_My
    (by intro z hz; have hMa2 := C.M.property a2; have hMw := C.M.property w; have hMy := C.M.property y
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hMa2, hMw, hMy])
    hMa2Mw hwMy

private def Utop (a : Fin (2 * k + 1)) : Finset (Fin (2 * k + 1)) :=
  C.U.filter (fun c => C.p.partnerRank a c ≤ k)

private def NH (v : Fin (2 * k + 1)) : Finset (Fin (2 * k + 1)) :=
  C.V.filter (fun w => C.Hadj v w)

private lemma T2_law {a b} (ha : a ∈ C.V) (hb : b ∈ C.V) (hab : C.Hadj a b) {c} (hc : c ∈ C.U) :
    C.p.partnerRank a b + k ≤ C.p.partnerRank a c ∨
    (C.p.partnerRank b c = k + 1 ∧ C.p.partnerRank c b + k ≤ C.p.partnerRank c a) := by
  rcases C.T1_obstruct ha hb hab.1 (C.pm_erase_adj ha hb hab) hc with ⟨_, h1⟩ | h2
  · exact Or.inl h1
  · exact Or.inr h2

private lemma Utop_eq {a c} (ha : a ∈ C.V) (hc : c ∈ C.U) (hle : C.p.partnerRank a c ≤ k) :
    c = C.f (C.M.val a) := by
  rcases C.T2_law ha (C.M_in_V ha).1 (C.M_in_V ha).2.2 hc with h1 | ⟨h2, _⟩
  · have := partnerRank_pos C.p a (C.M.val a); omega
  · exact C.f_uniq (C.M.val a) c h2

private lemma Utop_le_one {a} (ha : a ∈ C.V) : (C.Utop a).card ≤ 1 := by
  refine Finset.card_le_one.2 fun c₁ hc₁ c₂ hc₂ => ?_
  exact (C.Utop_eq ha (Finset.mem_filter.1 hc₁).1 (Finset.mem_filter.1 hc₁).2).trans
    (C.Utop_eq ha (Finset.mem_filter.1 hc₂).1 (Finset.mem_filter.1 hc₂).2).symm

private lemma NH_pos {v} (hv : v ∈ C.V) : 1 ≤ (C.NH v).card :=
  Finset.card_pos.2 ⟨C.M.val v, Finset.mem_filter.2 ⟨(C.M_in_V hv).1, (C.M_in_V hv).2.2⟩⟩

private lemma deg_ge2_adj {v w} (hv : v ∈ C.V) (hw : w ∈ C.V) (hvw : C.Hadj v w)
    (hdv : 2 ≤ (C.NH v).card) : 2 ≤ (C.NH w).card := by
  by_cases hwm : w = C.M.val v
  · have hpos : 0 < ((C.NH v).erase w).card := by
      have hwNH : w ∈ C.NH v := Finset.mem_filter.2 ⟨hw, hvw⟩
      have := Finset.card_erase_add_one hwNH; omega
    rcases Finset.card_pos.1 hpos with ⟨z, hz⟩
    have hzw := (Finset.mem_erase.1 hz).1
    have hzV := (Finset.mem_filter.1 (Finset.mem_erase.1 hz).2).1
    have hvz := (Finset.mem_filter.1 (Finset.mem_erase.1 hz).2).2
    have hwMz : C.Hadj w (C.M.val z) := hwm ▸ C.swap_adj hv hzV hvz
    have hv_ne_Mz : v ≠ C.M.val z := fun h => hzw (by rw [hwm, h, C.M.property z])
    have hsub : ({v, C.M.val z} : Finset _) ⊆ C.NH w := by
      intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact Finset.mem_filter.2 ⟨hv, C.Hadj_symm hvw⟩
      · exact Finset.mem_filter.2 ⟨(C.M_in_V hzV).1, hwMz⟩
    have hc := Finset.card_le_card hsub; rwa [Finset.card_pair hv_ne_Mz] at hc
  · have hv_ne_Mw : v ≠ C.M.val w := fun h => hwm (by rw [h, C.M.property w])
    have hsub : ({v, C.M.val w} : Finset _) ⊆ C.NH w := by
      intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact Finset.mem_filter.2 ⟨hv, C.Hadj_symm hvw⟩
      · exact Finset.mem_filter.2 ⟨(C.M_in_V hw).1, (C.M_in_V hw).2.2⟩
    have hc := Finset.card_le_card hsub; rwa [Finset.card_pair hv_ne_Mw] at hc

private lemma T4_no_U {v c} (hv : v ∈ C.V) (hdv : 2 ≤ (C.NH v).card) (hc : c ∈ C.U) :
    k + 2 ≤ C.p.partnerRank v c := by
  have hex_ge2 : ∀ {u}, u ∈ C.V → 2 ≤ (C.NH u).card → ∃ w ∈ C.NH u, 2 ≤ C.p.partnerRank u w := by
    intro u hu hdu; by_contra hall; push Not at hall
    have hle1 : (C.NH u).card ≤ 1 := Finset.card_le_one.2 fun w₁ hw₁ w₂ hw₂ => by
      have := hall w₁ hw₁; have := hall w₂ hw₂
      have := partnerRank_pos C.p u w₁; have := partnerRank_pos C.p u w₂
      exact partnerRank_inj C.p u (by omega)
    omega
  by_contra hlt
  rcases hex_ge2 hv hdv with ⟨w, hwNH, hrvw⟩
  have hwV := (Finset.mem_filter.1 hwNH).1; have hvw := (Finset.mem_filter.1 hwNH).2
  rcases C.T2_law hv hwV hvw hc with h1 | ⟨hrwc, hrc1⟩
  · omega
  · rcases hex_ge2 hwV (C.deg_ge2_adj hv hwV hvw hdv) with ⟨z, hzNH, hrwz⟩
    have hzV := (Finset.mem_filter.1 hzNH).1; have hwz := (Finset.mem_filter.1 hzNH).2
    rcases C.T2_law hwV hzV hwz hc with h3 | ⟨_, hrc2⟩
    · omega
    · have hvc : v ≠ c := fun h => Finset.disjoint_left.1 C.VU_disj hv (by rw [h]; exact hc)
      have hrcv : C.p.partnerRank c v ≤ 2 * k := by have := partnerRank_lt_of_ne C.p hvc; omega
      have := partnerRank_pos C.p c z; omega

private lemma T4_Utop {v} (hv : v ∈ C.V) (hdv : 2 ≤ (C.NH v).card) : (C.Utop v).card = 0 := by
  rw [Finset.card_eq_zero]; unfold Utop; rw [Finset.filter_eq_empty_iff]
  intro c hc; have := C.T4_no_U hv hdv hc; omega

private lemma T4_rank {v w c} (hv : v ∈ C.V) (hdv : 2 ≤ (C.NH v).card) (hw : w ∈ C.NH v) (hc : c ∈ C.U) :
    C.p.partnerRank v w + k ≤ C.p.partnerRank v c := by
  have hwV := (Finset.mem_filter.1 hw).1; have hvw := (Finset.mem_filter.1 hw).2
  rcases C.T2_law hv hwV hvw hc with h1 | ⟨h2, _⟩
  · exact h1
  · have := C.T4_no_U hwV (C.deg_ge2_adj hv hwV hvw hdv) hc; omega

private def ZeroOrd : Finset (Fin (2 * k + 1) × Fin (2 * k + 1)) :=
  (C.V ×ˢ C.V).filter (fun q => q.1 ≠ q.2 ∧ k + 1 ≤ C.p.partnerRank q.1 q.2 ∧ k + 1 ≤ C.p.partnerRank q.2 q.1)

private lemma zero_arc_identity :
    C.ZeroOrd.card + C.V.card * C.U.card = ∑ v ∈ C.V, ((C.NH v).card + 2 * (C.Utop v).card) := by
  let OutA : Fin (2 * k + 1) → Finset (Fin (2 * k + 1)) :=
    fun v => C.V.filter (fun w => w ≠ v ∧ C.p.partnerRank v w ≤ k ∧ k + 1 ≤ C.p.partnerRank w v)
  have hdeg_sum : ∀ v ∈ C.V, (C.Utop v).card + (C.NH v).card + (OutA v).card = k := by
    intro v hv
    have htop : (Finset.univ.filter (fun w => C.p.partnerRank v w ≤ k)).card = k :=
      card_partnerRank_le C.p v k (by omega)
    have hsplit : Finset.univ.filter (fun w => C.p.partnerRank v w ≤ k) = C.Utop v ∪ (C.NH v ∪ OutA v) := by
      ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Utop, NH, OutA, Hadj]
      constructor
      · intro hle
        have hwv : w ≠ v := fun h => by rw [h, C.p.partnerRank_self v] at hle; omega
        rcases C.mem_V_or_U w with hwV | hwU
        · right
          by_cases hrev : C.p.partnerRank w v ≤ k
          · exact Or.inl ⟨hwV, hwv.symm, hle, hrev⟩
          · exact Or.inr ⟨hwV, hwv, hle, by omega⟩
        · exact Or.inl ⟨hwU, hle⟩
      · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩) <;> exact h
    have hd1 : Disjoint (C.NH v) (OutA v) := by
      rw [Finset.disjoint_left]; intro w h1 h2
      have a1 := (Finset.mem_filter.1 h1).2.2.2; have a2 := (Finset.mem_filter.1 h2).2.2.2; omega
    have hd2 : Disjoint (C.Utop v) (C.NH v ∪ OutA v) := by
      rw [Finset.disjoint_left]; intro w h1 h2
      have hwU := (Finset.mem_filter.1 h1).1
      rcases Finset.mem_union.1 h2 with h | h
      · exact Finset.disjoint_left.1 C.VU_disj (Finset.mem_filter.1 h).1 hwU
      · exact Finset.disjoint_left.1 C.VU_disj (Finset.mem_filter.1 h).1 hwU
    rw [hsplit, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1] at htop; omega
  let OffV := (C.V ×ˢ C.V).filter (fun q => q.1 ≠ q.2)
  let HPairs := (C.V ×ˢ C.V).filter (fun q => C.Hadj q.1 q.2)
  let FwdPairs := (C.V ×ˢ C.V).filter (fun q => q.1 ≠ q.2 ∧ C.p.partnerRank q.1 q.2 ≤ k ∧ k + 1 ≤ C.p.partnerRank q.2 q.1)
  let BwdPairs := (C.V ×ˢ C.V).filter (fun q => q.1 ≠ q.2 ∧ k + 1 ≤ C.p.partnerRank q.1 q.2 ∧ C.p.partnerRank q.2 q.1 ≤ k)
  have hOff_card : OffV.card = C.V.card * C.V.card - C.V.card := by
    have hdiag : (C.V ×ˢ C.V).filter (fun q => q.1 = q.2) = C.V.image (fun v => (v, v)) := by
      ext ⟨a, b⟩; simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
      constructor
      · rintro ⟨⟨ha, _⟩, rfl⟩; exact ⟨a, ha, rfl⟩
      · rintro ⟨v, hv, h⟩; cases h; exact ⟨⟨hv, hv⟩, rfl⟩
    have hpart : ((C.V ×ˢ C.V).filter (fun q => q.1 = q.2)).card + OffV.card = (C.V ×ˢ C.V).card := by
      have hd : Disjoint ((C.V ×ˢ C.V).filter (fun q => q.1 = q.2)) OffV := by
        rw [Finset.disjoint_left]; intro q h1 h2; exact (Finset.mem_filter.1 h2).2 (Finset.mem_filter.1 h1).2
      have hu : (C.V ×ˢ C.V).filter (fun q => q.1 = q.2) ∪ OffV = C.V ×ˢ C.V := by
        ext q; simp only [OffV, Finset.mem_union, Finset.mem_filter]; tauto
      rw [← Finset.card_union_of_disjoint hd, hu]
    rw [hdiag, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1), Finset.card_product] at hpart
    omega
  have hH_card : HPairs.card = ∑ v ∈ C.V, (C.NH v).card := by
    have hbij : HPairs = C.V.biUnion (fun v => (C.NH v).image (fun w => (v, w))) := by
      ext ⟨a, b⟩; simp only [HPairs, NH, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨⟨ha, hb⟩, hab⟩; exact ⟨a, ha, b, ⟨hb, hab⟩, rfl⟩
      · rintro ⟨v, hv, w, ⟨hw, hvw⟩, h⟩; cases h; exact ⟨⟨hv, hw⟩, hvw⟩
    rw [hbij, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun v _ => Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
    · intro v₁ _ v₂ _ hne; change Disjoint _ _; rw [Finset.disjoint_left]; intro q h1 h2
      rcases Finset.mem_image.1 h1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.1 h2 with ⟨_, _, h⟩; exact hne (Prod.mk.inj h).1.symm
  have hFwd_card : FwdPairs.card = ∑ v ∈ C.V, (OutA v).card := by
    have hbij : FwdPairs = C.V.biUnion (fun v => (OutA v).image (fun w => (v, w))) := by
      ext ⟨a, b⟩; simp only [FwdPairs, OutA, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨⟨ha, hb⟩, hne, h1, h2⟩; exact ⟨a, ha, b, ⟨hb, hne.symm, h1, h2⟩, rfl⟩
      · rintro ⟨v, hv, w, ⟨hw, hne, h1, h2⟩, h⟩; cases h; exact ⟨⟨hv, hw⟩, hne.symm, h1, h2⟩
    rw [hbij, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun v _ => Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
    · intro v₁ _ v₂ _ hne; change Disjoint _ _; rw [Finset.disjoint_left]; intro q h1 h2
      rcases Finset.mem_image.1 h1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.1 h2 with ⟨_, _, h⟩; exact hne (Prod.mk.inj h).1.symm
  have hBwd_card : BwdPairs.card = FwdPairs.card := by
    refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
    · intro ⟨a, b⟩ h; simp only [BwdPairs, FwdPairs, Finset.mem_filter, Finset.mem_product] at h ⊢
      exact ⟨⟨h.1.2, h.1.1⟩, h.2.1.symm, h.2.2.2, h.2.2.1⟩
    · intro ⟨_, _⟩ _ ⟨_, _⟩ _ h; cases h; rfl
    · intro ⟨a, b⟩ h; refine ⟨(b, a), ?_, rfl⟩
      simp only [BwdPairs, FwdPairs, Finset.mem_filter, Finset.mem_product] at h ⊢
      exact ⟨⟨h.1.2, h.1.1⟩, h.2.1.symm, h.2.2.2, h.2.2.1⟩
  have hOff_eq : OffV = HPairs ∪ (FwdPairs ∪ (BwdPairs ∪ C.ZeroOrd)) := by
    ext ⟨a, b⟩; simp only [OffV, HPairs, FwdPairs, BwdPairs, ZeroOrd, Hadj, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨habV, hne⟩
      by_cases h1 : C.p.partnerRank a b ≤ k <;> by_cases h2 : C.p.partnerRank b a ≤ k
      · exact Or.inl ⟨habV, hne, h1, h2⟩
      · exact Or.inr (Or.inl ⟨habV, hne, h1, by omega⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨habV, hne, by omega, h2⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨habV, hne, by omega, by omega⟩))
    · rintro (⟨h, hne, _⟩ | ⟨h, hne, _⟩ | ⟨h, hne, _⟩ | ⟨h, hne, _⟩) <;> exact ⟨h, hne⟩
  have hd_BZ : Disjoint BwdPairs C.ZeroOrd := by
    rw [Finset.disjoint_left]; intro q h1 h2
    have a1 := (Finset.mem_filter.1 h1).2.2.2; have a2 := (Finset.mem_filter.1 h2).2.2.2; omega
  have hd_FBZ : Disjoint FwdPairs (BwdPairs ∪ C.ZeroOrd) := by
    rw [Finset.disjoint_left]; intro q h1 h2
    have a1 := (Finset.mem_filter.1 h1).2.2.1
    rcases Finset.mem_union.1 h2 with h | h <;> (have a2 := (Finset.mem_filter.1 h).2.2.1; omega)
  have hd_Hrest : Disjoint HPairs (FwdPairs ∪ (BwdPairs ∪ C.ZeroOrd)) := by
    rw [Finset.disjoint_left]; intro q h1 h2
    have a1 := (Finset.mem_filter.1 h1).2.2.1; have b1 := (Finset.mem_filter.1 h1).2.2.2
    rcases Finset.mem_union.1 h2 with h | h
    · have b2 := (Finset.mem_filter.1 h).2.2.2; omega
    · rcases Finset.mem_union.1 h with h | h <;> (have a2 := (Finset.mem_filter.1 h).2.2.1; omega)
  have htotal : OffV.card = HPairs.card + FwdPairs.card + BwdPairs.card + C.ZeroOrd.card := by
    rw [hOff_eq, Finset.card_union_of_disjoint hd_Hrest, Finset.card_union_of_disjoint hd_FBZ,
        Finset.card_union_of_disjoint hd_BZ]; omega
  rw [hOff_card, hH_card, hBwd_card, hFwd_card] at htotal
  have hsum_deg : ∑ v ∈ C.V, ((C.Utop v).card + (C.NH v).card + (OutA v).card) = C.V.card * k := by
    rw [Finset.sum_congr rfl (fun v hv => hdeg_sum v hv), Finset.sum_const, smul_eq_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum_deg
  have hsum_rhs : ∑ v ∈ C.V, ((C.NH v).card + 2 * (C.Utop v).card) =
      (∑ v ∈ C.V, (C.NH v).card) + 2 * ∑ v ∈ C.V, (C.Utop v).card := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsum_rhs]
  have hV_le : C.V.card ≤ C.V.card * C.V.card := Nat.le_mul_self C.V.card
  have hU_eq : C.V.card * C.U.card + C.V.card * C.V.card = 2 * (C.V.card * k) + C.V.card := by
    rw [← Nat.mul_add, Nat.add_comm C.U.card C.V.card, C.VU_card, Nat.mul_add, Nat.mul_one,
        ← Nat.mul_assoc, Nat.mul_comm C.V.card 2, Nat.mul_assoc]
  omega

private lemma T2_step5_obstruct {a1 b1 a2 b2 c : Fin (2 * k + 1)}
    (ha1 : a1 ∈ C.V) (hb1 : b1 ∈ C.V) (ha2 : a2 ∈ C.V) (hb2 : b2 ∈ C.V) (hc : c ∈ C.U)
    (h12 : a1 ≠ b1) (h13 : a1 ≠ a2) (h14 : a1 ≠ b2) (h23 : b1 ≠ a2) (h24 : b1 ≠ b2) (h34 : a2 ≠ b2)
    (hrb1a2 : C.p.partnerRank b1 a2 ≤ k)
    (hpm : C.HasHPM ((((C.V.erase a1).erase b1).erase a2).erase b2)) :
    (C.p.partnerRank a1 c = k + 1 ∧ C.p.partnerRank c a1 + k ≤ C.p.partnerRank c b2) ∨
    (C.p.partnerRank a1 a2 ≤ k + 1 ∧ C.p.partnerRank a2 a1 + k ≤ C.p.partnerRank a2 b1) ∨
    (C.p.partnerRank a1 b2 ≤ k + 1 ∧ C.p.partnerRank b2 a1 + k ≤ C.p.partnerRank b2 c) ∨
    (C.p.partnerRank a2 b2 + k ≤ C.p.partnerRank a2 b1 ∧ C.p.partnerRank b2 a2 + k ≤ C.p.partnerRank b2 c) := by
  rcases hpm with ⟨g, hginv, hgsupp, hgin⟩
  let W := (((C.V.erase a1).erase b1).erase a2).erase b2
  have hc_ne : ∀ v ∈ C.V, v ≠ c := fun v hv h => Finset.disjoint_left.1 C.VU_disj hv (h ▸ hc)
  have hb1c := hc_ne b1 hb1; have ha2c := hc_ne a2 ha2; have hb2c := hc_ne b2 hb2; have ha1c := hc_ne a1 ha1
  let S4 : Finset (Fin (2 * k + 1)) := {b1, a2, b2, c}
  have hs4 := swap4_spec h24 hb1c h34 ha2c
  have hdisj : Disjoint S4 W := by
    rw [Finset.disjoint_left]; intro z hz1 hz2
    simp only [S4, Finset.mem_insert, Finset.mem_singleton] at hz1
    simp only [W, Finset.mem_erase] at hz2
    rcases hz1 with rfl | rfl | rfl | rfl
    · exact hz2.2.2.1 rfl
    · exact hz2.2.1 rfl
    · exact hz2.1 rfl
    · exact Finset.disjoint_left.1 C.VU_disj hz2.2.2.2.2 hc
  have hgl := glue_involution hdisj hs4.1 hs4.2.2.2.2.2 hginv hgsupp
  let μV := glue S4 (swap4 b1 a2 b2 c) g
  have hμ_b1 : μV b1 = a2 := by dsimp only [μV]; rw [hgl.2.1 b1 (by simp [S4])]; exact hs4.2.1
  have hμ_a2 : μV a2 = b1 := by dsimp only [μV]; rw [hgl.2.1 a2 (by simp [S4])]; exact hs4.2.2.1
  have hμ_b2 : μV b2 = c := by dsimp only [μV]; rw [hgl.2.1 b2 (by simp [S4])]; exact hs4.2.2.2.1
  have hμ_c : μV c = b2 := by dsimp only [μV]; rw [hgl.2.1 c (by simp [S4])]; exact hs4.2.2.2.2.1
  have hμ_a1 : μV a1 = a1 := hgl.2.2.2 a1 (by simp [S4, W, h12, h13, h14, ha1c])
  have hμ_W : ∀ w ∈ W, μV w = g w := hgl.2.2.1
  have hμ_supp : ∀ z, z ∉ insert c C.V → μV z = z := by
    intro z hz; apply hgl.2.2.2
    simp only [Finset.mem_union, S4, W, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase, not_or] at hz ⊢
    exact ⟨⟨fun h => hz.2 (h ▸ hb1), fun h => hz.2 (h ▸ ha2), fun h => hz.2 (h ▸ hb2), hz.1⟩, fun h => hz.2 h.2.2.2.2⟩
  have hμ_w : ∀ w ∈ C.V.erase a1, μV w ∈ insert c C.V ∧ μV w ≠ w := by
    intro w hw; rcases Finset.mem_erase.1 hw with ⟨hwa1, hwV⟩
    by_cases h1 : w = b1; · rw [h1, hμ_b1]; exact ⟨Finset.mem_insert_of_mem ha2, h23.symm⟩
    by_cases h2 : w = a2; · rw [h2, hμ_a2]; exact ⟨Finset.mem_insert_of_mem hb1, h23⟩
    by_cases h3 : w = b2; · rw [h3, hμ_b2]; exact ⟨Finset.mem_insert_self _ _, hb2c.symm⟩
    · have hwW : w ∈ W := Finset.mem_erase.2 ⟨h3, Finset.mem_erase.2 ⟨h2, Finset.mem_erase.2 ⟨h1, Finset.mem_erase.2 ⟨hwa1, hwV⟩⟩⟩⟩
      rw [hμ_W w hwW]; have hgw := hgin w hwW
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_erase.1 (Finset.mem_erase.1 (Finset.mem_erase.1 (Finset.mem_erase.1 hgw.1).2).2).2).2, hgw.2.1.symm⟩
  rcases C.clean_Vc (μV := μV) hc ha1 hgl.1 hμ_supp hμ_a1 (by rw [hμ_c]; exact hb2) hμ_w with
    ⟨i, hi, j, hj, hij_ne, hμij, h1, h2⟩
  have hnot_imm : ∀ x ∈ insert c C.V, ∀ y,
      C.p.partnerRank x y + k ≤ C.p.partnerRank x (μV x) → x = a1 ∨ x = a2 ∨ x = b2 ∨ x = c := by
    intro x hx y hle; by_contra h; push Not at h
    by_cases hxb1 : x = b1
    · rw [hxb1, hμ_b1] at hle; have := partnerRank_pos C.p b1 y; omega
    · have hxV := (Finset.mem_insert.1 hx).resolve_left h.2.2.2
      have hxW : x ∈ W := Finset.mem_erase.2 ⟨h.2.2.1, Finset.mem_erase.2 ⟨h.2.1, Finset.mem_erase.2 ⟨hxb1, Finset.mem_erase.2 ⟨h.1, hxV⟩⟩⟩⟩
      rw [hμ_W x hxW] at hle; have := (hgin x hxW).2.2.1; have := partnerRank_pos C.p x y; omega
  have hi4 := hnot_imm i hi j h1; have hj4 := hnot_imm j hj i h2
  have hno_a2c : ¬ (C.p.partnerRank a2 c + k ≤ C.p.partnerRank a2 b1 ∧ C.p.partnerRank c a2 + k ≤ C.p.partnerRank c b2) := by
    rintro ⟨ha, hc'⟩
    have r1 : C.p.partnerRank a2 b1 ≤ 2 * k := by have := partnerRank_lt_of_ne C.p h23; omega
    have r2 : C.p.partnerRank c b2 ≤ 2 * k := by have := partnerRank_lt_of_ne C.p hb2c; omega
    exact C.no_H_VU ha2 hc ⟨ha2c, by omega, by omega⟩
  have ha1c_blk : C.p.partnerRank a1 c + k ≤ C.p.partnerRank a1 a1 →
      C.p.partnerRank c a1 + k ≤ C.p.partnerRank c b2 →
      C.p.partnerRank a1 c = k + 1 ∧ C.p.partnerRank c a1 + k ≤ C.p.partnerRank c b2 := by
    intro h_1 h_2; rw [C.p.partnerRank_self a1] at h_1
    have r2 : C.p.partnerRank c b2 ≤ 2 * k := by have := partnerRank_lt_of_ne C.p hb2c; omega
    have hrca1 : C.p.partnerRank c a1 ≤ k := by omega
    have hra1c : k + 1 ≤ C.p.partnerRank a1 c := by by_contra hlt; exact C.no_H_VU ha1 hc ⟨ha1c, by omega, hrca1⟩
    exact ⟨by omega, h_2⟩
  rcases hi4 with rfl | rfl | rfl | rfl <;> rcases hj4 with rfl | rfl | rfl | rfl
  · exact False.elim (hij_ne rfl)
  · rw [hμ_a1, C.p.partnerRank_self _] at h1; rw [hμ_a2] at h2; exact Or.inr (Or.inl ⟨by omega, h2⟩)
  · rw [hμ_a1, C.p.partnerRank_self _] at h1; rw [hμ_b2] at h2; exact Or.inr (Or.inr (Or.inl ⟨by omega, h2⟩))
  · rw [hμ_a1] at h1; rw [hμ_c] at h2; exact Or.inl (ha1c_blk h1 h2)
  · rw [hμ_a2] at h1; rw [hμ_a1, C.p.partnerRank_self _] at h2; exact Or.inr (Or.inl ⟨by omega, h1⟩)
  · exact False.elim (hij_ne rfl)
  · rw [hμ_a2] at h1; rw [hμ_b2] at h2; exact Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))
  · rw [hμ_a2] at h1; rw [hμ_c] at h2; exact False.elim (hno_a2c ⟨h1, h2⟩)
  · rw [hμ_b2] at h1; rw [hμ_a1, C.p.partnerRank_self _] at h2; exact Or.inr (Or.inr (Or.inl ⟨by omega, h1⟩))
  · rw [hμ_b2] at h1; rw [hμ_a2] at h2; exact Or.inr (Or.inr (Or.inr ⟨h2, h1⟩))
  · exact False.elim (hij_ne rfl)
  · rw [hμ_b2] at hμij; exact False.elim (hμij rfl)
  · rw [hμ_c] at h1; rw [hμ_a1] at h2; exact Or.inl (ha1c_blk h2 h1)
  · rw [hμ_c] at h1; rw [hμ_a2] at h2; exact False.elim (hno_a2c ⟨h2, h1⟩)
  · rw [hμ_c] at hμij; exact False.elim (hμij rfl)
  · exact False.elim (hij_ne rfl)

private lemma pm_erase_four_case2 {a2 b1 u1 u2} (ha2V : a2 ∈ C.V) (hb1V : b1 ∈ C.V)
    (hu1V : u1 ∈ C.V) (hu2V : u2 ∈ C.V)
    (hb1_ne_a2 : b1 ≠ a2) (hu1u2 : u1 ≠ u2)
    (hno_a2b1 : ¬ C.Hadj a2 b1) (hno_u1u2 : ¬ C.Hadj u1 u2)
    (ha2u1 : C.Hadj a2 u1) (ha2u2 : C.Hadj a2 u2)
    (hb1u1 : C.Hadj b1 u1) (hb1u2 : C.Hadj b1 u2) :
    C.HasHPM ((((C.V.erase u2).erase b1).erase a2).erase u1) := by
  let W4 := (((C.V.erase u2).erase b1).erase a2).erase u1
  let X : Finset (Fin (2 * k + 1)) := {a2, b1}
  let Y : Finset (Fin (2 * k + 1)) := {u1, u2}
  let LA : Finset (Fin (2 * k + 1)) := ({C.M.val u1, C.M.val u2} : Finset _) \ X
  let LB : Finset (Fin (2 * k + 1)) := ({C.M.val a2, C.M.val b1} : Finset _) \ Y
  have hL_adj : ∀ px ∈ LA, ∀ qx ∈ LB, C.Hadj px qx := by
    intro px hpx qx hqx
    have hp1 := (Finset.mem_sdiff.1 hpx).1; have hq1 := (Finset.mem_sdiff.1 hqx).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp1 hq1
    rcases hp1 with rfl | rfl <;> rcases hq1 with rfl | rfl
    · exact C.swap_adj hu1V ha2V (C.Hadj_symm ha2u1)
    · exact C.swap_adj hu1V hb1V (C.Hadj_symm hb1u1)
    · exact C.swap_adj hu2V ha2V (C.Hadj_symm ha2u2)
    · exact C.swap_adj hu2V hb1V (C.Hadj_symm hb1u2)
  have hL_disj : Disjoint LA LB := by
    rw [Finset.disjoint_left]; intro z hz1 hz2; exact (hL_adj z hz1 z hz2).1 rfl
  have hL_sub_W4 : LA ∪ LB ⊆ W4 := by
    intro z hz
    have hmemW4 : ∀ z ∈ C.V, z ∉ X → z ∉ Y → z ∈ W4 := by
      intro z hzV hzX hzY
      simp only [X, Y, Finset.mem_insert, Finset.mem_singleton, not_or] at hzX hzY
      exact Finset.mem_erase.2 ⟨hzY.1, Finset.mem_erase.2 ⟨hzX.1, Finset.mem_erase.2 ⟨hzX.2, Finset.mem_erase.2 ⟨hzY.2, hzV⟩⟩⟩⟩
    rcases Finset.mem_union.1 hz with hzA | hzB
    · have h1 := (Finset.mem_sdiff.1 hzA).1; have hzX := (Finset.mem_sdiff.1 hzA).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      have hzV : z ∈ C.V := by rcases h1 with rfl | rfl; exact (C.M_in_V hu1V).1; exact (C.M_in_V hu2V).1
      have hzY : z ∉ Y := by
        intro hy; simp only [Y, Finset.mem_insert, Finset.mem_singleton] at hy
        rcases h1 with rfl | rfl <;> rcases hy with heq | heq
        · exact (C.M_in_V hu1V).2.1 heq
        · exact hno_u1u2 (heq ▸ (C.M_in_V hu1V).2.2)
        · exact hno_u1u2 (C.Hadj_symm (heq ▸ (C.M_in_V hu2V).2.2))
        · exact (C.M_in_V hu2V).2.1 heq
      exact hmemW4 z hzV hzX hzY
    · have h1 := (Finset.mem_sdiff.1 hzB).1; have hzY := (Finset.mem_sdiff.1 hzB).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      have hzV : z ∈ C.V := by rcases h1 with rfl | rfl; exact (C.M_in_V ha2V).1; exact (C.M_in_V hb1V).1
      have hzX : z ∉ X := by
        intro hx; simp only [X, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases h1 with rfl | rfl <;> rcases hx with heq | heq
        · exact (C.M_in_V ha2V).2.1 heq
        · exact hno_a2b1 (heq ▸ (C.M_in_V ha2V).2.2)
        · exact hno_a2b1 (C.Hadj_symm (heq ▸ (C.M_in_V hb1V).2.2))
        · exact (C.M_in_V hb1V).2.1 heq
      exact hmemW4 z hzV hzX hzY
  have hLA_eq_LB : LA.card = LB.card := by
    have hcardA : ({C.M.val u1, C.M.val u2} : Finset _).card = 2 :=
      Finset.card_pair (fun h => hu1u2 (C.M.property.injective h))
    have hcardB : ({C.M.val a2, C.M.val b1} : Finset _).card = 2 :=
      Finset.card_pair (fun h => hb1_ne_a2.symm (C.M.property.injective h))
    have hbij : (({C.M.val u1, C.M.val u2} : Finset _) ∩ X).card =
        (({C.M.val a2, C.M.val b1} : Finset _) ∩ Y).card := by
      refine Finset.card_bij (fun z _ => C.M.val z) ?_ ?_ ?_
      · intro z hz; rcases Finset.mem_inter.1 hz with ⟨h1, h2⟩
        simp only [X, Y, Finset.mem_insert, Finset.mem_singleton, Finset.mem_inter] at h1 h2 ⊢
        constructor
        · rcases h2 with rfl | rfl <;> simp
        · rcases h1 with rfl | rfl <;> simp [C.M.property u1, C.M.property u2]
      · intro _ _ _ _ h; exact C.M.property.injective h
      · intro z hz; rcases Finset.mem_inter.1 hz with ⟨h1, h2⟩
        refine ⟨C.M.val z, ?_, C.M.property z⟩
        simp only [X, Y, Finset.mem_insert, Finset.mem_singleton, Finset.mem_inter] at h1 h2 ⊢
        constructor
        · rcases h2 with rfl | rfl <;> simp
        · rcases h1 with rfl | rfl <;> simp [C.M.property a2, C.M.property b1]
    have h1 := Finset.card_sdiff_add_card_inter ({C.M.val u1, C.M.val u2} : Finset _) X
    have h2 := Finset.card_sdiff_add_card_inter ({C.M.val a2, C.M.val b1} : Finset _) Y
    dsimp only [LA, LB]; omega
  let e : LA ≃ LB := Fintype.equivOfCardEq (by simp [hLA_eq_LB])
  let gL : Fin (2 * k + 1) → Fin (2 * k + 1) := fun z =>
    if hA : z ∈ LA then (e ⟨z, hA⟩).val
    else if hB : z ∈ LB then (e.symm ⟨z, hB⟩).val
    else z
  have hgL_inv : Function.Involutive gL := by
    intro z; simp only [gL]
    by_cases hA : z ∈ LA
    · have heB : (e ⟨z, hA⟩).val ∈ LB := (e ⟨z, hA⟩).property
      have henotA : (e ⟨z, hA⟩).val ∉ LA := Finset.disjoint_right.1 hL_disj heB
      simp [hA, heB, henotA]
    · by_cases hB : z ∈ LB
      · have heA : (e.symm ⟨z, hB⟩).val ∈ LA := (e.symm ⟨z, hB⟩).property
        simp [hA, hB, heA]
      · simp [hA, hB]
  have hgL_supp : ∀ z, z ∉ LA ∪ LB → gL z = z := by
    intro z hz; rw [Finset.mem_union] at hz; push Not at hz; simp [gL, hz.1, hz.2]
  let Wrest := W4 \ (LA ∪ LB)
  have hM_Wrest : ∀ z ∈ Wrest, C.M.val z ∈ Wrest := by
    intro z hz; rcases Finset.mem_sdiff.1 hz with ⟨hzW4, hznotL⟩
    simp only [W4, Finset.mem_erase] at hzW4
    have hzV := hzW4.2.2.2.2; have hMzV := (C.M_in_V hzV).1
    have hnotA : z ∉ LA := fun h => hznotL (Finset.mem_union_left _ h)
    have hnotB : z ∉ LB := fun h => hznotL (Finset.mem_union_right _ h)
    have hzX : z ∉ X := by simp [X, hzW4.2.1, hzW4.2.2.1]
    have hzY : z ∉ Y := by simp [Y, hzW4.1, hzW4.2.2.2.1]
    have hMzW4 : C.M.val z ∈ W4 := Finset.mem_erase.2
      ⟨fun h => hnotA (Finset.mem_sdiff.2 ⟨by simp [← h, C.M.property z], hzX⟩),
       Finset.mem_erase.2 ⟨fun h => hnotB (Finset.mem_sdiff.2 ⟨by simp [← h, C.M.property z], hzY⟩),
       Finset.mem_erase.2 ⟨fun h => hnotB (Finset.mem_sdiff.2 ⟨by simp [← h, C.M.property z], hzY⟩),
       Finset.mem_erase.2 ⟨fun h => hnotA (Finset.mem_sdiff.2 ⟨by simp [← h, C.M.property z], hzX⟩), hMzV⟩⟩⟩⟩
    refine Finset.mem_sdiff.2 ⟨hMzW4, ?_⟩
    intro hMzL; rcases Finset.mem_union.1 hMzL with hMzA | hMzB
    · have h1 := (Finset.mem_sdiff.1 hMzA).1; simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      rcases h1 with heq | heq
      · exact hzW4.1 (C.M.property.injective heq)
      · exact hzW4.2.2.2.1 (C.M.property.injective heq)
    · have h1 := (Finset.mem_sdiff.1 hMzB).1; simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      rcases h1 with heq | heq
      · exact hzW4.2.1 (C.M.property.injective heq)
      · exact hzW4.2.2.1 (C.M.property.injective heq)
  have hres := restrict_inv C.M.property hM_Wrest
  have hd_LW : Disjoint (LA ∪ LB) Wrest := Finset.disjoint_sdiff
  have hgl4 := glue_involution hd_LW hgL_inv hgL_supp hres.1 hres.2.2
  have hunion4 : (LA ∪ LB) ∪ Wrest = W4 := Finset.union_sdiff_of_subset hL_sub_W4
  refine ⟨glue (LA ∪ LB) gL (restrictTo Wrest C.M.val),
    hgl4.1, fun z hz => hgl4.2.2.2 z (hunion4.symm ▸ hz), ?_⟩
  intro z hzW4
  by_cases hzL : z ∈ LA ∪ LB
  · rw [hgl4.2.1 z hzL]
    rcases Finset.mem_union.1 hzL with hA | hB
    · simp only [gL, dif_pos hA]
      exact ⟨hL_sub_W4 (Finset.mem_union_right _ (e ⟨z, hA⟩).property), hL_adj z hA _ (e ⟨z, hA⟩).property⟩
    · have hnotA : z ∉ LA := Finset.disjoint_right.1 hL_disj hB
      simp only [gL, dif_neg hnotA, dif_pos hB]
      exact ⟨hL_sub_W4 (Finset.mem_union_left _ (e.symm ⟨z, hB⟩).property), C.Hadj_symm (hL_adj _ (e.symm ⟨z, hB⟩).property z hB)⟩
  · have hzR : z ∈ Wrest := Finset.mem_sdiff.2 ⟨hzW4, hzL⟩
    rw [hgl4.2.2.1 z hzR, hres.2.1 z hzR]
    have hzV := (Finset.mem_erase.1 (Finset.mem_erase.1 (Finset.mem_erase.1 (Finset.mem_erase.1 hzW4).2).2).2).2
    exact ⟨Finset.sdiff_subset (hM_Wrest z hzR), (C.M_in_V hzV).2.2⟩

private lemma pm_erase_four_case1 {b1 a2 b2} (_hb1V : b1 ∈ C.V) (ha2V : a2 ∈ C.V) (hb2V : b2 ∈ C.V)
    (hb1_ne_a2 : b1 ≠ a2) (hb1b2 : b1 ≠ b2) (ha2b2 : C.Hadj a2 b2)
    (hno_a2b1 : ¬ C.Hadj a2 b1) (hno_Ma2b1 : ¬ C.Hadj (C.M.val a2) b1) :
    C.HasHPM ((((C.V.erase (C.M.val b1)).erase b1).erase a2).erase b2) := by
  let a1 := C.M.val b1
  have hb1_ne_Ma2 : b1 ≠ C.M.val a2 := fun h => hno_a2b1 (h ▸ (C.M_in_V ha2V).2.2)
  have ha1_ne_Ma2 : a1 ≠ C.M.val a2 := fun h => hb1_ne_a2 (C.M.property.injective h)
  have hb1_ne_Mb2 : b1 ≠ C.M.val b2 := fun h => hno_Ma2b1 (h ▸ C.swap_adj ha2V hb2V ha2b2)
  have ha1_ne_Mb2 : a1 ≠ C.M.val b2 := fun h => hb1b2 (C.M.property.injective h)
  let W := (((C.V.erase a1).erase b1).erase a2).erase b2
  by_cases hbm : b2 = C.M.val a2
  · have hMW : ∀ z ∈ W, C.M.val z ∈ W := by
      intro z hz; simp only [W, Finset.mem_erase] at hz ⊢
      refine ⟨fun h => hz.2.1 (by rw [hbm] at h; exact C.M.property.injective h),
              fun h => hz.1 (by rw [hbm, ← h, C.M.property z]),
              fun h => hz.2.2.2.1 (by dsimp only [a1]; rw [← h, C.M.property z]),
              fun h => hz.2.2.1 (C.M.property.injective h),
              (C.M_in_V hz.2.2.2.2).1⟩
    have hres := restrict_inv C.M.property hMW
    exact ⟨restrictTo W C.M.val, hres.1, hres.2.2,
      fun z hz => by rw [hres.2.1 z hz]; exact ⟨hMW z hz, (C.M_in_V (Finset.mem_erase.1 (Finset.mem_erase.1 (Finset.mem_erase.1 (Finset.mem_erase.1 hz).2).2).2).2).2.2⟩⟩
  · have hMa2Mb2 := C.swap_adj ha2V hb2V ha2b2
    have hMa2_in : C.M.val a2 ∈ W := Finset.mem_erase.2 ⟨Ne.symm hbm, Finset.mem_erase.2 ⟨(C.M_in_V ha2V).2.1, Finset.mem_erase.2 ⟨hb1_ne_Ma2.symm, Finset.mem_erase.2 ⟨ha1_ne_Ma2.symm, (C.M_in_V ha2V).1⟩⟩⟩⟩
    have hMb2_in : C.M.val b2 ∈ W := Finset.mem_erase.2 ⟨(C.M_in_V hb2V).2.1, Finset.mem_erase.2 ⟨fun h => hbm (by rw [← C.M.property b2, h]), Finset.mem_erase.2 ⟨hb1_ne_Mb2.symm, Finset.mem_erase.2 ⟨ha1_ne_Mb2.symm, (C.M_in_V hb2V).1⟩⟩⟩⟩
    let W' := (W.erase (C.M.val a2)).erase (C.M.val b2)
    have hMW' : ∀ z ∈ W', C.M.val z ∈ W' := by
      intro z hz; simp only [W', W, Finset.mem_erase] at hz ⊢
      refine ⟨fun h => hz.2.2.1 (C.M.property.injective h),
              fun h => hz.2.2.2.1 (C.M.property.injective h),
              fun h => hz.1 (by rw [← h, C.M.property z]),
              fun h => hz.2.1 (by rw [← h, C.M.property z]),
              fun h => hz.2.2.2.2.2.1 (by dsimp only [a1]; rw [← h, C.M.property z]),
              fun h => hz.2.2.2.2.1 (C.M.property.injective h),
              (C.M_in_V hz.2.2.2.2.2.2).1⟩
    have hres := restrict_inv C.M.property hMW'
    have hd : Disjoint ({C.M.val a2, C.M.val b2} : Finset _) W' := by
      rw [Finset.disjoint_left]; intro z hz1 hz2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz1
      simp only [W', Finset.mem_erase] at hz2
      rcases hz1 with rfl | rfl; exact hz2.2.1 rfl; exact hz2.1 rfl
    have hgl := glue_involution hd (swap2_inv (C.M.val a2) (C.M.val b2)) (swap2_supp _ _) hres.1 hres.2.2
    have hunion : ({C.M.val a2, C.M.val b2} : Finset _) ∪ W' = W := by
      ext z; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, W', Finset.mem_erase]
      constructor
      · rintro ((rfl | rfl) | ⟨_, _, hzW⟩); exact hMa2_in; exact hMb2_in; exact hzW
      · intro hzW
        by_cases h1 : z = C.M.val a2; · exact Or.inl (Or.inl h1)
        by_cases h2 : z = C.M.val b2; · exact Or.inl (Or.inr h2)
        · exact Or.inr ⟨h2, h1, hzW⟩
    let g := glue ({C.M.val a2, C.M.val b2} : Finset _) (swap2 (C.M.val a2) (C.M.val b2)) (restrictTo W' C.M.val)
    refine ⟨g, hgl.1, fun z hz => hgl.2.2.2 z (hunion.symm ▸ hz), ?_⟩
    intro z hzW
    by_cases h1 : z = C.M.val a2
    · rw [h1]; dsimp only [g]; rw [hgl.2.1 (C.M.val a2) (by simp), swap2_left]; exact ⟨hMb2_in, hMa2Mb2⟩
    by_cases h2 : z = C.M.val b2
    · rw [h2]; dsimp only [g]; rw [hgl.2.1 (C.M.val b2) (by simp), swap2_right]; exact ⟨hMa2_in, C.Hadj_symm hMa2Mb2⟩
    · have hzW' : z ∈ W' := Finset.mem_erase.2 ⟨h2, Finset.mem_erase.2 ⟨h1, hzW⟩⟩
      dsimp only [g]; rw [hgl.2.2.1 z hzW', hres.2.1 z hzW']
      exact ⟨(Finset.mem_erase.1 (Finset.mem_erase.1 (hMW' z hzW')).2).2,
        (C.M_in_V (Finset.mem_erase.1 (Finset.mem_erase.1 (Finset.mem_erase.1 (Finset.mem_erase.1 hzW).2).2).2).2).2.2⟩

private lemma step6_G_prop {a2 b1 u1 u2 : Fin (2 * k + 1)}
    (ha2V : a2 ∈ C.V) (hda2 : 2 ≤ (C.NH a2).card)
    (hb1V : b1 ∈ C.V) (hb1_ne_a2 : b1 ≠ a2) (hno_a2b1 : ¬ C.Hadj a2 b1)
    (hrb1a2 : C.p.partnerRank b1 a2 ≤ k)
    (hu1V : u1 ∈ C.V) (hu2V : u2 ∈ C.V)
    (ha2u1 : C.Hadj a2 u1) (ha2u2 : C.Hadj a2 u2)
    (hu1u2 : u1 ≠ u2) (hra2_u2_u1 : C.p.partnerRank a2 u2 < C.p.partnerRank a2 u1)
    (hra2b1_lt : C.p.partnerRank a2 b1 < C.p.partnerRank a2 u2 + k) :
    ¬ C.Hadj (C.M.val a2) b1 ∧
    C.p.partnerRank (C.M.val b1) a2 = k + 1 ∧
    C.p.partnerRank a2 (C.M.val b1) < C.p.partnerRank a2 u2 := by
  have hdu1 := C.deg_ge2_adj ha2V hu1V ha2u1 hda2
  have hdu2 := C.deg_ge2_adj ha2V hu2V ha2u2 hda2
  have hb1_ne_u1 : b1 ≠ u1 := fun h => hno_a2b1 (h ▸ ha2u1)
  have hb1_ne_u2 : b1 ≠ u2 := fun h => hno_a2b1 (h ▸ ha2u2)
  have hno_Ma2b1 : ¬ C.Hadj (C.M.val a2) b1 := by
    intro hMa2b1
    have hno_u1u2 : ¬ C.Hadj u1 u2 := by
      intro hu1u2_adj
      by_cases hu2m : u2 = C.M.val a2
      · exact hno_a2b1 (C.clique_step ha2V hu1V hb1V ha2u1 (hu2m ▸ C.Hadj_symm hu1u2_adj) hMa2b1 hb1_ne_a2)
      · have hMa2Mu2 := C.swap_adj ha2V hu2V ha2u2
        have ha2Mu2 : C.Hadj a2 (C.M.val u2) := by
          have h1 : C.Hadj (C.M.val (C.M.val a2)) u1 := by rwa [C.M.property a2]
          have h2 := C.swap_adj hu1V hu2V hu1u2_adj
          have h3 : C.M.val u2 ≠ C.M.val (C.M.val a2) := fun h => by
            rw [C.M.property a2] at h; exact hu2m (by rw [← C.M.property u2, h])
          have := C.trans_adj (C.M_in_V ha2V).1 hu1V (C.M_in_V hu2V).1 h1 h2 h3
          rwa [C.M.property a2] at this
        exact hno_a2b1 (C.clique_step ha2V (C.M_in_V hu2V).1 hb1V ha2Mu2 hMa2Mu2 hMa2b1 hb1_ne_a2)
    have hb1u1 : C.Hadj b1 u1 := by
      have h1 : C.Hadj (C.M.val (C.M.val b1)) (C.M.val a2) := by rw [C.M.property b1]; exact C.Hadj_symm hMa2b1
      have h2 : C.Hadj (C.M.val (C.M.val a2)) u1 := by rwa [C.M.property a2]
      have h3 : u1 ≠ C.M.val (C.M.val b1) := by rw [C.M.property b1]; exact hb1_ne_u1.symm
      have := C.trans_adj (C.M_in_V hb1V).1 (C.M_in_V ha2V).1 hu1V h1 h2 h3
      rwa [C.M.property b1] at this
    have hb1u2 : C.Hadj b1 u2 := by
      have h1 : C.Hadj (C.M.val (C.M.val b1)) (C.M.val a2) := by rw [C.M.property b1]; exact C.Hadj_symm hMa2b1
      have h2 : C.Hadj (C.M.val (C.M.val a2)) u2 := by rwa [C.M.property a2]
      have h3 : u2 ≠ C.M.val (C.M.val b1) := by rw [C.M.property b1]; exact hb1_ne_u2.symm
      have := C.trans_adj (C.M_in_V hb1V).1 (C.M_in_V ha2V).1 hu2V h1 h2 h3
      rwa [C.M.property b1] at this
    have hpm4 := C.pm_erase_four_case2 ha2V hb1V hu1V hu2V hb1_ne_a2 hu1u2 hno_a2b1 hno_u1u2 ha2u1 ha2u2 hb1u1 hb1u2
    have hge3 := C.U_ge3
    rcases Finset.card_pos.1 (show 0 < C.U.card by omega) with ⟨c0, hc0⟩
    have h1_u1u2 : C.p.partnerRank u1 u2 ≤ k := by
      rcases C.T2_step5_obstruct hu2V hb1V ha2V hu1V hc0 hb1_ne_u2.symm ha2u2.1.symm hu1u2.symm hb1_ne_a2 hb1_ne_u1 ha2u1.1 hrb1a2 hpm4 with
        ⟨hr, _⟩ | ⟨_, hr⟩ | ⟨_, hr⟩ | ⟨hr, _⟩
      · have := C.T4_no_U hu2V hdu2 hc0; omega
      · omega
      · have hc0u1 : c0 ≠ u1 := fun h => Finset.disjoint_left.1 C.VU_disj hu1V (by rw [← h]; exact hc0)
        have hr1c : C.p.partnerRank u1 c0 ≤ 2 * k := by have := partnerRank_lt_of_ne C.p hc0u1; omega
        omega
      · omega
    have hpm4' : C.HasHPM ((((C.V.erase u1).erase b1).erase a2).erase u2) := by
      have heq : ((((C.V.erase u1).erase b1).erase a2).erase u2) = ((((C.V.erase u2).erase b1).erase a2).erase u1) := by
        ext z; simp only [Finset.mem_erase]; tauto
      rwa [heq]
    have h2_u2u1 : C.p.partnerRank u2 u1 ≤ k := by
      rcases C.T2_step5_obstruct hu1V hb1V ha2V hu2V hc0 hb1_ne_u1.symm ha2u1.1.symm hu1u2 hb1_ne_a2 hb1_ne_u2 ha2u2.1 hrb1a2 hpm4' with
        ⟨hr, _⟩ | ⟨_, hr⟩ | ⟨_, hr⟩ | ⟨hr, _⟩
      · have := C.T4_no_U hu1V hdu1 hc0; omega
      · omega
      · have hc0u2 : c0 ≠ u2 := fun h => Finset.disjoint_left.1 C.VU_disj hu2V (by rw [← h]; exact hc0)
        have hr2c : C.p.partnerRank u2 c0 ≤ 2 * k := by have := partnerRank_lt_of_ne C.p hc0u2; omega
        omega
      · omega
    exact hno_u1u2 ⟨hu1u2, h1_u1u2, h2_u2u1⟩
  have ha1V : C.M.val b1 ∈ C.V := (C.M_in_V hb1V).1
  have ha1_ne_b1 : C.M.val b1 ≠ b1 := (C.M_in_V hb1V).2.1
  have ha1_ne_a2 : C.M.val b1 ≠ a2 := fun h => hno_a2b1 (C.Hadj_symm (h ▸ (C.M_in_V hb1V).2.2))
  have hno_a1a2 : ¬ C.Hadj (C.M.val b1) a2 := fun h => hno_Ma2b1 (by
    have := C.swap_adj ha1V ha2V h; rw [C.M.property b1] at this; exact C.Hadj_symm this)
  have hno_a1u : ∀ u ∈ C.V, C.Hadj a2 u → ¬ C.Hadj (C.M.val b1) u := by
    intro u hu ha2u ha1u
    have h1 := C.swap_adj ha2V hu ha2u
    have h2 : C.Hadj (C.M.val (C.M.val u)) (C.M.val b1) := by rw [C.M.property u]; exact C.Hadj_symm ha1u
    have h3 : C.M.val b1 ≠ C.M.val a2 := fun h => hb1_ne_a2 (C.M.property.injective h)
    have h4 := C.trans_adj ha2V (C.M_in_V hu).1 ha1V h1 h2 h3
    have h5 := C.swap_adj (C.M_in_V ha2V).1 ha1V h4
    rw [C.M.property a2, C.M.property b1] at h5; exact hno_a2b1 h5
  have ha1_ne_u1 : C.M.val b1 ≠ u1 := fun h => hno_a1a2 (h ▸ C.Hadj_symm ha2u1)
  have ha1_ne_u2 : C.M.val b1 ≠ u2 := fun h => hno_a1a2 (h ▸ C.Hadj_symm ha2u2)
  have hex_c : ∃ c ∈ C.U, c ≠ C.f (C.M.val b1) := by
    have hpos : 0 < (C.U.erase (C.f (C.M.val b1))).card := by
      have := Finset.pred_card_le_card_erase (s := C.U) (a := C.f (C.M.val b1)); have := C.U_ge3; omega
    rcases Finset.card_pos.1 hpos with ⟨c, hc⟩; exact ⟨c, (Finset.mem_erase.1 hc).2, (Finset.mem_erase.1 hc).1⟩
  rcases hex_c with ⟨c, hcU, hcfa1⟩
  have hex_b2 : ∃ b2 ∈ C.V, C.Hadj a2 b2 ∧ b1 ≠ b2 ∧ C.M.val b1 ≠ b2 ∧ ¬ C.Hadj (C.M.val b1) b2 ∧
      C.p.partnerRank a2 b1 < C.p.partnerRank a2 b2 + k ∧ b2 ≠ C.f (C.M.val b1) := by
    by_cases h1 : u1 ≠ C.f (C.M.val b1)
    · exact ⟨u1, hu1V, ha2u1, hb1_ne_u1, ha1_ne_u1, hno_a1u u1 hu1V ha2u1, by omega, h1⟩
    · exact ⟨u2, hu2V, ha2u2, hb1_ne_u2, ha1_ne_u2, hno_a1u u2 hu2V ha2u2, hra2b1_lt,
        fun h2 => hu1u2 ((not_ne_iff.1 h1).trans h2.symm)⟩
  rcases hex_b2 with ⟨b2, hb2V, ha2b2, hb1b2, ha1b2, hno_a1b2, hrb1_lt_b2, hb2fa1⟩
  rcases C.T2_step5_obstruct ha1V hb1V ha2V hb2V hcU ha1_ne_b1 ha1_ne_a2 ha1b2 hb1_ne_a2 hb1b2 ha2b2.1 hrb1a2
      (C.pm_erase_four_case1 hb1V ha2V hb2V hb1_ne_a2 hb1b2 ha2b2 hno_a2b1 hno_Ma2b1) with
    ⟨hrc, _⟩ | ⟨hra1a2, hra2a1⟩ | ⟨hra1b2, hrb2a1⟩ | ⟨hrab, _⟩
  · exact False.elim (hcfa1 (C.f_uniq (C.M.val b1) c hrc))
  · have hra2b1_le : C.p.partnerRank a2 b1 ≤ 2 * k := by have := partnerRank_lt_of_ne C.p hb1_ne_a2; omega
    have hra2a1_le : C.p.partnerRank a2 (C.M.val b1) ≤ k := by omega
    have hra1a2_ge : k + 1 ≤ C.p.partnerRank (C.M.val b1) a2 := by by_contra hlt; exact hno_a1a2 ⟨ha1_ne_a2, by omega, hra2a1_le⟩
    exact ⟨hno_Ma2b1, by omega, by omega⟩
  · have hcb2 : c ≠ b2 := fun h => Finset.disjoint_left.1 C.VU_disj hb2V (by rw [← h]; exact hcU)
    have hrb2c : C.p.partnerRank b2 c ≤ 2 * k := by have := partnerRank_lt_of_ne C.p hcb2; omega
    have hrb2a1_le : C.p.partnerRank b2 (C.M.val b1) ≤ k := by omega
    have hra1b2_ge : k + 1 ≤ C.p.partnerRank (C.M.val b1) b2 := by by_contra hlt; exact hno_a1b2 ⟨ha1b2, by omega, hrb2a1_le⟩
    exact False.elim (hb2fa1 (C.f_uniq (C.M.val b1) b2 (by omega)))
  · omega

private lemma V2_empty : C.V.filter (fun v => 2 ≤ (C.NH v).card) = ∅ := by
  let V₂ := C.V.filter (fun v => 2 ≤ (C.NH v).card)
  let V₁ := C.V.filter (fun v => ¬ 2 ≤ (C.NH v).card)
  change V₂ = ∅
  by_contra hV2_ne
  have hV2_pos : 0 < V₂.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hV2_ne)
  have hex_w12 : ∀ v ∈ V₂, ∃ w₁ w₂, w₁ ∈ C.NH v ∧ w₂ ∈ C.NH v ∧ w₁ ≠ w₂ ∧
      C.p.partnerRank v w₂ < C.p.partnerRank v w₁ ∧
      (∀ w ∈ C.NH v, C.p.partnerRank v w ≤ C.p.partnerRank v w₁) ∧
      (∀ w ∈ C.NH v, w ≠ w₁ → C.p.partnerRank v w ≤ C.p.partnerRank v w₂) := by
    intro v hv2
    have hdv : 2 ≤ (C.NH v).card := (Finset.mem_filter.1 hv2).2
    rcases Finset.exists_max_image (C.NH v) (fun w => C.p.partnerRank v w) (Finset.card_pos.1 (by omega)) with ⟨w₁, hw₁, hw₁max⟩
    have her_ne : ((C.NH v).erase w₁).Nonempty := by have := Finset.card_erase_add_one hw₁; exact Finset.card_pos.1 (by omega)
    rcases Finset.exists_max_image ((C.NH v).erase w₁) (fun w => C.p.partnerRank v w) her_ne with ⟨w₂, hw₂er, hw₂max⟩
    have hw₂ne := (Finset.mem_erase.1 hw₂er).1; have hw₂ := (Finset.mem_erase.1 hw₂er).2
    have hlt : C.p.partnerRank v w₂ < C.p.partnerRank v w₁ := by
      have hle := hw₁max w₂ hw₂
      have hne : C.p.partnerRank v w₂ ≠ C.p.partnerRank v w₁ := fun h => hw₂ne (partnerRank_inj C.p v h)
      omega
    exact ⟨w₁, w₂, hw₁, hw₂, hw₂ne.symm, hlt, hw₁max, fun w hw hne => hw₂max w (Finset.mem_erase.2 ⟨hne, hw⟩)⟩
  let w1 : Fin (2 * k + 1) → Fin (2 * k + 1) := fun v => if h : v ∈ V₂ then Classical.choose (hex_w12 v h) else v
  let w2 : Fin (2 * k + 1) → Fin (2 * k + 1) := fun v => if h : v ∈ V₂ then Classical.choose (Classical.choose_spec (hex_w12 v h)) else v
  have hw12 : ∀ {v}, v ∈ V₂ →
      w1 v ∈ C.NH v ∧ w2 v ∈ C.NH v ∧ w1 v ≠ w2 v ∧
      C.p.partnerRank v (w2 v) < C.p.partnerRank v (w1 v) ∧
      (∀ w ∈ C.NH v, C.p.partnerRank v w ≤ C.p.partnerRank v (w1 v)) ∧
      (∀ w ∈ C.NH v, w ≠ w1 v → C.p.partnerRank v w ≤ C.p.partnerRank v (w2 v)) := by
    intro v hv; simp only [w1, w2, dif_pos hv]; exact Classical.choose_spec (Classical.choose_spec (hex_w12 v hv))
  have hr2_ge : ∀ v ∈ V₂, (C.NH v).card - 1 ≤ C.p.partnerRank v (w2 v) := by
    intro v hv; have hspec := hw12 hv
    have hsub : (C.NH v).erase (w1 v) ⊆ Finset.univ.filter (fun w => C.p.partnerRank v w ≤ C.p.partnerRank v (w2 v)) := by
      intro w hw; rcases Finset.mem_erase.1 hw with ⟨hne, hwNH⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hspec.2.2.2.2.2 w hwNH hne⟩
    have hle := Finset.card_le_card hsub
    rw [card_partnerRank_le C.p v _ (C.p.partnerRank_le v _)] at hle
    have her := Finset.card_erase_add_one hspec.1; omega
  let I2 : Fin (2 * k + 1) → Finset (Fin (2 * k + 1)) := fun v =>
    Finset.univ.filter (fun x => k + 1 ≤ C.p.partnerRank v x ∧ C.p.partnerRank v x < C.p.partnerRank v (w2 v) + k)
  have hI2_card : ∀ v ∈ V₂, (I2 v).card = C.p.partnerRank v (w2 v) - 1 := by
    intro v hv; have hspec := hw12 hv
    have hw1_le : C.p.partnerRank v (w1 v) ≤ k := (Finset.mem_filter.1 hspec.1).2.2.1
    have hw2_pos := partnerRank_pos C.p v (w2 v)
    have h := card_partnerRank_Ico C.p v (k + 1) (C.p.partnerRank v (w2 v) + k) (by omega) (by omega) (by omega)
    change (I2 v).card = _ at h; omega
  have hI2_sub_V : ∀ {v x}, v ∈ V₂ → x ∈ I2 v → x ∈ C.V ∧ x ≠ v ∧ ¬ C.Hadj v x := by
    intro v x hv hx
    have hvV := (Finset.mem_filter.1 hv).1; have hdv := (Finset.mem_filter.1 hv).2; have hspec := hw12 hv
    have hx1 := (Finset.mem_filter.1 hx).2.1; have hx2 := (Finset.mem_filter.1 hx).2.2
    have hxw1 : C.p.partnerRank v (w1 v) ≤ k := (Finset.mem_filter.1 hspec.1).2.2.1
    have hxne : x ≠ v := fun h => by rw [h, C.p.partnerRank_self v] at hx2; omega
    have hxV : x ∈ C.V := by
      rcases C.mem_V_or_U x with h | hxU; · exact h
      · have := C.T4_rank hvV hdv hspec.1 hxU; omega
    exact ⟨hxV, hxne, fun h => by have := h.2.1; omega⟩
  let G : Finset (Fin (2 * k + 1) × Fin (2 * k + 1)) :=
    (V₂ ×ˢ C.V).filter (fun q => q.2 ∈ I2 q.1 ∧ C.p.partnerRank q.2 q.1 ≤ k)
  let P0 : Finset (Fin (2 * k + 1) × Fin (2 * k + 1)) :=
    (V₂ ×ˢ C.V).filter (fun q => q.2 ∈ I2 q.1 ∧ k + 1 ≤ C.p.partnerRank q.2 q.1)
  have hGP0_sum : G.card + P0.card = ∑ v ∈ V₂, (C.p.partnerRank v (w2 v) - 1) := by
    have hdisj : Disjoint G P0 := by
      rw [Finset.disjoint_left]; intro q h1 h2
      have a1 := (Finset.mem_filter.1 h1).2.2; have a2 := (Finset.mem_filter.1 h2).2.2; omega
    have hunion : G ∪ P0 = V₂.biUnion (fun v => (I2 v).image (fun b => (v, b))) := by
      ext ⟨a, b⟩; simp only [G, P0, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro (⟨⟨ha, _⟩, hbI, _⟩ | ⟨⟨ha, _⟩, hbI, _⟩) <;> exact ⟨a, ha, b, hbI, rfl⟩
      · rintro ⟨v, hv, x, hxI, h⟩; cases h; have hxV := (hI2_sub_V hv hxI).1
        by_cases hr : C.p.partnerRank b a ≤ k
        · exact Or.inl ⟨⟨hv, hxV⟩, hxI, hr⟩
        · exact Or.inr ⟨⟨hv, hxV⟩, hxI, by omega⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun v hv => ?_
      rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2), hI2_card v hv]
    · intro v₁ _ v₂ _ hne; change Disjoint _ _; rw [Finset.disjoint_left]; intro q h1 h2
      rcases Finset.mem_image.1 h1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.1 h2 with ⟨_, _, h⟩; exact hne (Prod.mk.inj h).1.symm
  have hP0_le : P0.card ≤ C.ZeroOrd.card := by
    refine Finset.card_le_card fun ⟨a, b⟩ h => ?_
    simp only [P0, ZeroOrd, Finset.mem_filter, Finset.mem_product] at h ⊢
    exact ⟨⟨(Finset.mem_filter.1 h.1.1).1, h.1.2⟩, (hI2_sub_V h.1.1 h.2.1).2.1.symm,
      (Finset.mem_filter.1 h.2.1).2.1, h.2.2⟩
  have hG_prop : ∀ {a2 b1}, (a2, b1) ∈ G →
      ¬ C.Hadj (C.M.val a2) b1 ∧
      C.p.partnerRank (C.M.val b1) a2 = k + 1 ∧
      C.p.partnerRank a2 (C.M.val b1) < C.p.partnerRank a2 (w2 a2) := by
    intro a2 b1 hmemG
    have ha2_V2 := (Finset.mem_product.1 (Finset.mem_filter.1 hmemG).1).1
    have ha2V := (Finset.mem_filter.1 ha2_V2).1; have hda2 := (Finset.mem_filter.1 ha2_V2).2
    have hb1I := (Finset.mem_filter.1 hmemG).2.1; have hrb1a2 := (Finset.mem_filter.1 hmemG).2.2
    have hb1_sub := hI2_sub_V ha2_V2 hb1I
    have hwspec := hw12 ha2_V2
    exact C.step6_G_prop ha2V hda2 hb1_sub.1 hb1_sub.2.1 hb1_sub.2.2 hrb1a2
      (Finset.mem_filter.1 hwspec.1).1 (Finset.mem_filter.1 hwspec.2.1).1
      (Finset.mem_filter.1 hwspec.1).2 (Finset.mem_filter.1 hwspec.2.1).2
      hwspec.2.2.1 hwspec.2.2.2.1 (Finset.mem_filter.1 hb1I).2.2
  let B1 := V₁.filter (fun b1 => ∃ a2, (a2, b1) ∈ G)
  let B2 := V₂.filter (fun b1 => ∃ a2, (a2, b1) ∈ G)
  have hG_card : G.card = B1.card + B2.card := by
    have hdisjB : Disjoint B1 B2 := by
      rw [Finset.disjoint_left]; intro b h1 h2
      exact (Finset.mem_filter.1 (Finset.mem_filter.1 h1).1).2 (Finset.mem_filter.1 (Finset.mem_filter.1 h2).1).2
    rw [← Finset.card_union_of_disjoint hdisjB]
    refine Finset.card_bij (fun q _ => q.2) ?_ ?_ ?_
    · intro ⟨a2, b1⟩ hq
      have hb1V := (Finset.mem_product.1 (Finset.mem_filter.1 hq).1).2
      by_cases h2 : 2 ≤ (C.NH b1).card
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hb1V, h2⟩, ⟨a2, hq⟩⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hb1V, h2⟩, ⟨a2, hq⟩⟩)
    · intro ⟨a2, b1⟩ h1 ⟨a2', b1'⟩ h2 heq; dsimp only at heq; subst heq
      have ha : a2 = a2' := partnerRank_inj C.p (C.M.val b1) ((hG_prop h1).2.1.trans (hG_prop h2).2.1.symm)
      subst ha; rfl
    · intro b1 hb1
      rcases Finset.mem_union.1 hb1 with h1 | h2
      · rcases (Finset.mem_filter.1 h1).2 with ⟨a2, ha2⟩; exact ⟨(a2, b1), ha2, rfl⟩
      · rcases (Finset.mem_filter.1 h2).2 with ⟨a2, ha2⟩; exact ⟨(a2, b1), ha2, rfl⟩
  have hB1_Utop : ∀ b1 ∈ B1, (C.Utop b1).card = 0 := by
    intro b1 hb1
    have hb1V := (Finset.mem_filter.1 (Finset.mem_filter.1 hb1).1).1
    rcases (Finset.mem_filter.1 hb1).2 with ⟨a2, ha2G⟩
    have ha2V := (Finset.mem_filter.1 (Finset.mem_product.1 (Finset.mem_filter.1 ha2G).1).1).1
    have hfa : C.f (C.M.val b1) = a2 := (C.f_uniq (C.M.val b1) a2 (hG_prop ha2G).2.1).symm
    rw [Finset.card_eq_zero]; unfold Utop; rw [Finset.filter_eq_empty_iff]
    intro c hc hle
    have hceq := C.Utop_eq hb1V hc hle; rw [hfa] at hceq
    exact Finset.disjoint_left.1 C.VU_disj ha2V (by rw [← hceq]; exact hc)
  have hV_split1 : C.V = V₁ ∪ V₂ := by ext v; simp only [V₁, V₂, Finset.mem_union, Finset.mem_filter]; tauto
  have hV12_disj : Disjoint V₁ V₂ := by
    rw [Finset.disjoint_left]; intro v h1 h2; exact (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 h2).2
  have hV1_split : V₁ = (V₁ \ B1) ∪ B1 := (Finset.sdiff_union_of_subset (Finset.filter_subset _ _)).symm
  have hV1B1_disj : Disjoint (V₁ \ B1) B1 := Finset.sdiff_disjoint
  have hV1_card : V₁.card = (V₁ \ B1).card + B1.card := by
    rw [← Finset.card_union_of_disjoint hV1B1_disj, ← hV1_split]
  have hV_card_split : C.V.card = (V₁ \ B1).card + B1.card + V₂.card := by
    rw [hV_split1, Finset.card_union_of_disjoint hV12_disj, hV1_card]
  have hV1_sum : ∑ v ∈ V₁, ((C.NH v).card + 2 * (C.Utop v).card) =
      (∑ v ∈ V₁ \ B1, ((C.NH v).card + 2 * (C.Utop v).card)) +
      ∑ v ∈ B1, ((C.NH v).card + 2 * (C.Utop v).card) := by
    rw [← Finset.sum_union hV1B1_disj, ← hV1_split]
  have hrhs_bound : ∑ v ∈ C.V, ((C.NH v).card + 2 * (C.Utop v).card) ≤
      3 * (V₁ \ B1).card + B1.card + ∑ v ∈ V₂, (C.NH v).card := by
    rw [hV_split1, Finset.sum_union hV12_disj, hV1_sum]
    have h1 : ∑ v ∈ V₁ \ B1, ((C.NH v).card + 2 * (C.Utop v).card) ≤ 3 * (V₁ \ B1).card := by
      calc ∑ v ∈ V₁ \ B1, ((C.NH v).card + 2 * (C.Utop v).card)
          ≤ ∑ _v ∈ V₁ \ B1, 3 := Finset.sum_le_sum fun v hv => by
            have hv1 := (Finset.mem_sdiff.1 hv).1
            have hdv := (Finset.mem_filter.1 hv1).2
            have hu1 := C.Utop_le_one (Finset.mem_filter.1 hv1).1; omega
        _ = 3 * (V₁ \ B1).card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    have h2 : ∑ v ∈ B1, ((C.NH v).card + 2 * (C.Utop v).card) ≤ B1.card := by
      calc ∑ v ∈ B1, ((C.NH v).card + 2 * (C.Utop v).card)
          ≤ ∑ _v ∈ B1, 1 := Finset.sum_le_sum fun v hv => by
            have hdv := (Finset.mem_filter.1 (Finset.mem_filter.1 hv).1).2
            have hu0 := hB1_Utop v hv; omega
        _ = B1.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
    have h3 : ∑ v ∈ V₂, ((C.NH v).card + 2 * (C.Utop v).card) = ∑ v ∈ V₂, (C.NH v).card :=
      Finset.sum_congr rfl fun v hv => by rw [C.T4_Utop (Finset.mem_filter.1 hv).1 (Finset.mem_filter.1 hv).2]; simp
    omega
  have hB2_le : B2.card ≤ V₂.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hsum_r2_ge : ∑ v ∈ V₂, (C.NH v).card ≤ ∑ v ∈ V₂, (C.p.partnerRank v (w2 v) + 1) :=
    Finset.sum_le_sum fun v hv => by have := hr2_ge v hv; have := (Finset.mem_filter.1 hv).2; omega
  have hsum_shift : (∑ v ∈ V₂, (C.p.partnerRank v (w2 v) - 1)) + 2 * V₂.card =
      ∑ v ∈ V₂, (C.p.partnerRank v (w2 v) + 1) := by
    have h2 : 2 * V₂.card = ∑ _v ∈ V₂, 2 := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    rw [h2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by have := partnerRank_pos C.p v (w2 v); omega
  have hzero_id := C.zero_arc_identity
  have hU_ge3 := C.U_ge3
  have hmain_ineq : (∑ v ∈ V₂, (C.p.partnerRank v (w2 v) + 1)) + B1.card + (V₂.card - B2.card) ≤
      ∑ v ∈ V₂, (C.NH v).card := by
    have h2 : 3 * (V₁ \ B1).card + 3 * B1.card + 3 * V₂.card ≤ C.V.card * C.U.card := by
      rw [hV_card_split]; nlinarith
    omega
  have hG_pos : 0 < G.card := by omega
  rcases Finset.card_pos.1 hG_pos with ⟨⟨a2, b1⟩, hqG⟩
  have ha2_V2 : a2 ∈ V₂ := (Finset.mem_product.1 (Finset.mem_filter.1 hqG).1).1
  have hr2_eq : C.p.partnerRank a2 (w2 a2) + 1 = (C.NH a2).card := by
    by_contra hne
    have hge := hr2_ge a2 ha2_V2; have hda2 := (Finset.mem_filter.1 ha2_V2).2
    have hstrict : ∑ v ∈ V₂, (C.NH v).card < ∑ v ∈ V₂, (C.p.partnerRank v (w2 v) + 1) :=
      Finset.sum_lt_sum (fun v hv => by have := hr2_ge v hv; have := (Finset.mem_filter.1 hv).2; omega)
        ⟨a2, ha2_V2, by omega⟩
    omega
  have hprop := hG_prop hqG
  have hb1V : b1 ∈ C.V := (Finset.mem_product.1 (Finset.mem_filter.1 hqG).1).2
  have ha2V := (Finset.mem_filter.1 ha2_V2).1
  have ha1_not_NH : C.M.val b1 ∉ C.NH a2 := fun hm => by
    have := C.swap_adj ha2V (C.M_in_V hb1V).1 (Finset.mem_filter.1 hm).2
    rw [C.M.property b1] at this; exact hprop.1 this
  have hwspec := hw12 ha2_V2
  have hsub : insert (C.M.val b1) ((C.NH a2).erase (w1 a2)) ⊆
      Finset.univ.filter (fun w => C.p.partnerRank a2 w ≤ C.p.partnerRank a2 (w2 a2)) := by
    intro w hw; rcases Finset.mem_insert.1 hw with rfl | hwer
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by have := hprop.2.2; omega⟩
    · rcases Finset.mem_erase.1 hwer with ⟨hne, hwNH⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hwspec.2.2.2.2.2 w hwNH hne⟩
  have hnotmem : C.M.val b1 ∉ (C.NH a2).erase (w1 a2) := fun h => ha1_not_NH (Finset.mem_erase.1 h).2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnotmem, card_partnerRank_le C.p a2 _ (C.p.partnerRank_le a2 _)] at hc
  have her := Finset.card_erase_add_one hwspec.1
  omega

include C in
private lemma derive_false : False := by
  have hV2_empty := C.V2_empty
  have hNH_eq1 : ∀ v ∈ C.V, (C.NH v).card = 1 := by
    intro v hv
    have hnot2 : ¬ 2 ≤ (C.NH v).card := fun h2 => by
      have : v ∈ C.V.filter (fun w => 2 ≤ (C.NH w).card) := Finset.mem_filter.2 ⟨hv, h2⟩
      rw [hV2_empty] at this; exact Finset.notMem_empty v this
    have hge1 := C.NH_pos hv; omega
  have hV_ge_km1 := C.V_ge_k_sub_1; have hk := C.hk
  have hV_pos : 0 < C.V.card := by omega
  have hzero_id := C.zero_arc_identity; have hU_ge3 := C.U_ge3
  have hsum_le_3V : ∑ v ∈ C.V, ((C.NH v).card + 2 * (C.Utop v).card) ≤ 3 * C.V.card := by
    calc ∑ v ∈ C.V, ((C.NH v).card + 2 * (C.Utop v).card)
        ≤ ∑ _v ∈ C.V, 3 := Finset.sum_le_sum fun v hv => by rw [hNH_eq1 v hv]; have := C.Utop_le_one hv; omega
      _ = 3 * C.V.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hZero_empty : C.ZeroOrd = ∅ := by
    rw [← Finset.card_eq_zero]
    have h3V : 3 * C.V.card ≤ C.V.card * C.U.card := by nlinarith
    omega
  have hU_eq3 : C.U.card = 3 := by
    have h3V : 3 * C.V.card ≤ C.V.card * C.U.card := by nlinarith
    have hle : C.V.card * C.U.card ≤ C.V.card * 3 := by omega
    have := Nat.le_of_mul_le_mul_left hle hV_pos; omega
  have hUtop_eq1 : ∀ v ∈ C.V, (C.Utop v).card = 1 := by
    intro v hv; by_contra hne
    have hle := C.Utop_le_one hv
    have hlt : (C.NH v).card + 2 * (C.Utop v).card < 3 := by rw [hNH_eq1 v hv]; omega
    have hstrict : ∑ w ∈ C.V, ((C.NH w).card + 2 * (C.Utop w).card) < ∑ _w ∈ C.V, 3 :=
      Finset.sum_lt_sum (fun w hw => by rw [hNH_eq1 w hw]; have := C.Utop_le_one hw; omega) ⟨v, hv, hlt⟩
    rw [Finset.sum_const, smul_eq_mul] at hstrict
    rw [hU_eq3] at hzero_id; omega
  have hV_ge4 : 4 ≤ C.V.card := by have := C.VU_card; omega
  have hc_spec : ∀ v ∈ C.V, C.f (C.M.val v) ∈ C.U ∧ C.p.partnerRank v (C.f (C.M.val v)) ≤ k ∧ C.f (C.M.val v) ≠ C.f v := by
    intro v hv
    rcases Finset.card_pos.1 (show 0 < (C.Utop v).card by rw [hUtop_eq1 v hv]; omega) with ⟨c, hc⟩
    have hcU := (Finset.mem_filter.1 hc).1; have hle := (Finset.mem_filter.1 hc).2
    have hceq := C.Utop_eq hv hcU hle; rw [hceq] at hcU hle
    refine ⟨hcU, hle, fun heq => by have := C.f_rank v; rw [← heq] at this; omega⟩
  have hH_eq_M : ∀ {x y}, x ∈ C.V → y ∈ C.V → C.Hadj x y → y = C.M.val x := fun {x y} hx hy hxy =>
    Finset.card_le_one.1 (by change (C.NH x).card ≤ 1; rw [hNH_eq1 x hx]) y (Finset.mem_filter.2 ⟨hy, hxy⟩)
      (C.M.val x) (Finset.mem_filter.2 ⟨(C.M_in_V hx).1, (C.M_in_V hx).2.2⟩)
  have harc_force : ∀ {b1 a2}, b1 ∈ C.V → a2 ∈ C.V → a2 ≠ b1 → a2 ≠ C.M.val b1 →
      C.p.partnerRank b1 a2 ≤ k → C.f (C.M.val b1) = C.f a2 := by
    intro b1 a2 hb1 ha2 hne1 hne2 hrb1a2
    let a1 := C.M.val b1; let b2 := C.M.val a2
    have ha1V : a1 ∈ C.V := (C.M_in_V hb1).1; have hb2V : b2 ∈ C.V := (C.M_in_V ha2).1
    have ha1_ne_b1 : a1 ≠ b1 := (C.M_in_V hb1).2.1; have ha2_ne_b2 : a2 ≠ b2 := (C.M_in_V ha2).2.1.symm
    have ha1_ne_a2 : a1 ≠ a2 := hne2.symm
    have hb1_ne_b2 : b1 ≠ b2 := fun h => hne2 (by dsimp only [b2] at h; rw [h, C.M.property a2])
    have ha1_ne_b2 : a1 ≠ b2 := fun h => hne1 (by dsimp only [a1, b2] at h; exact (C.M.property.injective h).symm)
    let c := C.f a2
    have hc_b2 := hc_spec b2 hb2V
    have hMb2 : C.M.val b2 = a2 := C.M.property a2
    rw [hMb2] at hc_b2
    have hcU : c ∈ C.U := hc_b2.1; have hrb2c : C.p.partnerRank b2 c ≤ k := hc_b2.2.1
    have hpm : C.HasHPM ((((C.V.erase a1).erase b1).erase a2).erase b2) := by
      let W := (((C.V.erase a1).erase b1).erase a2).erase b2
      have hMW : ∀ z ∈ W, C.M.val z ∈ W := by
        intro z hz; simp only [W, Finset.mem_erase] at hz ⊢
        refine ⟨fun h => hz.2.1 (by dsimp only [b2] at h; exact C.M.property.injective h),
                fun h => hz.1 (by dsimp only [b2]; rw [← h, C.M.property z]),
                fun h => hz.2.2.2.1 (by dsimp only [a1]; rw [← h, C.M.property z]),
                fun h => hz.2.2.1 (by dsimp only [a1] at h; exact C.M.property.injective h),
                (C.M_in_V hz.2.2.2.2).1⟩
      have hres := restrict_inv C.M.property hMW
      exact ⟨restrictTo W C.M.val, hres.1, hres.2.2,
        fun z hz => by rw [hres.2.1 z hz]; exact ⟨hMW z hz, (C.M_in_V (Finset.mem_erase.1 (Finset.mem_erase.1 (Finset.mem_erase.1 (Finset.mem_erase.1 hz).2).2).2).2).2.2⟩⟩
    rcases C.T2_step5_obstruct ha1V hb1 ha2 hb2V hcU ha1_ne_b1 ha1_ne_a2 ha1_ne_b2 hne1.symm hb1_ne_b2 ha2_ne_b2 hrb1a2 hpm with
      ⟨hrc, _⟩ | ⟨hra1a2, hra2a1⟩ | ⟨_, hrb2⟩ | ⟨_, hrb2⟩
    · exact (C.f_uniq a1 c hrc).symm
    · have r1 : C.p.partnerRank a2 b1 ≤ 2 * k := by have := partnerRank_lt_of_ne C.p hne1.symm; omega
      have hra2a1_le : C.p.partnerRank a2 a1 ≤ k := by omega
      have ha2_ne_fa1 : a2 ≠ C.f a1 := fun h => Finset.disjoint_left.1 C.VU_disj ha2 (by rw [h]; exact (hc_spec b1 hb1).1)
      have hra1a2_ne : C.p.partnerRank a1 a2 ≠ k + 1 := fun h => ha2_ne_fa1 (C.f_uniq a1 a2 h)
      have heq := hH_eq_M ha1V ha2 ⟨ha1_ne_a2, by omega, hra2a1_le⟩
      dsimp only [a1] at heq; rw [C.M.property b1] at heq; exact False.elim (hne1 heq)
    · have := partnerRank_pos C.p b2 a1; omega
    · have := partnerRank_pos C.p b2 a2; omega
  rcases Finset.card_pos.1 hV_pos with ⟨a, haV⟩
  let b := C.M.val a
  have hbV : b ∈ C.V := (C.M_in_V haV).1; have hab : b ≠ a := (C.M_in_V haV).2.1
  have hrem_pos : 0 < ((C.V.erase a).erase b).card := by
    have h1 := Finset.card_erase_add_one haV
    have h2 := Finset.card_erase_add_one (Finset.mem_erase.2 ⟨hab, hbV⟩); omega
  rcases Finset.card_pos.1 hrem_pos with ⟨x, hx⟩
  have hxb : x ≠ b := (Finset.mem_erase.1 hx).1
  have hxa : x ≠ a := (Finset.mem_erase.1 (Finset.mem_erase.1 hx).2).1
  have hxV : x ∈ C.V := (Finset.mem_erase.1 (Finset.mem_erase.1 hx).2).2
  let y := C.M.val x
  have hyV : y ∈ C.V := (C.M_in_V hxV).1
  have hya : y ≠ a := fun h => hxb (by dsimp only [b]; dsimp only [y] at h; rw [← h, C.M.property x])
  have hyb : y ≠ b := fun h => hxa (by dsimp only [y, b] at h; exact C.M.property.injective h)
  have horient : ∀ u ∈ C.V, ∀ v ∈ C.V, u ≠ v → C.p.partnerRank u v ≤ k ∨ C.p.partnerRank v u ≤ k := by
    intro u hu v hv huv; by_contra h; push Not at h
    have hm : (u, v) ∈ C.ZeroOrd :=
      Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hu, hv⟩, huv, by dsimp only; omega, by dsimp only; omega⟩
    rw [hZero_empty] at hm; exact Finset.notMem_empty _ hm
  have h1 : C.f b = C.f x ∨ C.f y = C.f a := by
    rcases horient a haV x hxV hxa.symm with hax | hxa_r
    · left; exact harc_force haV hxV hxa hxb hax
    · right; exact harc_force hxV haV hxa.symm hya.symm hxa_r
  have h2 : C.f b = C.f y ∨ C.f x = C.f a := by
    rcases horient a haV y hyV hya.symm with hay | hya_r
    · left; exact harc_force haV hyV hya hyb hay
    · right
      have hMy : C.M.val y = x := C.M.property x
      have := harc_force hyV haV hya.symm (by rw [hMy]; exact hxa.symm) hya_r
      rwa [hMy] at this
  have hfab : C.f b ≠ C.f a := (hc_spec a haV).2.2
  have hfxy : C.f y ≠ C.f x := (hc_spec x hxV).2.2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact hfxy (h2.symm.trans h1)
  · exact hfab (h1.trans h2)
  · exact hfab (h2.trans h1)
  · exact hfxy (h1.trans h2.symm)

end Ctx

private lemma exists_kStable_odd (k : ℕ) (hk : 3 ≤ k) (p : CompleteProfile (2 * k + 1)) :
    ∃ μ : Matching (Fin (2 * k + 1)), IsKStable ⊤ p.partnerRank k μ := by
  classical
  by_contra hno; push Not at hno
  have hblk : ∀ μ : Matching (Fin (2 * k + 1)), ∃ i j, IsKBlockingPair ⊤ p.partnerRank k μ i j := by
    intro μ; have hns := hno μ; unfold IsKStable at hns; push Not at hns; exact hns (isAcceptable_top μ)
  let IsHM : Matching (Fin (2 * k + 1)) → Prop :=
    fun μ => ∀ i, μ.val i = i ∨ (i ≠ μ.val i ∧ p.partnerRank i (μ.val i) ≤ k ∧ p.partnerRank (μ.val i) i ≤ k)
  let allHM := Finset.univ.filter IsHM
  have hallHM_ne : allHM.Nonempty := ⟨emptyMatching _, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun _ => Or.inl rfl⟩⟩
  rcases Finset.exists_max_image allHM (fun μ => (Finset.univ.filter (fun i => μ.val i ≠ i)).card) hallHM_ne with
    ⟨M, hM_mem, hM_max⟩
  exact (Ctx.mk hk p hblk M (Finset.mem_filter.1 hM_mem).2
    (fun μ hμ => hM_max μ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hμ⟩))).derive_false

theorem stabilityThreshold_odd_le (k : ℕ) (hk : 3 ≤ k) :
    Roommates.stabilityThreshold (2 * k + 1) ≤ k :=
  Roommates.stabilityThreshold_le (by omega) (exists_kStable_odd k hk)

end CounterexampleCtx

end FMProof

theorem OMA.disproof : ¬ (type_of% @FanelliMoscardelli.stability_threshold_tight) := by
  rintro ⟨N₀, hN₀, h⟩
  have hle : Roommates.stabilityThreshold (2 * N₀ + 1) ≤ N₀ :=
    FMProof.stabilityThreshold_odd_le N₀ hN₀
  have heq : Roommates.stabilityThreshold (2 * N₀ + 1) = (2 * N₀ + 1 + 1) / 2 :=
    h (2 * N₀ + 1) (by omega)
  omega
