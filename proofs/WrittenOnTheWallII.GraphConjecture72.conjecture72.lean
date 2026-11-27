import FormalConjectures.WrittenOnTheWallII.GraphConjecture72

/-!
Disproof of `WrittenOnTheWallII.GraphConjecture72.conjecture72`.

Counterexample on 19 vertices: two 4-cycles sharing center `c = 0` (`0-1-Q-2-0` and `0-3-5-4-0`),
with the far vertex of the first cycle expanded into a 13-clique `Q = {6, ..., 18}` fully adjacent
to `1` and `2`. Then:
- `averageEccentricity G ≥ 70 / 19` (certified by a 1-Lipschitz layer function `layer19 : Fin 19 → ℕ`),
- `maxL ≥ 4` (witnessed by the independent neighborhood `{1, 2, 3, 4}` of `0`),
- `largestInducedTreeSize G ≤ 5` (no triangles or 4-cycles in an induced tree),
while `⌈70 / 19 + 4 / 3⌉ = ⌈286 / 57⌉ = 6 > 5`.
-/

namespace GraphConjecture72Disproof

open SimpleGraph

private def adj19 (u v : Fin 19) : Bool :=
  let a := u.val
  let b := v.val
  if a == b then false
  else
    (a == 0 && (b == 1 || b == 2 || b == 3 || b == 4)) ||
    (b == 0 && (a == 1 || a == 2 || a == 3 || a == 4)) ||
    (a == 5 && (b == 3 || b == 4)) ||
    (b == 5 && (a == 3 || a == 4)) ||
    ((a == 1 || a == 2) && 6 ≤ b) ||
    ((b == 1 || b == 2) && 6 ≤ a) ||
    (6 ≤ a && 6 ≤ b)

private lemma adj19_symm : ∀ u v : Fin 19, adj19 u v = true → adj19 v u = true := by
  decide

private lemma adj19_loopless : ∀ u : Fin 19, adj19 u u = false := by
  decide

private def G19 : SimpleGraph (ULift.{u} (Fin 19)) where
  Adj u v := adj19 u.down v.down = true
  symm := ⟨fun u v h => adj19_symm u.down v.down h⟩
  loopless := ⟨fun u h => by rw [adj19_loopless] at h; exact Bool.false_ne_true h⟩

private def mkV (n : Fin 19) : ULift.{u} (Fin 19) := ULift.up n

private lemma g19_adj_iff (u v : ULift.{u} (Fin 19)) :
    G19.Adj u v ↔ adj19 u.down v.down = true := Iff.rfl

private lemma g19_adj_mkV {a b : Fin 19} (h : adj19 a b = true) :
    G19.Adj (mkV.{u} a) (mkV.{u} b) := h

private lemma adj19_of_ge6 :
    ∀ q v : Fin 19, 6 ≤ q.val → adj19 q v = true → 6 ≤ v.val ∨ v = 1 ∨ v = 2 := by
  decide

private lemma adj19_one_two :
    ∀ a v : Fin 19, (a = 1 ∨ a = 2) → adj19 a v = true → 6 ≤ v.val ∨ v = 0 := by
  decide

private lemma adj19_q_q :
    ∀ x y : Fin 19, 6 ≤ x.val → 6 ≤ y.val → x ≠ y → adj19 x y = true := by
  decide

private lemma adj19_one_two_q :
    ∀ a q : Fin 19, (a = 1 ∨ a = 2) → 6 ≤ q.val → adj19 a q = true := by
  decide

private lemma adj19_zero_reach :
    ∀ w : Fin 19, w = 0 ∨ adj19 w 0 = true ∨ (adj19 w 3 = true ∧ adj19 3 0 = true) ∨
      (adj19 w 1 = true ∧ adj19 1 0 = true) := by
  decide

private lemma g19_connected : (G19.{u}).Connected := by
  refine ⟨fun u v => ?_⟩
  have hreach0 : ∀ w : ULift.{u} (Fin 19), G19.Reachable w (mkV 0) := by
    intro w
    rcases adj19_zero_reach w.down with h0 | h1 | ⟨h3a, h3b⟩ | ⟨h1a, h1b⟩
    · have : w = mkV 0 := ULift.ext _ _ h0
      rw [this]
    · exact Adj.reachable h1
    · exact (Adj.reachable (show G19.Adj w (mkV 3) from h3a)).trans
        (Adj.reachable (show G19.Adj (mkV 3) (mkV 0) from h3b))
    · exact (Adj.reachable (show G19.Adj w (mkV 1) from h1a)).trans
        (Adj.reachable (show G19.Adj (mkV 1) (mkV 0) from h1b))
  exact (hreach0 u).trans (hreach0 v).symm

private def layer19 (v : Fin 19) : ℕ :=
  if v.val = 5 then 0
  else if v.val = 3 ∨ v.val = 4 then 1
  else if v.val = 0 then 2
  else if v.val = 1 ∨ v.val = 2 then 3
  else 4

private lemma layer19_adj_le : ∀ u v : Fin 19, adj19 u v = true → layer19 u ≤ layer19 v + 1 := by
  decide

private lemma layer19_walk_le {u v : ULift.{u} (Fin 19)} (p : G19.Walk u v) :
    layer19 u.down ≤ layer19 v.down + p.length ∧ layer19 v.down ≤ layer19 u.down + p.length := by
  induction p with
  | nil => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | @cons a b c hab q ih =>
    have h1 : layer19 a.down ≤ layer19 b.down + 1 := layer19_adj_le a.down b.down hab
    have h2 : layer19 b.down ≤ layer19 a.down + 1 := layer19_adj_le b.down a.down hab.symm
    simp only [Walk.length_cons]
    omega

private lemma layer19_dist_le (u v : ULift.{u} (Fin 19)) :
    layer19 u.down ≤ layer19 v.down + G19.dist u v ∧
    layer19 v.down ≤ layer19 u.down + G19.dist u v := by
  obtain ⟨p, hp⟩ := (g19_connected u v).exists_walk_length_eq_dist
  rw [← hp]
  exact layer19_walk_le p

private lemma dist_le_eccent_toNat (u v : ULift.{u} (Fin 19)) :
    G19.dist u v ≤ (G19.eccent u).toNat := by
  have h1 : (G19.dist u v : ℕ∞) ≤ G19.eccent u := by
    rw [(g19_connected u v).coe_dist_eq_edist]
    exact G19.edist_le_eccent
  have hfin : G19.eccent u ≠ ⊤ := by
    intro htop
    have hle : G19.eccent u ≤ (19 : ℕ∞) := by
      rw [eccent_le_iff]
      intro w
      obtain ⟨p, hp_path, hp_len⟩ := (g19_connected u w).exists_path_of_dist
      rw [← (g19_connected u w).coe_dist_eq_edist, ← hp_len]
      have hlen : p.length < Fintype.card (ULift.{u} (Fin 19)) := hp_path.length_lt
      have hcard : Fintype.card (ULift.{u} (Fin 19)) = 19 := by simp
      exact_mod_cast (show p.length ≤ 19 by omega)
    rw [htop] at hle
    exact (ENat.natCast_lt_top 19).not_ge hle
  have hcast : ((G19.eccent u).toNat : ℕ∞) = G19.eccent u := ENat.natCast_toNat hfin
  rw [← hcast] at h1
  exact_mod_cast h1

private def eccLB (v : Fin 19) : ℕ :=
  if v.val = 0 then 2
  else if v.val ≤ 4 then 3
  else 4

private lemma eccLB_le_layer :
    ∀ v : Fin 19, eccLB v ≤ layer19 v ∨ eccLB v ≤ 4 - layer19 v := by
  decide

private lemma eccLB_le_eccent (u : ULift.{u} (Fin 19)) :
    eccLB u.down ≤ (G19.eccent u).toNat := by
  have h5 := layer19_dist_le u (mkV 5)
  have h6 := layer19_dist_le u (mkV 6)
  have hd5 := dist_le_eccent_toNat u (mkV 5)
  have hd6 := dist_le_eccent_toNat u (mkV 6)
  have hl5 : layer19 (mkV.{u} 5).down = 0 := by decide
  have hl6 : layer19 (mkV.{u} 6).down = 4 := by decide
  rw [hl5] at h5
  rw [hl6] at h6
  have hcheck := eccLB_le_layer u.down
  omega

private lemma avgEcc_ge : (70 : ℝ) / 19 ≤ averageEccentricity (G19.{u}) := by
  unfold averageEccentricity
  have hcard : (Fintype.card (ULift.{u} (Fin 19)) : ℝ) = 19 := by simp
  rw [hcard]
  have hsum_nat : 70 ≤ ∑ v : ULift.{u} (Fin 19), (G19.eccent v).toNat := by
    have h70 : (∑ v : ULift.{u} (Fin 19), eccLB v.down) = 70 := by
      have heq : (∑ v : ULift.{u} (Fin 19), eccLB v.down) = ∑ v : Fin 19, eccLB v :=
        Fintype.sum_equiv Equiv.ulift _ _ (fun _ => rfl)
      rw [heq]
      decide
    rw [← h70]
    exact Finset.sum_le_sum (fun v _ => eccLB_le_eccent v)
  have hsum_real : (70 : ℝ) ≤ ((∑ v : ULift.{u} (Fin 19), (G19.eccent v).toNat : ℕ) : ℝ) := by
    exact_mod_cast hsum_nat
  linarith

private lemma four_le_indepNeighbors_zero :
    4 ≤ indepNeighborsCard (G19.{u}) (mkV 0) := by
  classical
  unfold indepNeighborsCard
  have h1 : mkV.{u} 1 ∈ G19.neighborSet (mkV 0) := g19_adj_mkV (by decide)
  have h2 : mkV.{u} 2 ∈ G19.neighborSet (mkV 0) := g19_adj_mkV (by decide)
  have h3 : mkV.{u} 3 ∈ G19.neighborSet (mkV 0) := g19_adj_mkV (by decide)
  have h4 : mkV.{u} 4 ∈ G19.neighborSet (mkV 0) := g19_adj_mkV (by decide)
  let s : Finset (G19.neighborSet (mkV.{u} 0)) :=
    {⟨mkV 1, h1⟩, ⟨mkV 2, h2⟩, ⟨mkV 3, h3⟩, ⟨mkV 4, h4⟩}
  have hcard : s.card = 4 := by
    have h12 : (⟨mkV.{u} 1, h1⟩ : G19.neighborSet (mkV 0)) ≠ ⟨mkV 2, h2⟩ := by intro h; simp [mkV] at h
    have h13 : (⟨mkV.{u} 1, h1⟩ : G19.neighborSet (mkV 0)) ≠ ⟨mkV 3, h3⟩ := by intro h; simp [mkV] at h
    have h14 : (⟨mkV.{u} 1, h1⟩ : G19.neighborSet (mkV 0)) ≠ ⟨mkV 4, h4⟩ := by intro h; simp [mkV] at h
    have h23 : (⟨mkV.{u} 2, h2⟩ : G19.neighborSet (mkV 0)) ≠ ⟨mkV 3, h3⟩ := by intro h; simp [mkV] at h
    have h24 : (⟨mkV.{u} 2, h2⟩ : G19.neighborSet (mkV 0)) ≠ ⟨mkV 4, h4⟩ := by intro h; simp [mkV] at h
    have h34 : (⟨mkV.{u} 3, h3⟩ : G19.neighborSet (mkV 0)) ≠ ⟨mkV 4, h4⟩ := by intro h; simp [mkV] at h
    simp [s, h12, h13, h14, h23, h24, h34]
  have hindep : (G19.induce (G19.neighborSet (mkV.{u} 0))).IsIndepSet (s : Set _) := by
    intro a ha b hb hne hadj
    change adj19 a.val.down b.val.down = true at hadj
    simp only [Finset.mem_coe, s, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      first
      | exact hne rfl
      | (dsimp only [mkV] at hadj; revert hadj; decide)
  have hle : s.card ≤ (G19.induce (G19.neighborSet (mkV.{u} 0))).indepNum := by
    unfold SimpleGraph.indepNum
    apply le_csSup
    · exact ⟨Fintype.card _, fun n ⟨t, ht⟩ => by rw [← ht.card_eq]; exact t.card_le_univ⟩
    · exact ⟨s, ⟨hindep, rfl⟩⟩
  omega

private lemma no_triangle_in_tree {α : Type*} {G : SimpleGraph α} {s : Finset α}
    (hT : (G.induce (s : Set α)).IsTree) {a b c : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) : False := by
  let H := G.induce (s : Set α)
  let a' : (s : Set α) := ⟨a, ha⟩
  let b' : (s : Set α) := ⟨b, hb⟩
  let c' : (s : Set α) := ⟨c, hc⟩
  have hab' : H.Adj a' b' := hab
  have hbc' : H.Adj b' c' := hbc
  have hca' : H.Adj c' a' := hca
  let p : H.Walk a' a' := Walk.cons hab' (Walk.cons hbc' (Walk.cons hca' Walk.nil))
  have hp : p.IsCycle := by
    refine ⟨⟨⟨?_⟩, by simp [p]⟩, ?_⟩
    · simp [p, hab'.ne, hbc'.ne, hca'.ne, hab'.ne.symm, hca'.ne.symm]
    · simp [p, hbc'.ne, hca'.ne, hab'.ne.symm]
  exact hT.isAcyclic p hp

private lemma no_four_cycle_in_tree {α : Type*} {G : SimpleGraph α} {s : Finset α}
    (hT : (G.induce (s : Set α)).IsTree) {a b c d : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hab_ne : a ≠ b) (hac_ne : a ≠ c) (had_ne : a ≠ d)
    (hbc_ne : b ≠ c) (hbd_ne : b ≠ d) (hcd_ne : c ≠ d)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a) : False := by
  let H := G.induce (s : Set α)
  let a' : (s : Set α) := ⟨a, ha⟩
  let b' : (s : Set α) := ⟨b, hb⟩
  let c' : (s : Set α) := ⟨c, hc⟩
  let d' : (s : Set α) := ⟨d, hd⟩
  have hab' : H.Adj a' b' := hab
  have hbc' : H.Adj b' c' := hbc
  have hcd' : H.Adj c' d' := hcd
  have hda' : H.Adj d' a' := hda
  have h1 : a' ≠ b' := fun h => hab_ne (congrArg Subtype.val h)
  have h2 : a' ≠ c' := fun h => hac_ne (congrArg Subtype.val h)
  have h3 : a' ≠ d' := fun h => had_ne (congrArg Subtype.val h)
  have h4 : b' ≠ c' := fun h => hbc_ne (congrArg Subtype.val h)
  have h5 : b' ≠ d' := fun h => hbd_ne (congrArg Subtype.val h)
  have h6 : c' ≠ d' := fun h => hcd_ne (congrArg Subtype.val h)
  let p : H.Walk a' a' :=
    Walk.cons hab' (Walk.cons hbc' (Walk.cons hcd' (Walk.cons hda' Walk.nil)))
  have hp : p.IsCycle := by
    refine ⟨⟨⟨?_⟩, by simp [p]⟩, ?_⟩
    · simp [p, h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm]
    · simp [p, h4, h5, h6, h1.symm, h2.symm, h3.symm]
  exact hT.isAcyclic p hp

private lemma induced_tree_card_le_five {s : Finset (ULift.{u} (Fin 19))}
    (hT : (G19.induce (s : Set _)).IsTree) : s.card ≤ 5 := by
  let Q : Finset (ULift.{u} (Fin 19)) := Finset.univ.filter (fun v => 6 ≤ v.down.val)
  let C : Finset (ULift.{u} (Fin 19)) := Finset.univ.filter (fun v => v.down.val < 6)
  have hpart : s.card = (s ∩ C).card + (s ∩ Q).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext v
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
        Q, C]
      constructor
      · intro h
        by_cases hlt : v.down.val < 6
        · exact Or.inl ⟨h, hlt⟩
        · exact Or.inr ⟨h, by omega⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · rw [Finset.disjoint_left]
      intro v h1 h2
      simp only [Finset.mem_inter, Finset.mem_filter, Q, C] at h1 h2
      omega
  have hQle2 : (s ∩ Q).card ≤ 2 := by
    by_contra hgt
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (s ∩ Q).card)
    have hne : ((s ∩ Q).erase a |>.erase b).Nonempty := by
      rw [← Finset.card_pos]
      have hb' : b ∈ (s ∩ Q).erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
      rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]
      omega
    obtain ⟨c, hc⟩ := hne
    have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
    have hc' := (Finset.mem_erase.mp hc).2
    have hca : c ≠ a := (Finset.mem_erase.mp hc').1
    have hcQ := (Finset.mem_erase.mp hc').2
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, Q] at ha hb hcQ
    have hab' : a.down ≠ b.down := fun h => hab (ULift.ext _ _ h)
    have hbc' : b.down ≠ c.down := fun h => hcb (ULift.ext _ _ h.symm)
    have hca' : c.down ≠ a.down := fun h => hca (ULift.ext _ _ h)
    exact no_triangle_in_tree hT ha.1 hb.1 hcQ.1
      (adj19_q_q a.down b.down ha.2 hb.2 hab')
      (adj19_q_q b.down c.down hb.2 hcQ.2 hbc')
      (adj19_q_q c.down a.down hcQ.2 ha.2 hca')
  by_cases hQ2 : (s ∩ Q).card = 2
  · obtain ⟨q1, hq1, q2, hq2, hqne⟩ := Finset.one_lt_card.mp (by omega : 1 < (s ∩ Q).card)
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, Q] at hq1 hq2
    have hqne' : q1.down ≠ q2.down := fun h => hqne (ULift.ext _ _ h)
    have h1not : mkV.{u} 1 ∉ s := fun h1 =>
      no_triangle_in_tree hT h1 hq1.1 hq2.1
        (adj19_one_two_q 1 q1.down (Or.inl rfl) hq1.2)
        (adj19_q_q q1.down q2.down hq1.2 hq2.2 hqne')
        (adj19_symm 1 q2.down (adj19_one_two_q 1 q2.down (Or.inl rfl) hq2.2))
    have h2not : mkV.{u} 2 ∉ s := fun h2 =>
      no_triangle_in_tree hT h2 hq1.1 hq2.1
        (adj19_one_two_q 2 q1.down (Or.inr rfl) hq1.2)
        (adj19_q_q q1.down q2.down hq1.2 hq2.2 hqne')
        (adj19_symm 2 q2.down (adj19_one_two_q 2 q2.down (Or.inr rfl) hq2.2))
    have hsQ : ∀ v ∈ s, 6 ≤ v.down.val := by
      intro v hv
      obtain ⟨p⟩ := hT.connected ⟨q1, hq1.1⟩ ⟨v, hv⟩
      have hwalk : ∀ {a b : (s : Set (ULift.{u} (Fin 19)))}
          (_ : (G19.induce (s : Set (ULift.{u} (Fin 19)))).Walk a b),
          6 ≤ a.val.down.val → 6 ≤ b.val.down.val := by
        intro a b w
        induction w with
        | nil => exact id
        | @cons x y z hxy _ ih =>
          intro hx6
          apply ih
          rcases adj19_of_ge6 x.val.down y.val.down hx6 hxy with hy6 | hy1 | hy2
          · exact hy6
          · exact absurd (show mkV.{u} 1 ∈ s from ULift.ext y.val (mkV 1) hy1 ▸ y.property) h1not
          · exact absurd (show mkV.{u} 2 ∈ s from ULift.ext y.val (mkV 2) hy2 ▸ y.property) h2not
      exact hwalk p hq1.2
    have hC0 : (s ∩ C).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro v hv
      simp only [Finset.mem_inter, Finset.mem_filter, C] at hv
      have := hsQ v hv.1
      omega
    omega
  · have hQle1 : (s ∩ Q).card ≤ 1 := by omega
    have hCcard : C.card = 6 := by
      have heq : C.card = (Finset.univ.filter (fun v : Fin 19 => v.val < 6)).card := by
        refine Finset.card_bij (fun x _ => x.down) ?_ ?_ ?_
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, C] at hx ⊢
          exact hx
        · intro a _ b _ hab; exact ULift.ext _ _ hab
        · intro b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
          exact ⟨ULift.up b, by simp [C, hb], rfl⟩
      rw [heq]; decide
    have hnot_bcycle : ¬ (mkV.{u} 0 ∈ s ∧ mkV 3 ∈ s ∧ mkV 4 ∈ s ∧ mkV 5 ∈ s) := by
      rintro ⟨h0, h3, h4, h5⟩
      exact no_four_cycle_in_tree hT h0 h3 h5 h4
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (g19_adj_mkV (by decide)) (g19_adj_mkV (by decide))
        (g19_adj_mkV (by decide)) (g19_adj_mkV (by decide))
    by_cases hQ0 : (s ∩ Q).card = 0
    · have hCsub : s ∩ C ⊂ C := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.inter_subset_right, fun heq => ?_⟩
        have hmem_s : ∀ v : Fin 19, v.val < 6 → mkV.{u} v ∈ s := fun v hv =>
          (Finset.mem_inter.mp (heq.symm ▸ (by simp [C, mkV, hv] : mkV.{u} v ∈ C))).1
        exact hnot_bcycle ⟨hmem_s 0 (by decide), hmem_s 3 (by decide),
          hmem_s 4 (by decide), hmem_s 5 (by decide)⟩
      have hClt : (s ∩ C).card < C.card := Finset.card_lt_card hCsub
      omega
    · have hQ1 : (s ∩ Q).card = 1 := by omega
      obtain ⟨q, hq⟩ := Finset.card_pos.mp (by omega : 0 < (s ∩ Q).card)
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, Q] at hq
      by_cases h0s : mkV.{u} 0 ∈ s
      · have hnot_acycle : ¬ (mkV.{u} 1 ∈ s ∧ mkV 2 ∈ s) := by
          rintro ⟨h1, h2⟩
          exact no_four_cycle_in_tree hT h0s h1 hq.1 h2
            (by decide)
            (fun h => by have := congrArg (fun x => x.down.val) h; simp [mkV] at this; omega)
            (by decide)
            (fun h => by have := congrArg (fun x => x.down.val) h; simp [mkV] at this; omega)
            (by decide)
            (fun h => by have := congrArg (fun x => x.down.val) h; simp [mkV] at this; omega)
            (g19_adj_mkV (by decide))
            (adj19_one_two_q 1 q.down (Or.inl rfl) hq.2)
            (adj19_symm 2 q.down (adj19_one_two_q 2 q.down (Or.inr rfl) hq.2))
            (g19_adj_mkV (by decide))
        have hex1 : ∃ x ∈ ({mkV.{u} 1, mkV 2} : Finset _), x ∉ s := by
          by_contra hall
          push Not at hall
          exact hnot_acycle ⟨hall (mkV 1) (by simp), hall (mkV 2) (by simp)⟩
        have hex2 : ∃ y ∈ ({mkV.{u} 3, mkV 4, mkV 5} : Finset _), y ∉ s := by
          by_contra hall
          push Not at hall
          exact hnot_bcycle ⟨h0s, hall (mkV 3) (by simp), hall (mkV 4) (by simp), hall (mkV 5) (by simp)⟩
        obtain ⟨x, hxA, hxnot⟩ := hex1
        obtain ⟨y, hyB, hynot⟩ := hex2
        have hxy : x ≠ y := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxA hyB
          rcases hxA with rfl | rfl <;> rcases hyB with rfl | rfl | rfl <;> decide
        have hxC : x ∈ C := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxA
          rcases hxA with rfl | rfl <;> simp [C, mkV]
        have hyC : y ∈ C := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hyB
          rcases hyB with rfl | rfl | rfl <;> simp [C, mkV]
        have hsub : s ∩ C ⊆ (C.erase x).erase y := by
          intro v hv
          simp only [Finset.mem_inter, Finset.mem_erase] at hv ⊢
          exact ⟨fun h => hynot (h ▸ hv.1), fun h => hxnot (h ▸ hv.1), hv.2⟩
        have hyCx : y ∈ C.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hyC⟩
        have hle := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hyCx, Finset.card_erase_of_mem hxC, hCcard] at hle
        omega
      · have hs_in : ∀ v ∈ s, v.down = 1 ∨ v.down = 2 ∨ 6 ≤ v.down.val := by
          intro v hv
          obtain ⟨p⟩ := hT.connected ⟨q, hq.1⟩ ⟨v, hv⟩
          have hwalk : ∀ {a b : (s : Set (ULift.{u} (Fin 19)))}
              (_ : (G19.induce (s : Set (ULift.{u} (Fin 19)))).Walk a b),
              (a.val.down = 1 ∨ a.val.down = 2 ∨ 6 ≤ a.val.down.val) →
              (b.val.down = 1 ∨ b.val.down = 2 ∨ 6 ≤ b.val.down.val) := by
            intro a b w
            induction w with
            | nil => exact id
            | @cons x y z hxy _ ih =>
              intro hx
              apply ih
              rcases hx with hx1 | hx2 | hx6
              · rcases adj19_one_two x.val.down y.val.down (Or.inl hx1) hxy with hy6 | hy0
                · exact Or.inr (Or.inr hy6)
                · exact absurd (show mkV.{u} 0 ∈ s from ULift.ext y.val (mkV 0) hy0 ▸ y.property) h0s
              · rcases adj19_one_two x.val.down y.val.down (Or.inr hx2) hxy with hy6 | hy0
                · exact Or.inr (Or.inr hy6)
                · exact absurd (show mkV.{u} 0 ∈ s from ULift.ext y.val (mkV 0) hy0 ▸ y.property) h0s
              · rcases adj19_of_ge6 x.val.down y.val.down hx6 hxy with hy6 | hy1 | hy2
                · exact Or.inr (Or.inr hy6)
                · exact Or.inl hy1
                · exact Or.inr (Or.inl hy2)
          exact hwalk p (Or.inr (Or.inr hq.2))
        have hCsub : s ∩ C ⊆ {mkV.{u} 1, mkV 2} := by
          intro v hv
          simp only [Finset.mem_inter, Finset.mem_filter, C] at hv
          rcases hs_in v hv.1 with h1 | h2 | h6
          · exact Finset.mem_insert.mpr (Or.inl (ULift.ext _ _ h1))
          · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (ULift.ext _ _ h2)))
          · omega
        have hCle : (s ∩ C).card ≤ 2 :=
          (Finset.card_le_card hCsub).trans Finset.card_le_two
        omega

private lemma largestInducedTreeSize_le_five :
    largestInducedTreeSize (G19.{u}) ≤ 5 := by
  unfold largestInducedTreeSize
  apply csSup_le
  · let s0 : Finset (ULift.{u} (Fin 19)) := {mkV 0}
    refine ⟨1, s0, rfl, ?_⟩
    have : Nonempty (s0 : Set (ULift.{u} (Fin 19))) := ⟨⟨mkV 0, by simp [s0]⟩⟩
    have : Subsingleton (s0 : Set (ULift.{u} (Fin 19))) := ⟨fun a b => by
      apply Subtype.ext
      have ha : a.val = mkV 0 := by simpa [s0] using a.property
      have hb : b.val = mkV 0 := by simpa [s0] using b.property
      exact ha.trans hb.symm⟩
    exact IsTree.of_subsingleton
  · rintro n ⟨s, rfl, hT⟩
    exact induced_tree_card_le_five hT

end GraphConjecture72Disproof

theorem OMA.disproof : ¬ (type_of% @WrittenOnTheWallII.GraphConjecture72.conjecture72) := by
  intro hconj
  have h := hconj GraphConjecture72Disproof.G19 GraphConjecture72Disproof.g19_connected
  dsimp only at h
  set maxL := (Finset.univ.image (fun v => SimpleGraph.indepNeighborsCard GraphConjecture72Disproof.G19 v)).max' (by simp)
  have hmaxL : 4 ≤ maxL := by
    have hmem : SimpleGraph.indepNeighborsCard GraphConjecture72Disproof.G19 (GraphConjecture72Disproof.mkV 0) ∈
        Finset.univ.image (fun v => SimpleGraph.indepNeighborsCard GraphConjecture72Disproof.G19 v) :=
      Finset.mem_image_of_mem _ (Finset.mem_univ _)
    exact GraphConjecture72Disproof.four_le_indepNeighbors_zero.trans (Finset.le_max' _ _ hmem)
  have havg := GraphConjecture72Disproof.avgEcc_ge
  have htree := GraphConjecture72Disproof.largestInducedTreeSize_le_five
  have hmaxL_real : (4 : ℝ) ≤ (maxL : ℝ) := by exact_mod_cast hmaxL
  have hgt5 : (5 : ℝ) < SimpleGraph.averageEccentricity GraphConjecture72Disproof.G19 + (maxL : ℝ) / 3 := by
    linarith
  have hceil : (5 : ℤ) < ⌈SimpleGraph.averageEccentricity GraphConjecture72Disproof.G19 + (maxL : ℝ) / 3⌉ :=
    Int.lt_ceil.mpr (by exact_mod_cast hgt5)
  have hceil_real : (6 : ℝ) ≤ (⌈SimpleGraph.averageEccentricity GraphConjecture72Disproof.G19 + (maxL : ℝ) / 3⌉ : ℝ) := by
    exact_mod_cast (show (6 : ℤ) ≤ _ by omega)
  have htree_real : (SimpleGraph.largestInducedTreeSize GraphConjecture72Disproof.G19 : ℝ) ≤ 5 := by
    exact_mod_cast htree
  linarith
