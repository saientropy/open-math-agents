import FormalConjectures.WrittenOnTheWallII.GraphConjecture96

/-!
Proof of `WrittenOnTheWallII.GraphConjecture96.conjecture96`:
for every connected simple graph `G` on a nontrivial finite vertex type,
`α(G) ≤ 1 + min_v distEven(v) * (max_u λ(u) - 1)`.

Fix a root `v` attaining `minDistEven` and let `E = {w | Even (G.dist v w)}` and `L = max_u λ(u)`.
- If `L = 1`, any two vertices at distance `2` would produce a size-`2` independent set in their
  common neighbor's neighborhood, so `G` has diameter `1` and `α(G) ≤ 1`.
- If `L ≥ 2`, map each odd-distance vertex `w ∈ I \ E` of an independent set `I` to a BFS parent
  `p w ∈ E \ I`. Every fiber `F_u` (`u ≠ v`) admits a BFS parent `x` of `u` at distance `2` from
  all of `F_u`, so `|F_u| + 1 ≤ λ(u) ≤ L`, while `|F_v| ≤ L`. Summing over `P = p '' (I \ E)`
  disjoint from `I ∩ E` inside `E` yields `|I| ≤ 1 + |E| * (L - 1)`.
-/

namespace GraphConjecture96Proof

open SimpleGraph

private lemma card_le_indepNeighborsCard {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (u : α) (S : Finset α)
    (hN : ∀ w ∈ S, G.Adj u w) (hI : G.IsIndepSet (S : Set α)) :
    S.card ≤ indepNeighborsCard G u := by
  classical
  unfold indepNeighborsCard SimpleGraph.indepNum
  let S' : Finset (G.neighborSet u) :=
    S.attach.image (fun x => ⟨x.val, hN x.val x.property⟩)
  have hcard : S'.card = S.card := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_attach
    · intro a b hab
      exact Subtype.ext (congrArg (fun z : G.neighborSet u => z.val) hab)
  have hind : (G.induce (G.neighborSet u)).IsIndepSet (S' : Set _) := by
    intro a ha b hb hne hadj
    simp only [Finset.mem_coe, S', Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    have hxy : x ≠ y := fun h => hne (Subtype.ext h)
    exact hI hx hy hxy hadj
  rw [← hcard]
  apply le_csSup
  · exact ⟨Fintype.card _, fun n ⟨t, ht⟩ => ht.card_eq ▸ t.card_le_univ⟩
  · exact ⟨S', ⟨hind, rfl⟩⟩

private lemma dist_le_add_one_of_adj {α : Type*} {G : SimpleGraph α} (hG : G.Connected)
    {a b c : α} (hbc : G.Adj b c) : G.dist a c ≤ G.dist a b + 1 := by
  obtain ⟨p, hp⟩ := (hG a b).exists_walk_length_eq_dist
  have hle := G.dist_le (p.concat hbc)
  simpa [hp] using hle

private lemma exists_bfs_parent {α : Type*} {G : SimpleGraph α} (hG : G.Connected)
    {v w : α} (hpos : 0 < G.dist v w) :
    ∃ u : α, G.Adj u w ∧ G.dist v u + 1 = G.dist v w := by
  obtain ⟨p, hp⟩ := (hG v w).exists_walk_length_eq_dist
  cases hrev : p.reverse with
  | nil =>
    have hlen : p.reverse.length = 0 := by rw [hrev]; rfl
    rw [Walk.length_reverse, hp] at hlen
    omega
  | @cons _ u _ hwu q =>
    refine ⟨u, hwu.symm, ?_⟩
    have hqlen : q.length + 1 = G.dist v w := by
      have h1 : p.reverse.length = q.length + 1 := by rw [hrev]; rfl
      rw [Walk.length_reverse, hp] at h1
      omega
    have hle1 : G.dist v u ≤ q.length := by
      rw [← q.length_reverse]
      exact G.dist_le q.reverse
    have hle2 : G.dist v w ≤ G.dist v u + 1 := dist_le_add_one_of_adj hG hwu.symm
    omega

private lemma one_le_maxL {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) (hG : G.Connected) :
    1 ≤ (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp) := by
  obtain ⟨u, w, huw⟩ := exists_pair_ne α
  obtain ⟨p⟩ := hG u w
  cases p with
  | nil => exact absurd rfl huw
  | @cons _ b _ hub _ =>
    have h1 : 1 ≤ indepNeighborsCard G u := by
      have hcard := card_le_indepNeighborsCard G u {b} (by simp [hub])
        (by intro x hx y hy hne; simp at hx hy; subst hx; subst hy; exact absurd rfl hne)
      simpa using hcard
    have hmem : indepNeighborsCard G u ∈ Finset.univ.image (fun v => indepNeighborsCard G v) :=
      Finset.mem_image_of_mem _ (Finset.mem_univ u)
    exact h1.trans (Finset.le_max' _ _ hmem)

private lemma indep_card_le_one_of_maxL_eq_one {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (hG : G.Connected)
    (hL : ∀ u : α, indepNeighborsCard G u ≤ 1)
    {I : Finset α} (hI : G.IsIndepSet (I : Set α)) : I.card ≤ 1 := by
  by_contra hgt
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < I.card)
  have hnadj : ¬ G.Adj x y := hI hx hy hxy
  obtain ⟨p, hp⟩ := (hG x y).exists_walk_length_eq_dist
  cases p with
  | nil => exact hxy rfl
  | @cons _ b _ hxb q =>
    cases q with
    | nil => exact hnadj hxb
    | @cons _ c _ hbc r =>
      have hac_ne : x ≠ c := by
        intro hxc
        subst hxc
        have hle : G.dist x y ≤ r.length := G.dist_le r
        simp only [Walk.length_cons] at hp
        omega
      have hac_nadj : ¬ G.Adj x c := by
        intro hxc
        have hle : G.dist x y ≤ (Walk.cons hxc r).length := G.dist_le (Walk.cons hxc r)
        simp only [Walk.length_cons] at hle hp
        omega
      have hpair : ({x, c} : Finset α).card ≤ indepNeighborsCard G b := by
        apply card_le_indepNeighborsCard G b {x, c}
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hxb.symm
          · exact hbc
        · intro u hu w hw hne hadj
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hu hw
          rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
          · exact hne rfl
          · exact hac_nadj hadj
          · exact hac_nadj hadj.symm
          · exact hne rfl
      rw [Finset.card_pair hac_ne] at hpair
      have := hL b
      omega

private lemma indep_card_le_bound {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (hG : G.Connected) (v : α) (L : ℕ)
    (hL : ∀ u : α, indepNeighborsCard G u ≤ L) (hL2 : 2 ≤ L)
    {I : Finset α} (hI : G.IsIndepSet (I : Set α)) :
    I.card ≤ 1 + distEven G v * (L - 1) := by
  classical
  let E : Finset α := Finset.univ.filter (fun w => Even (G.dist v w))
  have hEcard : E.card = distEven G v := rfl
  let I_even : Finset α := I ∩ E
  let I_odd : Finset α := I \ E
  have hI_split : I.card = I_even.card + I_odd.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext w
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, I_even, I_odd]
      tauto
    · rw [Finset.disjoint_left]
      intro w h1 h2
      simp only [Finset.mem_inter, Finset.mem_sdiff, I_even, I_odd] at h1 h2
      exact h2.2 h1.2
  have hodd_parent : ∀ w ∈ I_odd, ∃ u : α, G.Adj u w ∧ G.dist v u + 1 = G.dist v w := by
    intro w hw
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, I_odd, E] at hw
    have hpos : 0 < G.dist v w := by
      by_contra h0
      have hd0 : G.dist v w = 0 := by omega
      exact hw.2 (hd0 ▸ ⟨0, rfl⟩)
    exact exists_bfs_parent hG hpos
  let par : α → α := fun w =>
    if hw : w ∈ I_odd then (hodd_parent w hw).choose else v
  have hpar_spec : ∀ w ∈ I_odd, G.Adj (par w) w ∧ G.dist v (par w) + 1 = G.dist v w := by
    intro w hw
    simp only [par, dif_pos hw]
    exact (hodd_parent w hw).choose_spec
  let P : Finset α := I_odd.image par
  have hP_sub_E : P ⊆ E := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    have hspec := hpar_spec w hw
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, I_odd, E] at hw ⊢
    rcases Nat.even_or_odd (G.dist v (par w)) with hev | ⟨k, hk⟩
    · exact hev
    · exfalso
      apply hw.2
      refine ⟨k + 1, ?_⟩
      omega
  have hP_disj : Disjoint I_even P := by
    rw [Finset.disjoint_left]
    intro u huI huP
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp huP
    have hspec := hpar_spec w hw
    have hwI : w ∈ I := (Finset.mem_sdiff.mp hw).1
    have huI' : par w ∈ I := (Finset.mem_inter.mp huI).1
    exact hI huI' hwI hspec.1.ne hspec.1
  have hsum_EP : I_even.card + P.card ≤ E.card := by
    rw [← Finset.card_union_of_disjoint hP_disj]
    exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_right hP_sub_E)
  have hfiber_le : ∀ u ∈ P, (I_odd.filter (fun w => par w = u)).card ≤
      (L - 1) + if u = v then 1 else 0 := by
    intro u hu
    set F : Finset α := I_odd.filter (fun w => par w = u)
    have hF_sub_I : ∀ w ∈ F, w ∈ I := fun w hw =>
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw).1).1
    have hF_adj : ∀ w ∈ F, G.Adj u w := by
      intro w hw
      have hw1 := (Finset.mem_filter.mp hw).1
      have hw2 := (Finset.mem_filter.mp hw).2
      rw [← hw2]
      exact (hpar_spec w hw1).1
    have hF_ind : G.IsIndepSet (F : Set α) := hI.mono (fun w hw => hF_sub_I w hw)
    by_cases huv : u = v
    · simp only [huv, ↓reduceIte]
      have h1 : F.card ≤ indepNeighborsCard G u := card_le_indepNeighborsCard G u F hF_adj hF_ind
      have h2 := hL u
      omega
    · simp only [huv, ↓reduceIte, Nat.add_zero]
      have hdist_pos : 0 < G.dist v u := by
        by_contra h0
        have hd0 : G.dist v u = 0 := by omega
        have heq := (G.dist_eq_zero_iff_eq_or_not_reachable.mp hd0).resolve_right
          (not_not.mpr (hG v u))
        exact huv heq.symm
      obtain ⟨x, hxu, hxdist⟩ := exists_bfs_parent hG hdist_pos
      have hxnotF : x ∉ F := by
        intro hxF
        have hspec := hpar_spec x (Finset.mem_filter.mp hxF).1
        rw [(Finset.mem_filter.mp hxF).2] at hspec
        omega
      have hxnadj : ∀ w ∈ F, ¬ G.Adj x w := by
        intro w hw hxw
        have hspec := hpar_spec w (Finset.mem_filter.mp hw).1
        rw [(Finset.mem_filter.mp hw).2] at hspec
        have htri : G.dist v w ≤ G.dist v x + 1 := dist_le_add_one_of_adj hG hxw
        omega
      have hins_ind : G.IsIndepSet ((insert x F : Finset α) : Set α) := by
        intro a ha b hb hne hadj
        simp only [Finset.coe_insert, Set.mem_insert_iff] at ha hb
        rcases ha with rfl | haF <;> rcases hb with rfl | hbF
        · exact hne rfl
        · exact hxnadj b hbF hadj
        · exact hxnadj a haF hadj.symm
        · exact hF_ind haF hbF hne hadj
      have hins_adj : ∀ w ∈ insert x F, G.Adj u w := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hwF
        · exact hxu.symm
        · exact hF_adj w hwF
      have hcard := card_le_indepNeighborsCard G u (insert x F) hins_adj hins_ind
      rw [Finset.card_insert_of_notMem hxnotF] at hcard
      have h2 := hL u
      omega
  have hodd_sum : I_odd.card = ∑ u ∈ P, (I_odd.filter (fun w => par w = u)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := par) (t := P)]
    intro w hw
    exact Finset.mem_image_of_mem par hw
  have hodd_bound : I_odd.card ≤ P.card * (L - 1) + 1 := by
    rw [hodd_sum]
    calc ∑ u ∈ P, (I_odd.filter (fun w => par w = u)).card
        ≤ ∑ u ∈ P, ((L - 1) + if u = v then 1 else 0) := Finset.sum_le_sum hfiber_le
      _ = ∑ _u ∈ P, (L - 1) + ∑ u ∈ P, (if u = v then 1 else 0) := Finset.sum_add_distrib
      _ = P.card * (L - 1) + (if v ∈ P then 1 else 0) := by
          simp [Finset.sum_const, smul_eq_mul, eq_comm]
      _ ≤ P.card * (L - 1) + 1 := by split_ifs <;> omega
  have hL1 : 1 ≤ L - 1 := by omega
  have hieven_mul : I_even.card ≤ I_even.card * (L - 1) := Nat.le_mul_of_pos_right _ hL1
  calc I.card = I_even.card + I_odd.card := hI_split
    _ ≤ I_even.card * (L - 1) + (P.card * (L - 1) + 1) := by omega
    _ = 1 + (I_even.card + P.card) * (L - 1) := by ring
    _ ≤ 1 + E.card * (L - 1) := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_right (L - 1) hsum_EP) 1
    _ = 1 + distEven G v * (L - 1) := by rw [hEcard]

end GraphConjecture96Proof

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture96.conjecture96 := by
  intro α _ _ _ G hG
  dsimp only
  set minDistEven := (Finset.univ.image (SimpleGraph.distEven G)).min' (by simp)
  set maxL := (Finset.univ.image (fun v => SimpleGraph.indepNeighborsCard G v)).max' (by simp)
  have hmaxL_ge : ∀ u : α, SimpleGraph.indepNeighborsCard G u ≤ maxL := fun u =>
    Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ u))
  have h1L : 1 ≤ maxL := GraphConjecture96Proof.one_le_maxL G hG
  have hmin_mem : minDistEven ∈ Finset.univ.image (SimpleGraph.distEven G) :=
    Finset.min'_mem _ _
  obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hmin_mem
  have hnat : G.indepNum ≤ 1 + minDistEven * (maxL - 1) := by
    unfold SimpleGraph.indepNum
    apply csSup_le
    · exact ⟨0, ∅, ⟨by simp [SimpleGraph.IsIndepSet], rfl⟩⟩
    · rintro n ⟨I, hI, rfl⟩
      by_cases hL1 : maxL = 1
      · have hle1 := GraphConjecture96Proof.indep_card_le_one_of_maxL_eq_one G hG
          (fun u => by have := hmaxL_ge u; omega) hI
        omega
      · have hL2 : 2 ≤ maxL := by omega
        have hbd := GraphConjecture96Proof.indep_card_le_bound G hG v maxL hmaxL_ge hL2 hI
        rw [hv] at hbd
        exact hbd
  have hreal : (G.indepNum : ℝ) ≤ (1 + minDistEven * (maxL - 1) : ℕ) := by
    exact_mod_cast hnat
  push_cast [Nat.cast_sub h1L] at hreal
  linarith
