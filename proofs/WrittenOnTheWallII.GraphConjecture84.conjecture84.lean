import FormalConjectures.WrittenOnTheWallII.GraphConjecture84

/-!
# Proof of Written on the Wall II, Conjecture 84

We prove `2 * rad(G) / δ(G) ≤ tree(G)` for every finite simple connected graph `G` with
positive minimum degree `δ(G)`:
- When `δ(G) ≥ 2`, a geodesic of length `rad(G)` yields an induced tree on `rad(G) + 1` vertices.
- When `δ(G) = 1` and `rad(G) ≥ 2`, a leaf's neighbor is a cut vertex, and we prove
  Gebendorfer's cut-vertex bound `2 * rad(G) ≤ tree(G)` via Chung's `2 * rad - 1` induced path
  theorem and minimal-counterexample reduction to a 2-connected core with uniform pendant paths.
-/

open SimpleGraph

namespace GraphConjecture84Proof

section BasicHelpers

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private lemma edist_eq_coe_dist {G : SimpleGraph V} (hG : G.Connected) (u v : V) :
    G.edist u v = (G.dist u v : ℕ∞) := by
  rw [SimpleGraph.dist, ENat.natCast_toNat]
  exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hG u v)

omit [DecidableEq V] in
private lemma radius_ne_top_of_connected {G : SimpleGraph V} (hG : G.Connected) :
    G.radius ≠ ⊤ := by
  have : Nonempty V := hG.nonempty
  exact G.radius_ne_top_iff.mpr hG

omit [DecidableEq V] in
private lemma radius_eq_coe_toNat {G : SimpleGraph V} (hG : G.Connected) :
    G.radius = (G.radius.toNat : ℕ∞) :=
  (ENat.natCast_toNat (radius_ne_top_of_connected hG)).symm

omit [DecidableEq V] in
private lemma exists_center_dist_le {G : SimpleGraph V} (hG : G.Connected) :
    ∃ u : V, ∀ v : V, G.dist u v ≤ G.radius.toNat := by
  have : Nonempty V := hG.nonempty
  obtain ⟨u, hu⟩ := G.exists_eccent_eq_radius
  refine ⟨u, fun v => ?_⟩
  have h1 : G.edist u v ≤ G.radius := hu ▸ G.edist_le_eccent
  rw [edist_eq_coe_dist hG, radius_eq_coe_toNat hG, Nat.cast_le] at h1
  exact h1

omit [DecidableEq V] in
private lemma radius_toNat_le_of_exists {G : SimpleGraph V} (hG : G.Connected)
    {r : ℕ} (h : ∃ u : V, ∀ v : V, G.dist u v ≤ r) :
    G.radius.toNat ≤ r := by
  obtain ⟨u, hu⟩ := h
  have h1 : G.eccent u ≤ (r : ℕ∞) := by
    rw [SimpleGraph.eccent]
    refine iSup_le fun v => ?_
    rw [edist_eq_coe_dist hG]
    exact Nat.cast_le.mpr (hu v)
  have h2 : G.radius ≤ (r : ℕ∞) := le_trans G.radius_le_eccent h1
  rw [radius_eq_coe_toNat hG, Nat.cast_le] at h2
  exact h2

omit [DecidableEq V] in
private lemma exists_dist_ge_radius {G : SimpleGraph V} (hG : G.Connected) (u : V) :
    ∃ v : V, G.radius.toNat ≤ G.dist u v := by
  have : Nonempty V := hG.nonempty
  obtain ⟨v, hv⟩ := G.exists_edist_eq_eccent_of_finite u
  refine ⟨v, ?_⟩
  have h1 : G.radius ≤ G.edist u v := hv ▸ G.radius_le_eccent
  rw [radius_eq_coe_toNat hG, edist_eq_coe_dist hG, Nat.cast_le] at h1
  exact h1

omit [Fintype V] [DecidableEq V] in
private lemma iso_edist_eq {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (u v : V) : G.edist u v = H.edist (e u) (e v) := by
  refine le_antisymm ?_ ?_
  · rw [SimpleGraph.edist_eq_sInf]
    apply le_sInf
    rintro _ ⟨w, rfl⟩
    have h1 := G.edist_le ((w.map e.symm.toHom).copy (e.symm_apply_apply u) (e.symm_apply_apply v))
    simpa [SimpleGraph.edist_eq_sInf] using h1
  · rw [SimpleGraph.edist_eq_sInf]
    apply le_sInf
    rintro _ ⟨w, rfl⟩
    have h1 := H.edist_le (w.map e.toHom)
    simpa [SimpleGraph.edist_eq_sInf] using h1

omit [Fintype V] [DecidableEq V] in
private lemma iso_radius_eq {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : G.radius = H.radius := by
  simp only [SimpleGraph.radius, SimpleGraph.eccent]
  refine le_antisymm ?_ ?_
  · refine le_iInf fun u => iInf_le_of_le (e.symm u) (iSup_le fun v => ?_)
    have heq : G.edist (e.symm u) v = H.edist u (e v) := by
      simpa using iso_edist_eq e (e.symm u) v
    rw [heq]
    exact le_iSup (fun w => H.edist u w) (e v)
  · refine le_iInf fun u => iInf_le_of_le (e u) (iSup_le fun v => ?_)
    have heq : H.edist (e u) v = G.edist u (e.symm v) := by
      simpa using (iso_edist_eq e u (e.symm v)).symm
    rw [heq]
    exact le_iSup (fun w => G.edist u w) (e.symm v)

omit [Fintype V] [DecidableEq V] in
private lemma dist_getVert_le_of_le {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ p.length) :
    G.dist (p.getVert a) (p.getVert b) ≤ b - a := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha
    simp
  | succ b ih =>
    rcases eq_or_lt_of_le hab with rfl | hlt
    · simp
    · have hab' : a ≤ b := by omega
      have hb' : b ≤ p.length := by omega
      have hadj : G.Adj (p.getVert b) (p.getVert (b + 1)) := p.adj_getVert_succ (by omega)
      have htri : G.dist (p.getVert a) (p.getVert (b + 1)) ≤
          G.dist (p.getVert a) (p.getVert b) + G.dist (p.getVert b) (p.getVert (b + 1)) :=
        hadj.reachable.dist_triangle_right _
      have h1 : G.dist (p.getVert b) (p.getVert (b + 1)) = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr hadj
      have hih := ih hab' hb'
      omega

omit [Fintype V] [DecidableEq V] in
private lemma dist_getVert_le {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) ≤ max i j - min i j := by
  rcases le_total i j with hij | hji
  · rw [max_eq_right hij, min_eq_left hij]
    exact dist_getVert_le_of_le p hij hj
  · rw [max_eq_left hji, min_eq_right hji, SimpleGraph.dist_comm]
    exact dist_getVert_le_of_le p hji hi

omit [Fintype V] [DecidableEq V] in
private lemma dist_getVert_left {G : SimpleGraph V} (hG : G.Connected) {u v : V}
    {p : G.Walk u v} (hp : p.length = G.dist u v) {i : ℕ} (hi : i ≤ p.length) :
    G.dist u (p.getVert i) = i := by
  have hle1 : G.dist u (p.getVert i) ≤ i := by
    simpa [Walk.getVert_zero] using dist_getVert_le_of_le p (Nat.zero_le i) hi
  have hle2 : G.dist (p.getVert i) v ≤ p.length - i := by
    simpa [Walk.getVert_length] using dist_getVert_le_of_le p hi le_rfl
  have htri : G.dist u v ≤ G.dist u (p.getVert i) + G.dist (p.getVert i) v := hG.dist_triangle
  omega

omit [Fintype V] [DecidableEq V] in
private lemma dist_getVert_right {G : SimpleGraph V} (hG : G.Connected) {u v : V}
    {p : G.Walk u v} (hp : p.length = G.dist u v) {i : ℕ} (hi : i ≤ p.length) :
    G.dist (p.getVert i) v = p.length - i := by
  have hle1 : G.dist u (p.getVert i) = i := dist_getVert_left hG hp hi
  have hle2 : G.dist (p.getVert i) v ≤ p.length - i := by
    simpa [Walk.getVert_length] using dist_getVert_le_of_le p hi le_rfl
  have htri : G.dist u v ≤ G.dist u (p.getVert i) + G.dist (p.getVert i) v := hG.dist_triangle
  omega

private def walkInduce {G : SimpleGraph V} {s : Set V} :
    ∀ {u v : V} (p : G.Walk u v) (hp : ∀ w ∈ p.support, w ∈ s),
      (G.induce s).Walk ⟨u, hp u p.start_mem_support⟩ ⟨v, hp v p.end_mem_support⟩
  | _, _, .nil, _ => .nil
  | _, _, @Walk.cons _ _ u' v' w' hadj p, hp =>
    Walk.cons
      (show (G.induce s).Adj ⟨u', hp u' (List.mem_cons_self ..)⟩
        ⟨v', hp v' (List.mem_cons_of_mem _ p.start_mem_support)⟩ from hadj)
      (walkInduce p (fun w hw => hp w (List.mem_cons_of_mem _ hw)))

omit [Fintype V] [DecidableEq V] in
private lemma walkInduce_length {G : SimpleGraph V} {s : Set V} :
    ∀ {u v : V} (p : G.Walk u v) (hp : ∀ w ∈ p.support, w ∈ s),
      (walkInduce p hp).length = p.length
  | _, _, .nil, _ => rfl
  | _, _, .cons _ p, hp => by
    simp [walkInduce, walkInduce_length p]

omit [Fintype V] [DecidableEq V] in
private lemma dist_le_induce_dist {G : SimpleGraph V} {s : Set V}
    {u v : s} (hr : (G.induce s).Reachable u v) :
    G.dist u.1 v.1 ≤ (G.induce s).dist u v := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  rw [← hp]
  have hmap : (p.map (Embedding.induce s).toHom).length = p.length := Walk.length_map _ _
  rw [← hmap]
  exact G.dist_le _

omit [DecidableEq V] in
private lemma largestInducedTreeSize_ge_of_induce {G : SimpleGraph V}
    (S : Set V) [Fintype S] [DecidableEq S] :
    largestInducedTreeSize (G.induce S) ≤ largestInducedTreeSize G := by
  unfold largestInducedTreeSize
  by_cases hne :
      ({ n | ∃ t : Finset S, t.card = n ∧ ((G.induce S).induce (t : Set S)).IsTree }).Nonempty
  · apply csSup_le hne
    rintro n ⟨t, rfl, ht⟩
    let t' : Finset V := t.map ⟨Subtype.val, Subtype.val_injective⟩
    have hcard : t'.card = t.card := Finset.card_map _
    rw [← hcard]
    apply card_le_largestInducedTreeSize
    let e : ((G.induce S).induce (t : Set S)) ≃g (G.induce (t' : Set V)) :=
      { toFun := fun x => ⟨x.1.1, by
          simp only [Finset.mem_coe, t', Finset.mem_map, Function.Embedding.coeFn_mk]
          exact ⟨x.1, x.2, rfl⟩⟩
        invFun := fun y =>
          ⟨⟨y.1, by
              have hy := y.2
              simp only [Finset.mem_coe, t', Finset.mem_map, Function.Embedding.coeFn_mk] at hy
              obtain ⟨a, _, hval⟩ := hy
              rw [← hval]
              exact a.2⟩,
            by
              have hy := y.2
              simp only [Finset.mem_coe, t', Finset.mem_map, Function.Embedding.coeFn_mk] at hy
              obtain ⟨a, ha, hval⟩ := hy
              have hsub : (⟨y.1, by rw [← hval]; exact a.2⟩ : S) = a := Subtype.ext hval.symm
              rw [hsub]
              exact ha⟩
        left_inv := fun x => by ext; rfl
        right_inv := fun y => by ext; rfl
        map_rel_iff' := by intro a b; rfl }
    exact (e.isTree_iff).mp ht
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, csSup_empty]
    exact Nat.zero_le _

omit [Fintype V] [DecidableEq V] in
private lemma iso_largestInducedTreeSize_le {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    largestInducedTreeSize G ≤ largestInducedTreeSize H := by
  unfold largestInducedTreeSize
  by_cases hne :
      ({ n | ∃ t : Finset V, t.card = n ∧ (G.induce (t : Set V)).IsTree }).Nonempty
  · apply csSup_le hne
    rintro n ⟨t, rfl, ht⟩
    let t' : Finset W := t.map ⟨f, f.injective⟩
    have hcard : t'.card = t.card := Finset.card_map _
    rw [← hcard]
    apply card_le_largestInducedTreeSize
    let ef : (G.induce (t : Set V)) ≃g (H.induce (t' : Set W)) :=
      { toFun := fun x => ⟨f x.1, by
          simp only [Finset.mem_coe, t', Finset.mem_map, Function.Embedding.coeFn_mk]
          exact ⟨x.1, x.2, rfl⟩⟩
        invFun := fun y => ⟨f.symm y.1, by
          have hy := y.2
          simp only [Finset.mem_coe, t', Finset.mem_map, Function.Embedding.coeFn_mk] at hy
          obtain ⟨a, ha, hval⟩ := hy
          have : f.symm y.1 = a := by rw [← hval]; exact f.symm_apply_apply a
          rw [this]
          exact ha⟩
        left_inv := fun x => by apply Subtype.ext; exact f.symm_apply_apply x.1
        right_inv := fun y => by apply Subtype.ext; exact f.apply_symm_apply y.1
        map_rel_iff' := by intro a b; exact f.map_rel_iff }
    exact (ef.isTree_iff).mp ht
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, csSup_empty]
    exact Nat.zero_le _

private lemma iso_largestInducedTreeSize_eq {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    largestInducedTreeSize G = largestInducedTreeSize H :=
  le_antisymm (iso_largestInducedTreeSize_le e) (iso_largestInducedTreeSize_le e.symm)

omit [Fintype V] [DecidableEq V] in
private lemma isTree_singleton {G : SimpleGraph V} (v : V) :
    (G.induce (({v} : Finset V) : Set V)).IsTree := by
  have : Nonempty ↥(({v} : Finset V) : Set V) := ⟨⟨v, by simp⟩⟩
  have : Subsingleton ↥(({v} : Finset V) : Set V) := ⟨fun a b => by
    apply Subtype.ext
    have ha : (a : V) = v := by simpa using a.2
    have hb : (b : V) = v := by simpa using b.2
    exact ha.trans hb.symm⟩
  exact IsTree.of_subsingleton

private lemma two_le_largestInducedTreeSize_of_adj {G : SimpleGraph V}
    {u v : V} (hadj : G.Adj u v) :
    2 ≤ largestInducedTreeSize G := by
  have hne : v ∉ ({u} : Finset V) := by simp [hadj.ne.symm]
  have hT : (G.induce ((insert v {u} : Finset V) : Set V)).IsTree := by
    refine IsTree.induce_insert_of_unique_adj (isTree_singleton u) hne
      (Finset.mem_singleton_self u) hadj.symm ?_
    intro b hb _
    exact Finset.mem_singleton.mp hb
  have hcard : (insert v ({u} : Finset V)).card = 2 := by
    rw [Finset.card_insert_of_notMem hne, Finset.card_singleton]
  have hle := card_le_largestInducedTreeSize hT
  omega

omit [Fintype V] in
/-- Attach a chain `f 1, ..., f k` onto an induced tree `T` containing `f 0`, where each
`f (t + 1)` is new and has unique neighbor `f t` in `T ∪ {f 1, ..., f t}`. -/
private lemma induce_attach_chain_isTree {G : SimpleGraph V} {T : Finset V}
    (hT : (G.induce (T : Set V)).IsTree)
    (k : ℕ) (f : ℕ → V)
    (hf0 : f 0 ∈ T)
    (hdisj : ∀ i, 1 ≤ i → i ≤ k → f i ∉ T)
    (hinj : Set.InjOn f (Set.Icc 0 k))
    (hadj : ∀ i < k, G.Adj (f i) (f (i + 1)))
    (huniq_T : ∀ i, 1 ≤ i → i ≤ k → ∀ w ∈ T, G.Adj (f i) w → i = 1 ∧ w = f 0)
    (huniq_chain : ∀ i j, 1 ≤ j → j < i → i ≤ k → G.Adj (f i) (f j) → j + 1 = i) :
    let S := T ∪ (Finset.Icc 1 k).image f
    (G.induce (S : Set V)).IsTree ∧ S.card = T.card + k := by
  induction k with
  | zero =>
    have hIcc : Finset.Icc 1 0 = ∅ := Finset.Icc_eq_empty (by omega)
    dsimp only
    rw [hIcc, Finset.image_empty, Finset.union_empty, add_zero]
    exact ⟨hT, rfl⟩
  | succ k ih =>
    have hprev := ih
      (fun i h1 h2 => hdisj i h1 (by omega))
      (hinj.mono (show Set.Icc 0 k ⊆ Set.Icc 0 (k + 1) from fun x hx => ⟨hx.1, Nat.le_succ_of_le hx.2⟩))
      (fun i hi => hadj i (by omega))
      (fun i h1 h2 w hw ha => huniq_T i h1 (by omega) w hw ha)
      (fun i j h1 h2 h3 ha => huniq_chain i j h1 h2 (by omega) ha)
    set S_prev := T ∪ (Finset.Icc 1 k).image f
    have hS_eq : T ∪ (Finset.Icc 1 (k + 1)).image f = insert (f (k + 1)) S_prev := by
      ext x
      simp only [S_prev, Finset.mem_union, Finset.mem_image, Finset.mem_Icc, Finset.mem_insert]
      constructor
      · rintro (hx | ⟨i, ⟨h1, h2⟩, rfl⟩)
        · exact Or.inr (Or.inl hx)
        · rcases eq_or_lt_of_le h2 with rfl | hlt
          · exact Or.inl rfl
          · exact Or.inr (Or.inr ⟨i, ⟨h1, by omega⟩, rfl⟩)
      · rintro (rfl | hx | ⟨i, ⟨h1, h2⟩, rfl⟩)
        · exact Or.inr ⟨k + 1, ⟨by omega, le_rfl⟩, rfl⟩
        · exact Or.inl hx
        · exact Or.inr ⟨i, ⟨h1, by omega⟩, rfl⟩
    have hnotmem : f (k + 1) ∉ S_prev := by
      simp only [S_prev, Finset.mem_union, Finset.mem_image, Finset.mem_Icc, not_or, not_exists,
        not_and]
      refine ⟨hdisj (k + 1) (by omega) le_rfl, fun i ⟨h1, h2⟩ heq => ?_⟩
      have := hinj ⟨by omega, by omega⟩ ⟨by omega, le_rfl⟩ heq
      omega
    have hfk_mem : f k ∈ S_prev := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact Finset.mem_union_left _ hf0
      · exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk, le_rfl⟩, rfl⟩)
    have htree_next : (G.induce ((insert (f (k + 1)) S_prev : Finset V) : Set V)).IsTree := by
      refine IsTree.induce_insert_of_unique_adj hprev.1 hnotmem hfk_mem (hadj k (by omega)).symm ?_
      intro b hb hba
      simp only [S_prev, Finset.mem_union, Finset.mem_image, Finset.mem_Icc] at hb
      rcases hb with hbT | ⟨j, ⟨h1, h2⟩, rfl⟩
      · obtain ⟨hk0, rfl⟩ := huniq_T (k + 1) (by omega) le_rfl b hbT hba
        have : k = 0 := by omega
        subst this
        rfl
      · have hj := huniq_chain (k + 1) j h1 (by omega) le_rfl hba
        have : j = k := by omega
        subst this
        rfl
    rw [hS_eq]
    refine ⟨htree_next, ?_⟩
    rw [Finset.card_insert_of_notMem hnotmem, hprev.2]
    omega

/-- An induced path of `n + 1` vertices gives an induced tree of size `n + 1`. -/
private lemma induced_path_card_le_tree {G : SimpleGraph V} (n : ℕ) (f : ℕ → V)
    (hinj : Set.InjOn f (Set.Icc 0 n))
    (hadj : ∀ i < n, G.Adj (f i) (f (i + 1)))
    (hchord : ∀ i j, j < i → i ≤ n → G.Adj (f i) (f j) → j + 1 = i) :
    n + 1 ≤ largestInducedTreeSize G := by
  have h := induce_attach_chain_isTree (isTree_singleton (G := G) (f 0)) n f
    (Finset.mem_singleton_self _)
    (fun i h1 h2 hmem => by
      have heq : f i = f 0 := Finset.mem_singleton.mp hmem
      have := hinj ⟨by omega, h2⟩ ⟨le_rfl, by omega⟩ heq
      omega)
    hinj hadj
    (fun i h1 h2 w hw ha => by
      have hw0 : w = f 0 := Finset.mem_singleton.mp hw
      subst hw0
      have := hchord i 0 (by omega) h2 ha
      exact ⟨by omega, rfl⟩)
    (fun i j _ h2 h3 ha => hchord i j h2 h3 ha)
  have hcard : ({f 0} ∪ (Finset.Icc 1 n).image f).card = 1 + n := by
    simpa using h.2
  have hle := card_le_largestInducedTreeSize h.1
  omega

private lemma geodesic_tree_bound {G : SimpleGraph V} (hG : G.Connected) :
    G.radius.toNat + 1 ≤ largestInducedTreeSize G := by
  have : Nonempty V := hG.nonempty
  obtain ⟨u, v, huv⟩ := G.exists_edist_eq_radius_of_finite
  have hdist : G.dist u v = G.radius.toNat := by
    rw [SimpleGraph.dist, huv]
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u v
  have hlen : p.length = G.radius.toNat := hp.trans hdist
  have hpath : p.IsPath := p.isPath_of_length_eq_dist hp
  have hle := induced_path_card_le_tree p.length p.getVert
    (fun i hi j hj heq => hpath.getVert_injOn hi.2 hj.2 heq)
    (fun i hi => p.adj_getVert_succ hi)
    (fun i j hji hi hadj => by
      have hdi : G.dist u (p.getVert i) = i := dist_getVert_left hG hp hi
      have hdj : G.dist u (p.getVert j) = j := dist_getVert_left hG hp (by omega)
      have htri : G.dist u (p.getVert i) ≤
          G.dist u (p.getVert j) + G.dist (p.getVert j) (p.getVert i) := hG.dist_triangle
      have h1 : G.dist (p.getVert j) (p.getVert i) = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
      omega)
  omega

omit [Fintype V] [DecidableEq V] in
/-- A vertex maximizing distance from a fixed vertex `a` is not a cut vertex. -/
private lemma induce_erase_connected_of_max_dist {G : SimpleGraph V} (hG : G.Connected)
    (a x : V) (hax : x ≠ a) (hmax : ∀ u : V, G.dist a u ≤ G.dist a x) :
    (G.induce ({x}ᶜ : Set V)).Connected := by
  have ha : a ∈ ({x}ᶜ : Set V) := by simp [Ne.symm hax]
  have : Nonempty ({x}ᶜ : Set V) := ⟨⟨a, ha⟩⟩
  refine SimpleGraph.Connected.mk ?_
  intro u v
  have hreach_a : ∀ z : ({x}ᶜ : Set V), (G.induce ({x}ᶜ : Set V)).Reachable ⟨a, ha⟩ z := by
    intro z
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist a z.1
    refine ⟨walkInduce p ?_⟩
    intro w hw
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hwx
    subst hwx
    obtain ⟨i, hpi, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hw
    have hdi : G.dist a (p.getVert i) = i := dist_getVert_left hG hp hi
    have hne_end : i < p.length := by
      by_contra hge
      have hieq : i = p.length := by omega
      subst hieq
      rw [Walk.getVert_length] at hpi
      exact z.2 hpi
    rw [hpi] at hdi
    have hle := hmax z.1
    omega
  exact (hreach_a u).symm.trans (hreach_a v)

/-- Layer-size lemma: every connected finite graph has at least `2 * rad(G)` vertices. -/
private lemma two_mul_radius_le_card {G : SimpleGraph V} (hG : G.Connected) :
    2 * G.radius.toNat ≤ Fintype.card V := by
  set r := G.radius.toNat
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · omega
  obtain ⟨u, hu⟩ := exists_center_dist_le hG
  let L : ℕ → Finset V := fun i => Finset.univ.filter (fun w => G.dist u w = i)
  have hL0 : 1 ≤ (L 0).card := by
    refine Finset.card_pos.mpr ⟨u, ?_⟩
    simp [L]
  have hLr : 1 ≤ (L r).card := by
    obtain ⟨v, hv⟩ := exists_dist_ge_radius hG u
    have hveq : G.dist u v = r := le_antisymm (hu v) hv
    exact Finset.card_pos.mpr ⟨v, by simp [L, hveq]⟩
  have hLi : ∀ i, 1 ≤ i → i < r → 2 ≤ (L i).card := by
    intro i hi1 hir
    obtain ⟨v, hv⟩ := exists_dist_ge_radius hG u
    have hveq : G.dist u v = r := le_antisymm (hu v) hv
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u v
    have hplen : p.length = r := hp.trans hveq
    have hi_le_p : i ≤ p.length := by omega
    have hxi : p.getVert i ∈ L i := by
      simp [L, dist_getVert_left hG hp hi_le_p]
    by_contra hlt
    have hcard1 : (L i).card = 1 := by
      have hpos : 1 ≤ (L i).card := Finset.card_pos.mpr ⟨_, hxi⟩
      omega
    obtain ⟨x, hxL⟩ := Finset.card_eq_one.mp hcard1
    have hux : G.dist u x = i := by
      have : x ∈ L i := by rw [hxL]; exact Finset.mem_singleton_self x
      exact (Finset.mem_filter.mp this).2
    obtain ⟨q, hq⟩ := hG.exists_walk_length_eq_dist u x
    have hqlen : q.length = i := hq.trans hux
    set a := q.getVert 1
    have hua : G.dist u a = 1 := dist_getVert_left hG hq (by omega)
    have hax : G.dist a x = i - 1 := by
      have h1 := dist_getVert_right hG hq (by omega : 1 ≤ q.length)
      change G.dist a x = q.length - 1 at h1
      omega
    have ha_le : ∀ w : V, G.dist a w ≤ r - 1 := by
      intro w
      by_cases hltw : G.dist u w < i
      · have htri : G.dist a w ≤ G.dist a u + G.dist u w := hG.dist_triangle
        rw [SimpleGraph.dist_comm (u := a) (v := u), hua] at htri
        omega
      · obtain ⟨pw, hpw⟩ := hG.exists_walk_length_eq_dist u w
        have hi_le : i ≤ pw.length := by omega
        have hmem : pw.getVert i ∈ L i := by
          simp [L, dist_getVert_left hG hpw hi_le]
        rw [hxL, Finset.mem_singleton] at hmem
        have hxw : G.dist x w = G.dist u w - i := by
          have := dist_getVert_right hG hpw hi_le
          rw [hmem] at this
          omega
        have htri : G.dist a w ≤ G.dist a x + G.dist x w := hG.dist_triangle
        have huw : G.dist u w ≤ r := hu w
        omega
    have hrad := radius_toNat_le_of_exists hG ⟨a, ha_le⟩
    omega
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (r + 1)) : Set ℕ) L := by
    intro i _ j _ hij
    change Disjoint (L i) (L j)
    rw [Finset.disjoint_left]
    intro w hwi hwj
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hwi hwj
    exact hij (hwi.symm.trans hwj)
  have hsum_le : ∑ i ∈ Finset.range (r + 1), (L i).card ≤ Fintype.card V := by
    rw [← Finset.card_biUnion hdisj]
    exact Finset.card_le_univ _
  have hsum_ge : 2 * r ≤ ∑ i ∈ Finset.range (r + 1), (L i).card := by
    have hsplit : ∑ i ∈ Finset.range (r + 1), (L i).card =
        (L 0).card + (∑ i ∈ Finset.Ico 1 r, (L i).card) + (L r).card := by
      rw [Finset.sum_range_succ, Finset.sum_range_eq_add_Ico _ hrpos]
    rw [hsplit]
    have hmid : ∑ i ∈ Finset.Ico 1 r, 2 ≤ ∑ i ∈ Finset.Ico 1 r, (L i).card :=
      Finset.sum_le_sum fun i hi => hLi i (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2
    simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul] at hmid
    omega
  omega

end BasicHelpers

section ChungTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Chung's / Erdős–Saks–Sós induced path bound: every connected finite graph of radius `r`
contains an induced tree (in fact, an induced path) on at least `2 * r - 1` vertices. -/
private lemma chung_induced_tree_bound {G : SimpleGraph V} (hG : G.Connected) :
    2 * G.radius.toNat - 1 ≤ largestInducedTreeSize G := by
  set r := G.radius.toNat
  by_cases hr2 : r ≤ 2
  · rcases eq_or_lt_of_le hr2 with hr2eq | hrlt2
    · have hgeo := geodesic_tree_bound hG
      omega
    · rcases Nat.eq_zero_or_pos r with hr0 | hr1
      · omega
      · have : Nonempty V := hG.nonempty
        have h1 := one_le_largestInducedTreeSize G
        omega
  have hr3 : 3 ≤ r := by omega
  let P : ℕ → Prop := fun n =>
    ∃ S : Finset V, S.card = n ∧ (G.induce (S : Set V)).Connected ∧
      r ≤ (G.induce (S : Set V)).radius.toNat
  have hP_ex : ∃ n, P n := by
    let e : G.induce ((Finset.univ : Finset V) : Set V) ≃g G :=
      { toFun := Subtype.val
        invFun := fun x => ⟨x, Finset.mem_univ x⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := by intro a b; rfl }
    refine ⟨Fintype.card V, Finset.univ, Finset.card_univ, e.connected_iff.mpr hG, ?_⟩
    rw [iso_radius_eq e]
  classical
  let m := Nat.find hP_ex
  obtain ⟨S, hScard, hHconn, hHrad⟩ := Nat.find_spec hP_ex
  have hSmin : ∀ S' : Finset V, S'.card < S.card → (G.induce (S' : Set V)).Connected →
      (G.induce (S' : Set V)).radius.toNat < r := by
    intro S' hlt hconn'
    by_contra hge
    push Not at hge
    have hP' : P S'.card := ⟨S', rfl, hconn', hge⟩
    have := Nat.find_min hP_ex (by omega : S'.card < m)
    exact this hP'
  set H := G.induce (S : Set V)
  have : Nonempty (S : Set V) := hHconn.nonempty
  let a : (S : Set V) := Classical.arbitrary _
  obtain ⟨vr, _, hvr_max⟩ := Finset.exists_max_image (Finset.univ : Finset (S : Set V))
    (fun u => H.dist a u) Finset.univ_nonempty
  have hvr_ne_a : vr ≠ a := by
    intro heq
    have hle0 : ∀ u : (S : Set V), H.dist a u ≤ 0 := by
      intro u
      have := hvr_max u (Finset.mem_univ u)
      simpa [heq] using this
    have := radius_toNat_le_of_exists hHconn ⟨a, hle0⟩
    omega
  have hH'_conn : (H.induce ({vr}ᶜ : Set (S : Set V))).Connected :=
    induce_erase_connected_of_max_dist hHconn a vr hvr_ne_a (fun u => hvr_max u (Finset.mem_univ u))
  let S' := S.erase vr.1
  let e' : H.induce ({vr}ᶜ : Set (S : Set V)) ≃g G.induce (S' : Set V) :=
    { toFun := fun x => ⟨x.1.1, by
        simp only [S', Finset.mem_coe, Finset.mem_erase]
        refine ⟨?_, x.1.2⟩
        intro hval
        exact x.2 (Subtype.ext hval)⟩
      invFun := fun y => ⟨⟨y.1, (Finset.mem_erase.mp y.2).2⟩, by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hsub
        exact (Finset.mem_erase.mp y.2).1 (congrArg Subtype.val hsub)⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun y => by ext; rfl
      map_rel_iff' := by intro x y; rfl }
  have hS'_conn : (G.induce (S' : Set V)).Connected := e'.connected_iff.mp hH'_conn
  have hS'_card : S'.card < S.card := Finset.card_erase_lt_of_mem vr.2
  have hS'_rad : (G.induce (S' : Set V)).radius.toNat < r := hSmin S' hS'_card hS'_conn
  have hH'_rad : (H.induce ({vr}ᶜ : Set (S : Set V))).radius.toNat < r := by
    rw [iso_radius_eq e']
    exact hS'_rad
  obtain ⟨v0', hv0'⟩ := exists_center_dist_le hH'_conn
  set v0 : (S : Set V) := v0'.1
  have hv0_le : ∀ u : (S : Set V), u ≠ vr → H.dist v0 u ≤ r - 1 := by
    intro u hu
    have h1 := dist_le_induce_dist (G := H) (s := ({vr}ᶜ : Set (S : Set V)))
      (u := v0') (v := ⟨u, hu⟩) (hH'_conn v0' ⟨u, hu⟩)
    have h2 := hv0' ⟨u, hu⟩
    change H.dist v0 u ≤ (H.induce ({vr}ᶜ : Set (S : Set V))).dist v0' ⟨u, hu⟩ at h1
    omega
  have hv0_vr_ge : r ≤ H.dist v0 vr := by
    obtain ⟨y, hy⟩ := exists_dist_ge_radius hHconn v0
    by_cases hyv : y = vr
    · subst hyv; omega
    · have := hv0_le y hyv; omega
  have hv0_vr_le : H.dist v0 vr ≤ r := by
    have hv0_ne_vr : v0 ≠ vr := v0'.2
    obtain ⟨q0, hq0⟩ := hHconn.exists_walk_length_eq_dist v0 vr
    have hq0_pos : 0 < q0.length := by
      have := hHconn.pos_dist_of_ne hv0_ne_vr
      omega
    set u := q0.getVert (q0.length - 1)
    have hu_adj : H.Adj u vr := by
      have := q0.adj_getVert_succ (by omega : q0.length - 1 < q0.length)
      simpa [show q0.length - 1 + 1 = q0.length by omega, Walk.getVert_length] using this
    have hu_ne : u ≠ vr := hu_adj.ne
    have htri : H.dist v0 vr ≤ H.dist v0 u + H.dist u vr := hHconn.dist_triangle
    have h1 : H.dist u vr = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hu_adj
    have h2 : H.dist v0 u ≤ r - 1 := hv0_le u hu_ne
    omega
  have hv0_vr : H.dist v0 vr = r := le_antisymm hv0_vr_le hv0_vr_ge
  obtain ⟨q, hq⟩ := hHconn.exists_walk_length_eq_dist v0 vr
  have hqlen : q.length = r := hq.trans hv0_vr
  set v : ℕ → (S : Set V) := q.getVert
  have hv_dist0 : ∀ i ≤ r, H.dist v0 (v i) = i := fun i hi =>
    dist_getVert_left hHconn hq (by omega)
  have hv_dist2 : ∀ i ≤ r, H.dist (v 2) (v i) ≤ max 2 i - min 2 i := fun i hi =>
    dist_getVert_le q (by omega) (by omega)
  obtain ⟨x, hx_ge⟩ := exists_dist_ge_radius hHconn (v 2)
  have hx_ge_r : r ≤ H.dist (v 2) x := le_trans hHrad hx_ge
  have hx_ne_vr : x ≠ vr := by
    intro heq
    have h1 : v r = vr := by simp [v, ← hqlen]
    have h2 := hv_dist2 r le_rfl
    rw [h1, ← heq] at h2
    omega
  set ℓ := H.dist v0 x
  have hℓ_le : ℓ ≤ r - 1 := hv0_le x hx_ne_vr
  have hℓ_ge : r - 2 ≤ ℓ := by
    have htri : H.dist (v 2) x ≤ H.dist (v 2) v0 + H.dist v0 x := hHconn.dist_triangle
    have h20 : H.dist (v 2) v0 = 2 := by
      rw [SimpleGraph.dist_comm]
      exact hv_dist0 2 (by omega)
    omega
  obtain ⟨p, hp⟩ := hHconn.exists_walk_length_eq_dist v0 x
  have hplen : p.length = ℓ := hp
  set w : ℕ → (S : Set V) := p.getVert
  have hw_dist0 : ∀ j ≤ ℓ, H.dist v0 (w j) = j := fun j hj =>
    dist_getVert_left hHconn hp (by omega)
  have hw_distx : ∀ j ≤ ℓ, H.dist (w j) x = ℓ - j := fun j hj => by
    have h1 := dist_getVert_right hHconn hp (by omega : j ≤ p.length)
    change H.dist (w j) x = p.length - j at h1
    omega
  have hdisj_vw : ∀ i j, 1 ≤ i → i ≤ r → 1 ≤ j → j ≤ ℓ → v i ≠ w j := by
    intro i j hi1 hir hj1 hjℓ heq
    have hij : i = j := by
      have h1 := hv_dist0 i hir
      have h2 := hw_dist0 j hjℓ
      rw [heq] at h1
      omega
    subst hij
    have htri : H.dist (v 2) x ≤ H.dist (v 2) (v i) + H.dist (v i) x := hHconn.dist_triangle
    have h1 := hv_dist2 i hir
    have h2 : H.dist (v i) x = ℓ - i := by rw [heq]; exact hw_distx i hjℓ
    omega
  have hcross : ∀ i j, 1 ≤ i → i ≤ r → 1 ≤ j → j ≤ ℓ → H.Adj (v i) (w j) →
      i = 1 ∧ j = 1 ∧ ℓ = r - 1 := by
    intro i j hi1 hir hj1 hjℓ hadj
    have hi_le : i ≤ j + 1 := by
      have htri : H.dist v0 (v i) ≤ H.dist v0 (w j) + H.dist (w j) (v i) := hHconn.dist_triangle
      have h1 : H.dist (w j) (v i) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
      have h2 := hv_dist0 i hir
      have h3 := hw_dist0 j hjℓ
      omega
    have htri2 : H.dist (v 2) x ≤ H.dist (v 2) (v i) + H.dist (v i) x := hHconn.dist_triangle
    have htri3 : H.dist (v i) x ≤ H.dist (v i) (w j) + H.dist (w j) x := hHconn.dist_triangle
    have h1 : H.dist (v i) (w j) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
    have h2 := hv_dist2 i hir
    have h3 := hw_distx j hjℓ
    omega
  suffices htreeH : 2 * r - 1 ≤ largestInducedTreeSize H by
    exact le_trans htreeH (largestInducedTreeSize_ge_of_induce (S : Set V))
  by_cases hadj11 : H.Adj (v 1) (w 1)
  · have hℓ_eq : ℓ = r - 1 := (hcross 1 1 le_rfl (by omega) le_rfl (by omega) hadj11).2.2
    let f : ℕ → (S : Set V) := fun t =>
      if t < ℓ then w (ℓ - t) else v (t - ℓ + 1)
    have hbound := induced_path_card_le_tree (G := H) (ℓ + r - 1) f ?_ ?_ ?_
    · omega
    · intro a ha b hb heq
      simp only [Set.mem_Icc] at ha hb
      dsimp only [f] at heq
      split_ifs at heq with ha' hb' hb'
      · have h1 := hw_dist0 (ℓ - a) (by omega)
        have h2 := hw_dist0 (ℓ - b) (by omega)
        rw [heq] at h1
        omega
      · exact (hdisj_vw (b - ℓ + 1) (ℓ - a) (by omega) (by omega) (by omega) (by omega) heq.symm).elim
      · exact (hdisj_vw (a - ℓ + 1) (ℓ - b) (by omega) (by omega) (by omega) (by omega) heq).elim
      · have h1 := hv_dist0 (a - ℓ + 1) (by omega)
        have h2 := hv_dist0 (b - ℓ + 1) (by omega)
        rw [heq] at h1
        omega
    · intro i hi
      dsimp only [f]
      by_cases hlt : i + 1 < ℓ
      · rw [if_pos (by omega), if_pos hlt]
        have h1 : ℓ - i = (ℓ - (i + 1)) + 1 := by omega
        rw [h1]
        exact (p.adj_getVert_succ (by omega)).symm
      · by_cases heq : i + 1 = ℓ
        · rw [if_pos (by omega), if_neg (by omega)]
          have h1 : ℓ - i = 1 := by omega
          have h2 : i + 1 - ℓ + 1 = 1 := by omega
          rw [h1, h2]
          exact hadj11.symm
        · rw [if_neg (by omega), if_neg (by omega)]
          have h1 : i + 1 - ℓ + 1 = (i - ℓ + 1) + 1 := by omega
          rw [h1]
          exact q.adj_getVert_succ (by omega)
    · intro i j hji hi hadj
      dsimp only [f] at hadj
      split_ifs at hadj with hi' hj' hj'
      · have h1 := hw_dist0 (ℓ - i) (by omega)
        have h2 := hw_dist0 (ℓ - j) (by omega)
        have htri : H.dist v0 (w (ℓ - j)) ≤ H.dist v0 (w (ℓ - i)) + H.dist (w (ℓ - i)) (w (ℓ - j)) :=
          hHconn.dist_triangle
        have h3 : H.dist (w (ℓ - i)) (w (ℓ - j)) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
        omega
      · omega
      · obtain ⟨hi1, hj1, _⟩ :=
          hcross (i - ℓ + 1) (ℓ - j) (by omega) (by omega) (by omega) (by omega) hadj
        omega
      · have h1 := hv_dist0 (i - ℓ + 1) (by omega)
        have h2 := hv_dist0 (j - ℓ + 1) (by omega)
        have htri : H.dist v0 (v (i - ℓ + 1)) ≤
            H.dist v0 (v (j - ℓ + 1)) + H.dist (v (j - ℓ + 1)) (v (i - ℓ + 1)) :=
          hHconn.dist_triangle
        have h3 : H.dist (v (j - ℓ + 1)) (v (i - ℓ + 1)) = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
        omega
  · let f : ℕ → (S : Set V) := fun t =>
      if t < ℓ then w (ℓ - t) else v (t - ℓ)
    have hbound := induced_path_card_le_tree (G := H) (ℓ + r) f ?_ ?_ ?_
    · omega
    · intro a ha b hb heq
      simp only [Set.mem_Icc] at ha hb
      dsimp only [f] at heq
      split_ifs at heq with ha' hb' hb'
      · have h1 := hw_dist0 (ℓ - a) (by omega)
        have h2 := hw_dist0 (ℓ - b) (by omega)
        rw [heq] at h1
        omega
      · by_cases hb0 : b = ℓ
        · subst hb0
          have h1 := hw_dist0 (ℓ - a) (by omega)
          have h2 : v 0 = v0 := Walk.getVert_zero q
          rw [show ℓ - ℓ = 0 by omega, h2] at heq
          rw [heq, SimpleGraph.dist_self] at h1
          omega
        · exact (hdisj_vw (b - ℓ) (ℓ - a) (by omega) (by omega) (by omega) (by omega) heq.symm).elim
      · by_cases ha0 : a = ℓ
        · subst ha0
          have h1 := hw_dist0 (ℓ - b) (by omega)
          have h2 : v 0 = v0 := Walk.getVert_zero q
          rw [show ℓ - ℓ = 0 by omega, h2] at heq
          rw [← heq, SimpleGraph.dist_self] at h1
          omega
        · exact (hdisj_vw (a - ℓ) (ℓ - b) (by omega) (by omega) (by omega) (by omega) heq).elim
      · have h1 := hv_dist0 (a - ℓ) (by omega)
        have h2 := hv_dist0 (b - ℓ) (by omega)
        rw [heq] at h1
        omega
    · intro i hi
      dsimp only [f]
      by_cases hlt : i + 1 < ℓ
      · rw [if_pos (by omega), if_pos hlt]
        have h1 : ℓ - i = (ℓ - (i + 1)) + 1 := by omega
        rw [h1]
        exact (p.adj_getVert_succ (by omega)).symm
      · by_cases heq : i + 1 = ℓ
        · rw [if_pos (by omega), if_neg (by omega)]
          have h1 : ℓ - i = 1 := by omega
          have h2 : i + 1 - ℓ = 0 := by omega
          rw [h1, h2]
          have hv0q : v 0 = w 0 := by
            show q.getVert 0 = p.getVert 0
            simp
          rw [hv0q]
          exact (p.adj_getVert_succ (by omega)).symm
        · rw [if_neg (by omega), if_neg (by omega)]
          have h1 : i + 1 - ℓ = (i - ℓ) + 1 := by omega
          rw [h1]
          exact q.adj_getVert_succ (by omega)
    · intro i j hji hi hadj
      dsimp only [f] at hadj
      split_ifs at hadj with hi' hj' hj'
      · have h1 := hw_dist0 (ℓ - i) (by omega)
        have h2 := hw_dist0 (ℓ - j) (by omega)
        have htri : H.dist v0 (w (ℓ - j)) ≤ H.dist v0 (w (ℓ - i)) + H.dist (w (ℓ - i)) (w (ℓ - j)) :=
          hHconn.dist_triangle
        have h3 : H.dist (w (ℓ - i)) (w (ℓ - j)) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
        omega
      · omega
      · by_cases hi0 : i = ℓ
        · subst hi0
          have hv0q : v (ℓ - ℓ) = v0 := by simp [v]
          rw [hv0q] at hadj
          have h1 := hw_dist0 (ℓ - j) (by omega)
          have h2 : H.dist v0 (w (ℓ - j)) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
          omega
        · obtain ⟨hi1, hj1, _⟩ :=
            hcross (i - ℓ) (ℓ - j) (by omega) (by omega) (by omega) (by omega) hadj
          rw [hi1, hj1] at hadj
          exact (hadj11 hadj).elim
      · have h1 := hv_dist0 (i - ℓ) (by omega)
        have h2 := hv_dist0 (j - ℓ) (by omega)
        have htri : H.dist v0 (v (i - ℓ)) ≤ H.dist v0 (v (j - ℓ)) + H.dist (v (j - ℓ)) (v (i - ℓ)) :=
          hHconn.dist_triangle
        have h3 : H.dist (v (j - ℓ)) (v (i - ℓ)) = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
        omega

end ChungTheorem

section CutVertexTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

private def IsCutVertex (G : SimpleGraph V) (c : V) : Prop :=
  ¬ (G.induce ({c}ᶜ : Set V)).Connected

private def HasCutVertex (G : SimpleGraph V) : Prop :=
  ∃ c : V, IsCutVertex G c

private def IsCompOfCut (G : SimpleGraph V) (c : V) (K : Set V) : Prop :=
  ∃ a : ({c}ᶜ : Set V), K = {v : V | ∃ hv : v ≠ c, (G.induce ({c}ᶜ : Set V)).Reachable a ⟨v, hv⟩}

private structure PendantData (G : SimpleGraph V) (c : V) where
  K : Set V
  k : ℕ
  p : ℕ → V
  hcK : c ∉ K
  hk : 0 < k
  hp0 : p 0 = c
  hK : K = {v : V | ∃ i, 1 ≤ i ∧ i ≤ k ∧ v = p i}
  hinj : Set.InjOn p (Set.Icc 0 k)
  hadj : ∀ i < k, G.Adj (p i) (p (i + 1))
  hnbr : ∀ i, 1 ≤ i → i ≤ k → ∀ w : V, G.Adj (p i) w → w = p (i - 1) ∨ (i < k ∧ w = p (i + 1))

private def IsPendantPath (G : SimpleGraph V) (c : V) (K : Set V) : Prop :=
  ∃ d : PendantData G c, d.K = K

omit [Fintype V] [DecidableEq V] in
private lemma compOfCut_not_mem {G : SimpleGraph V} {c : V} {K : Set V}
    (hK : IsCompOfCut G c K) : c ∉ K := by
  obtain ⟨a, rfl⟩ := hK
  rintro ⟨hc, _⟩
  exact hc rfl

omit [Fintype V] [DecidableEq V] in
private lemma compOfCut_nonempty {G : SimpleGraph V} {c : V} {K : Set V}
    (hK : IsCompOfCut G c K) : K.Nonempty := by
  obtain ⟨a, rfl⟩ := hK
  exact ⟨a.1, a.2, Reachable.refl a⟩

omit [Fintype V] [DecidableEq V] in
private lemma compOfCut_adj_mem {G : SimpleGraph V} {c : V} {K : Set V}
    (hK : IsCompOfCut G c K) {u w : V} (hu : u ∈ K) (hadj : G.Adj u w) :
    w ∈ K ∨ w = c := by
  obtain ⟨a, rfl⟩ := hK
  obtain ⟨huc, hru⟩ := hu
  by_cases hwc : w = c
  · exact Or.inr hwc
  · refine Or.inl ⟨hwc, hru.trans ?_⟩
    exact Adj.reachable (G := G.induce ({c}ᶜ : Set V)) (u := ⟨u, huc⟩) (v := ⟨w, hwc⟩) hadj

omit [Fintype V] [DecidableEq V] in
private lemma compOfCut_eq_or_disjoint {G : SimpleGraph V} {c : V} {K₁ K₂ : Set V}
    (h1 : IsCompOfCut G c K₁) (h2 : IsCompOfCut G c K₂) :
    K₁ = K₂ ∨ Disjoint K₁ K₂ := by
  obtain ⟨a₁, rfl⟩ := h1
  obtain ⟨a₂, rfl⟩ := h2
  by_cases hreach : (G.induce ({c}ᶜ : Set V)).Reachable a₁ a₂
  · left
    ext v
    constructor
    · rintro ⟨hv, h⟩; exact ⟨hv, hreach.symm.trans h⟩
    · rintro ⟨hv, h⟩; exact ⟨hv, hreach.trans h⟩
  · right
    rw [Set.disjoint_left]
    rintro v ⟨hv, h1⟩ ⟨_, h2⟩
    exact hreach (h1.trans h2.symm)

omit [Fintype V] [DecidableEq V] in
private lemma walk_hits_cut_of_sep {G : SimpleGraph V} {c : V} {K : Set V}
    (hsep : ∀ u ∈ K, ∀ w : V, G.Adj u w → w ∈ K ∨ w = c) :
    ∀ {u v : V} (p : G.Walk u v), u ∈ K → v ∉ K → c ∈ p.support
  | _, _, .nil, hu, hv => (hv hu).elim
  | _, _, .cons hadj q, hu, hv => by
    rcases hsep _ hu _ hadj with hwK | rfl
    · exact List.mem_cons_of_mem _ (walk_hits_cut_of_sep hsep q hwK hv)
    · exact List.mem_cons_of_mem _ q.start_mem_support

omit [Fintype V] in
private lemma dist_through_cut {G : SimpleGraph V} (hG : G.Connected) {c : V} {K : Set V}
    (hsep : ∀ u ∈ K, ∀ w : V, G.Adj u w → w ∈ K ∨ w = c)
    {u v : V} (hu : u ∈ K) (hv : v ∉ K) :
    G.dist u v = G.dist u c + G.dist c v := by
  refine le_antisymm hG.dist_triangle ?_
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u v
  have hc : c ∈ p.support := walk_hits_cut_of_sep hsep p hu hv
  have h1 : G.dist u c ≤ (p.takeUntil c hc).length := G.dist_le _
  have h2 : G.dist c v ≤ (p.dropUntil c hc).length := G.dist_le _
  have hsum : (p.takeUntil c hc).length + (p.dropUntil c hc).length = p.length := by
    rw [← Walk.length_append, Walk.take_spec]
  omega

omit [Fintype V] in
private lemma dist_through_cut_symm {G : SimpleGraph V} (hG : G.Connected) {c : V} {K : Set V}
    (hsep : ∀ u ∈ K, ∀ w : V, G.Adj u w → w ∈ K ∨ w = c)
    {u v : V} (hu : u ∉ K) (hv : v ∈ K) :
    G.dist u v = G.dist u c + G.dist c v := by
  rw [SimpleGraph.dist_comm (u := u) (v := v), dist_through_cut hG hsep hv hu,
    SimpleGraph.dist_comm (u := v) (v := c), SimpleGraph.dist_comm (u := c) (v := u), add_comm]

private lemma not_isCutVertex_of_unique_adj {G : SimpleGraph V} (hG : G.Connected)
    (x a : V) (huniq : ∀ w : V, G.Adj x w → w = a) (hcard : 2 ≤ Fintype.card V) :
    ¬ IsCutVertex G x := by
  intro hcut
  apply hcut
  have hne : ∃ y : V, y ≠ x := by
    have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_ne x
  obtain ⟨y0, hy0⟩ := hne
  have : Nonempty ({x}ᶜ : Set V) := ⟨⟨y0, hy0⟩⟩
  refine SimpleGraph.Connected.mk fun u v => ?_
  obtain ⟨q⟩ := hG u.1 v.1
  let p := q.toPath
  refine ⟨walkInduce p.1 ?_⟩
  intro w hw hwx
  have hwx' : w = x := Set.mem_singleton_iff.mp (by simpa using hwx)
  subst hwx'
  obtain ⟨idx, hidx_eq, hidx_le⟩ := Walk.mem_support_iff_exists_getVert.mp hw
  have hidx_pos : 0 < idx := by
    by_contra h0
    have h0' : idx = 0 := by omega
    subst h0'
    rw [Walk.getVert_zero] at hidx_eq
    exact u.2 hidx_eq
  have hidx_lt : idx < p.1.length := by
    by_contra hge
    have heq : idx = p.1.length := by omega
    subst heq
    rw [Walk.getVert_length] at hidx_eq
    exact v.2 hidx_eq
  have h1 : G.Adj w (p.1.getVert (idx - 1)) := by
    have := p.1.adj_getVert_succ (by omega : idx - 1 < p.1.length)
    rw [show idx - 1 + 1 = idx by omega, hidx_eq] at this
    exact this.symm
  have h2 : G.Adj w (p.1.getVert (idx + 1)) := by
    have := p.1.adj_getVert_succ hidx_lt
    rw [hidx_eq] at this
    exact this
  have hne_adj : p.1.getVert (idx - 1) ≠ p.1.getVert (idx + 1) := by
    intro heq
    have := p.2.getVert_injOn (by omega : idx - 1 ≤ p.1.length) (by omega : idx + 1 ≤ p.1.length) heq
    omega
  exact hne_adj ((huniq _ h1).trans (huniq _ h2).symm)

omit [Fintype V] [DecidableEq V] in
private lemma pendant_sep {G : SimpleGraph V} {c : V} {K : Set V}
    (hP : IsPendantPath G c K) :
    ∀ u ∈ K, ∀ w : V, G.Adj u w → w ∈ K ∨ w = c := by
  obtain ⟨d, rfl⟩ := hP
  intro u hu w hadj
  rw [d.hK] at hu ⊢
  obtain ⟨i, hi1, hik, rfl⟩ := hu
  rcases d.hnbr i hi1 hik w hadj with rfl | ⟨hlt, rfl⟩
  · by_cases hi1' : i = 1
    · subst hi1'; exact Or.inr d.hp0
    · exact Or.inl ⟨i - 1, by omega, by omega, rfl⟩
  · exact Or.inl ⟨i + 1, by omega, by omega, rfl⟩

omit [Fintype V] [DecidableEq V] in
private lemma pendant_isCompOfCut {G : SimpleGraph V} {c : V} {K : Set V}
    (hP : IsPendantPath G c K) : IsCompOfCut G c K := by
  obtain ⟨d, rfl⟩ := hP
  have hne : ∀ i, 1 ≤ i → i ≤ d.k → d.p i ≠ c := by
    intro i h1 h2 heq
    have h0 : d.p i = d.p 0 := heq.trans d.hp0.symm
    have := d.hinj ⟨by omega, h2⟩ ⟨le_rfl, by omega⟩ h0
    omega
  refine ⟨⟨d.p 1, hne 1 le_rfl d.hk⟩, ?_⟩
  rw [d.hK]
  ext v
  constructor
  · rintro ⟨i, hi1, hik, rfl⟩
    refine ⟨hne i hi1 hik, ?_⟩
    have hreach : ∀ j (hj1 : 1 ≤ j) (hjk : j ≤ d.k),
        (G.induce ({c}ᶜ : Set V)).Reachable ⟨d.p 1, hne 1 le_rfl d.hk⟩
          ⟨d.p j, hne j hj1 hjk⟩ := by
      intro j hj1 hjk
      induction j with
      | zero => omega
      | succ j ih =>
        by_cases hj0 : j = 0
        · subst hj0; exact Reachable.refl _
        · exact (ih (by omega) (by omega)).trans
            (Adj.reachable (G := G.induce ({c}ᶜ : Set V)) (d.hadj j (by omega)))
    exact hreach i hi1 hik
  · rintro ⟨hvc, ⟨q⟩⟩
    have hstay : ∀ {a b : ({c}ᶜ : Set V)} (w : (G.induce ({c}ᶜ : Set V)).Walk a b),
        (∃ i, 1 ≤ i ∧ i ≤ d.k ∧ a.1 = d.p i) → (∃ i, 1 ≤ i ∧ i ≤ d.k ∧ b.1 = d.p i) := by
      intro a b w
      induction w with
      | nil => exact id
      | @cons a x b hstep _ ih =>
        intro ha
        apply ih
        obtain ⟨i, hi1, hik, haeq⟩ := ha
        have hstep' : G.Adj (d.p i) x.1 := by simpa [haeq] using hstep
        rcases d.hnbr i hi1 hik x.1 hstep' with heq | ⟨hlt, heq⟩
        · by_cases hi1' : i = 1
          · subst hi1'
            exfalso
            exact x.2 (heq.trans d.hp0)
          · exact ⟨i - 1, by omega, by omega, heq⟩
        · exact ⟨i + 1, by omega, by omega, heq⟩
    exact hstay q ⟨1, le_rfl, d.hk, rfl⟩

omit [Fintype V] in
private lemma pendant_cycle_disjoint {G : SimpleGraph V} {c : V} {K : Set V}
    (hP : IsPendantPath G c K) {v : V} {Z : G.Walk v v} (hZ : Z.IsCycle) :
    ∀ w ∈ Z.support, w ∉ K := by
  obtain ⟨d, rfl⟩ := hP
  intro w hw hmem
  rw [d.hK] at hmem
  let I : Finset ℕ := (Finset.Icc 1 d.k).filter (fun i => d.p i ∈ Z.support)
  have hIne : I.Nonempty := by
    obtain ⟨i, h1, h2, rfl⟩ := hmem
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, hw⟩⟩
  set m := I.max' hIne
  have hm_mem : m ∈ I := Finset.max'_mem I hIne
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm_mem).1).1
  have hmk : m ≤ d.k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm_mem).1).2
  have hpm_supp : d.p m ∈ Z.support := (Finset.mem_filter.mp hm_mem).2
  let R := Z.rotate (d.p m) hpm_supp
  have hR : R.IsCycle := hZ.rotate hpm_supp
  have hsnd_ne : R.snd ≠ R.penultimate := hR.snd_ne_penultimate
  have hsnd_adj : G.Adj (d.p m) R.snd := R.adj_snd hR.not_nil
  have hpen_adj : G.Adj (d.p m) R.penultimate := (R.adj_penultimate hR.not_nil).symm
  have hsnd_supp : R.snd ∈ Z.support :=
    (Z.mem_support_rotate_iff (d.p m) hpm_supp).mp (R.getVert_mem_support 1)
  have hpen_supp : R.penultimate ∈ Z.support :=
    (Z.mem_support_rotate_iff (d.p m) hpm_supp).mp (R.getVert_mem_support (R.length - 1))
  rcases d.hnbr m hm1 hmk R.snd hsnd_adj with h1 | ⟨hlt, h1⟩
  · rcases d.hnbr m hm1 hmk R.penultimate hpen_adj with h2 | ⟨hlt, h2⟩
    · exact hsnd_ne (h1.trans h2.symm)
    · have hm1_mem : m + 1 ∈ I :=
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, h2 ▸ hpen_supp⟩
      have := Finset.le_max' I (m + 1) hm1_mem
      omega
  · have hm1_mem : m + 1 ∈ I :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, h1 ▸ hsnd_supp⟩
    have := Finset.le_max' I (m + 1) hm1_mem
    omega

omit [Fintype V] in
private lemma pendant_path_disjoint {G : SimpleGraph V} {c : V} {K : Set V}
    (hP : IsPendantPath G c K) {u v : V} {q : G.Walk u v} (hq : q.IsPath)
    (hu : u ∉ K) (hv : v ∉ K) :
    ∀ w ∈ q.support, w ∉ K := by
  obtain ⟨d, rfl⟩ := hP
  intro w hw hmem
  rw [d.hK] at hmem hu hv
  let I : Finset ℕ := (Finset.Icc 1 d.k).filter (fun i => d.p i ∈ q.support)
  have hIne : I.Nonempty := by
    obtain ⟨i, h1, h2, rfl⟩ := hmem
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, hw⟩⟩
  set m := I.max' hIne
  have hm_mem : m ∈ I := Finset.max'_mem I hIne
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm_mem).1).1
  have hmk : m ≤ d.k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm_mem).1).2
  have hpm_supp : d.p m ∈ q.support := (Finset.mem_filter.mp hm_mem).2
  obtain ⟨idx, hidx_eq, hidx_le⟩ := Walk.mem_support_iff_exists_getVert.mp hpm_supp
  have hpm_K : d.p m ∈ {v : V | ∃ i, 1 ≤ i ∧ i ≤ d.k ∧ v = d.p i} := ⟨m, hm1, hmk, rfl⟩
  have hidx_pos : 0 < idx := by
    by_contra h0
    have h0' : idx = 0 := by omega
    subst h0'
    rw [Walk.getVert_zero] at hidx_eq
    exact hu (hidx_eq ▸ hpm_K)
  have hidx_lt : idx < q.length := by
    by_contra hge
    have heq : idx = q.length := by omega
    subst heq
    rw [Walk.getVert_length] at hidx_eq
    exact hv (hidx_eq ▸ hpm_K)
  have hprev_adj : G.Adj (d.p m) (q.getVert (idx - 1)) := by
    have := q.adj_getVert_succ (by omega : idx - 1 < q.length)
    rw [show idx - 1 + 1 = idx by omega, hidx_eq] at this
    exact this.symm
  have hnext_adj : G.Adj (d.p m) (q.getVert (idx + 1)) := by
    have := q.adj_getVert_succ hidx_lt
    rw [hidx_eq] at this
    exact this
  have hne : q.getVert (idx - 1) ≠ q.getVert (idx + 1) := by
    intro heq
    have := hq.getVert_injOn (by omega : idx - 1 ≤ q.length) (by omega : idx + 1 ≤ q.length) heq
    omega
  have hprev_supp : q.getVert (idx - 1) ∈ q.support := q.getVert_mem_support _
  have hnext_supp : q.getVert (idx + 1) ∈ q.support := q.getVert_mem_support _
  rcases d.hnbr m hm1 hmk _ hprev_adj with h1 | ⟨hlt, h1⟩
  · rcases d.hnbr m hm1 hmk _ hnext_adj with h2 | ⟨hlt, h2⟩
    · exact hne (h1.trans h2.symm)
    · have hm1_mem : m + 1 ∈ I :=
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, h2 ▸ hnext_supp⟩
      have := Finset.le_max' I (m + 1) hm1_mem
      omega
  · have hm1_mem : m + 1 ∈ I :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, h1 ▸ hprev_supp⟩
    have := Finset.le_max' I (m + 1) hm1_mem
    omega

omit [Fintype V] [DecidableEq V] in
/-- 1-Lipschitz potential proof that distances along a pendant path equal index differences. -/
private lemma pendant_dist_eq {G : SimpleGraph V} (hG : G.Connected) {c : V}
    (d : PendantData G c) {i j : ℕ} (hi : i ≤ d.k) (hj : j ≤ d.k) :
    G.dist (d.p i) (d.p j) = max i j - min i j := by
  classical
  let φ : V → ℕ := fun v =>
    if h : ∃ m, 1 ≤ m ∧ m ≤ d.k ∧ v = d.p m then Classical.choose h else 0
  have hφ_p : ∀ m ≤ d.k, φ (d.p m) = m := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · dsimp only [φ]
      rw [dif_neg]
      rintro ⟨n, hn1, hnk, heq⟩
      have := d.hinj ⟨le_rfl, by omega⟩ ⟨by omega, hnk⟩ heq
      omega
    · have hex : ∃ n, 1 ≤ n ∧ n ≤ d.k ∧ d.p m = d.p n := ⟨m, hmpos, hm, rfl⟩
      dsimp only [φ]
      rw [dif_pos hex]
      have hspec := Classical.choose_spec hex
      exact (d.hinj ⟨by omega, hm⟩ ⟨by omega, hspec.2.1⟩ hspec.2.2).symm
  have hφ_lip : ∀ u v : V, G.Adj u v → max (φ u) (φ v) - min (φ u) (φ v) ≤ 1 := by
    intro u v huv
    by_cases hu : ∃ m, 1 ≤ m ∧ m ≤ d.k ∧ u = d.p m
    · obtain ⟨m, hm1, hmk, rfl⟩ := hu
      rw [hφ_p m hmk]
      rcases d.hnbr m hm1 hmk v huv with rfl | ⟨hlt, rfl⟩
      · rw [hφ_p (m - 1) (by omega)]; omega
      · rw [hφ_p (m + 1) (by omega)]; omega
    · by_cases hv : ∃ m, 1 ≤ m ∧ m ≤ d.k ∧ v = d.p m
      · obtain ⟨m, hm1, hmk, rfl⟩ := hv
        rw [hφ_p m hmk]
        rcases d.hnbr m hm1 hmk u huv.symm with rfl | ⟨hlt, rfl⟩
        · rw [hφ_p (m - 1) (by omega)]; omega
        · rw [hφ_p (m + 1) (by omega)]; omega
      · have h1 : φ u = 0 := dif_neg hu
        have h2 : φ v = 0 := dif_neg hv
        rw [h1, h2]; simp
  have hφ_walk : ∀ {u v : V} (w : G.Walk u v), max (φ u) (φ v) - min (φ u) (φ v) ≤ w.length := by
    intro u v w
    induction w with
    | nil => simp
    | @cons a b d' hab q ih =>
      have hstep := hφ_lip a b hab
      simp only [Walk.length_cons]
      omega
  have hle : ∀ {a b : ℕ}, a ≤ b → b ≤ d.k → G.dist (d.p a) (d.p b) ≤ b - a := by
    intro a b hab hbk
    induction b with
    | zero =>
      have : a = 0 := by omega
      subst this; simp
    | succ b ih =>
      rcases eq_or_lt_of_le hab with rfl | hlt
      · simp
      · have htri : G.dist (d.p a) (d.p (b + 1)) ≤
            G.dist (d.p a) (d.p b) + G.dist (d.p b) (d.p (b + 1)) := hG.dist_triangle
        have h1 : G.dist (d.p b) (d.p (b + 1)) = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.mpr (d.hadj b (by omega))
        have hih := ih (by omega) (by omega)
        omega
  have hge : max i j - min i j ≤ G.dist (d.p i) (d.p j) := by
    obtain ⟨q, hq⟩ := hG.exists_walk_length_eq_dist (d.p i) (d.p j)
    have h1 := hφ_walk q
    rw [hφ_p i hi, hφ_p j hj, hq] at h1
    exact h1
  rcases le_total i j with hij | hji
  · rw [max_eq_right hij, min_eq_left hij] at hge ⊢
    exact le_antisymm (hle hij hj) hge
  · rw [max_eq_left hji, min_eq_right hji] at hge ⊢
    rw [SimpleGraph.dist_comm]
    exact le_antisymm (hle hji hi) (by rwa [SimpleGraph.dist_comm] at hge)

/-- Lemma 2: A component `K` of `G - c` with at most one non-cut vertex of `G` is a pendant path. -/
private lemma pendant_of_at_most_one_noncut {G : SimpleGraph V} (hG : G.Connected)
    {c : V} {K : Set V} (hK : IsCompOfCut G c K)
    (huniq : ∀ x y : V, x ∈ K → y ∈ K → ¬ IsCutVertex G x → ¬ IsCutVertex G y → x = y) :
    IsPendantPath G c K := by
  classical
  have hcK : c ∉ K := compOfCut_not_mem hK
  have hsep : ∀ u ∈ K, ∀ w : V, G.Adj u w → w ∈ K ∨ w = c :=
    fun u hu w hadj => compOfCut_adj_mem hK hu hadj
  let M : Set V := K ∪ {c}
  set HM := G.induce M
  have hpath_M : ∀ {u v : V} (q : G.Walk u v), q.IsPath → u ∈ M → v ∈ M →
      ∀ w ∈ q.support, w ∈ M := by
    intro u v q hq hu hv w hw
    by_contra hwM
    have hwK : w ∉ K := fun h => hwM (Or.inl h)
    have hwc : w ≠ c := fun h => hwM (Or.inr h)
    have h1_c : c ∈ (q.takeUntil w hw).support := by
      rcases hu with huK | rfl
      · exact walk_hits_cut_of_sep hsep (q.takeUntil w hw) huK hwK
      · exact (q.takeUntil w hw).start_mem_support
    have h2_c : c ∈ (q.dropUntil w hw).support := by
      rcases hv with hvK | rfl
      · have := walk_hits_cut_of_sep hsep (q.dropUntil w hw).reverse hvK hwK
        simpa [Walk.support_reverse] using this
      · exact (q.dropUntil w hw).end_mem_support
    have hnodup : q.support.Nodup := hq.support_nodup
    have hspec := congrArg Walk.support (q.take_spec hw)
    rw [Walk.support_append] at hspec
    rw [← hspec] at hnodup
    have hdrop_cons : (q.dropUntil w hw).support = w :: (q.dropUntil w hw).support.tail := by
      cases hq' : q.dropUntil w hw <;> simp
    have hc_tail : c ∈ (q.dropUntil w hw).support.tail := by
      rw [hdrop_cons] at h2_c
      rcases List.mem_cons.mp h2_c with heq | hmem
      · exact (hwc heq.symm).elim
      · exact hmem
    exact (List.nodup_append.mp hnodup).2.2 c h1_c c hc_tail rfl
  have hHM_conn : HM.Connected := by
    have : Nonempty M := ⟨⟨c, Or.inr rfl⟩⟩
    refine SimpleGraph.Connected.mk fun u v => ?_
    obtain ⟨q⟩ := hG u.1 v.1
    let p := q.toPath
    exact ⟨walkInduce p.1 (hpath_M p.1 p.2 u.2 v.2)⟩
  have hHM_dist : ∀ u v : M, HM.dist u v = G.dist u.1 v.1 := by
    intro u v
    refine le_antisymm ?_ (dist_le_induce_dist (hHM_conn u v))
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u.1 v.1
    have hpath := p.isPath_of_length_eq_dist hp
    have hle := HM.dist_le (walkInduce p (hpath_M p hpath u.2 v.2))
    rw [walkInduce_length, hp] at hle
    exact hle
  have hnoncut_lift : ∀ x : M, x.1 ∈ K → (HM.induce ({x}ᶜ : Set M)).Connected → ¬ IsCutVertex G x.1 := by
    intro x hxK hxconn hcut
    apply hcut
    have : Nonempty ({x.1}ᶜ : Set V) := ⟨⟨c, fun h => hcK (h ▸ hxK)⟩⟩
    refine SimpleGraph.Connected.mk fun u v => ?_
    have hreach_c : ∀ z : ({x.1}ᶜ : Set V),
        (G.induce ({x.1}ᶜ : Set V)).Reachable z ⟨c, fun h => hcK (h ▸ hxK)⟩ := by
      intro z
      by_cases hzM : z.1 ∈ M
      · have hz_ne : (⟨z.1, hzM⟩ : M) ≠ x := fun h => z.2 (congrArg Subtype.val h)
        have hc_ne : (⟨c, Or.inr rfl⟩ : M) ≠ x :=
          fun h => hcK (by have hval : c = x.1 := congrArg Subtype.val h; rwa [hval])
        obtain ⟨q⟩ := hxconn ⟨⟨z.1, hzM⟩, hz_ne⟩ ⟨⟨c, Or.inr rfl⟩, hc_ne⟩
        let f : HM.induce ({x}ᶜ : Set M) →g G.induce ({x.1}ᶜ : Set V) :=
          { toFun := fun a => ⟨a.1.1, fun h => a.2 (Subtype.ext h)⟩
            map_rel' := fun h => h }
        exact ⟨q.map f⟩
      · obtain ⟨q⟩ := hG z.1 c
        let p := q.toPath
        refine ⟨walkInduce p.1 ?_⟩
        intro w hw hwx
        have hwx' : w = x.1 := Set.mem_singleton_iff.mp (by simpa using hwx)
        have hw_x : x.1 ∈ p.1.support := hwx' ▸ hw
        have hzK : z.1 ∉ K := fun h => hzM (Or.inl h)
        have hc_take : c ∈ (p.1.takeUntil x.1 hw_x).support := by
          have := walk_hits_cut_of_sep hsep (p.1.takeUntil x.1 hw_x).reverse hxK hzK
          simpa [Walk.support_reverse] using this
        have hnodup := p.2.support_nodup
        have hspec := congrArg Walk.support (p.1.take_spec hw_x)
        rw [Walk.support_append] at hspec
        rw [← hspec] at hnodup
        have hdrop_cons : (p.1.dropUntil x.1 hw_x).support =
            x.1 :: (p.1.dropUntil x.1 hw_x).support.tail :=
          (show ∀ {a b : V} (q' : G.Walk a b), q'.support = a :: q'.support.tail from
            fun q' => by cases q' <;> rfl) (p.1.dropUntil x.1 hw_x)
        have hc_end : c ∈ (p.1.dropUntil x.1 hw_x).support := (p.1.dropUntil x.1 hw_x).end_mem_support
        have hc_tail : c ∈ (p.1.dropUntil x.1 hw_x).support.tail := by
          rw [hdrop_cons] at hc_end
          rcases List.mem_cons.mp hc_end with heq | hmem
          · rw [← heq] at hxK; exact (hcK hxK).elim
          · exact hmem
        exact (List.nodup_append.mp hnodup).2.2 c hc_take c hc_tail rfl
    exact (hreach_c u).trans (hreach_c v).symm
  let Kfin : Finset V := Finset.univ.filter (fun v => v ∈ K)
  have hKfin_ne : Kfin.Nonempty := by
    obtain ⟨a, ha⟩ := compOfCut_nonempty hK
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  obtain ⟨x, hx_mem, hx_max⟩ := Finset.exists_max_image Kfin (fun u => G.dist c u) hKfin_ne
  have hxK : x ∈ K := (Finset.mem_filter.mp hx_mem).2
  have hxc : x ≠ c := fun h => hcK (h ▸ hxK)
  have hx_max_M : ∀ u : M, HM.dist ⟨c, Or.inr rfl⟩ u ≤ HM.dist ⟨c, Or.inr rfl⟩ ⟨x, Or.inl hxK⟩ := by
    intro u
    rw [hHM_dist, hHM_dist]
    rcases u.2 with huK | huc
    · exact hx_max u.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ u.1, huK⟩)
    · rw [Set.mem_singleton_iff.mp huc]; simp
  have hx_HM_conn : (HM.induce ({⟨x, Or.inl hxK⟩}ᶜ : Set M)).Connected :=
    induce_erase_connected_of_max_dist hHM_conn ⟨c, Or.inr rfl⟩ ⟨x, Or.inl hxK⟩
      (fun h => hxc (congrArg Subtype.val h)) hx_max_M
  have hx_noncut : ¬ IsCutVertex G x := hnoncut_lift ⟨x, Or.inl hxK⟩ hxK hx_HM_conn
  set k := G.dist c x
  have hk_pos : 0 < k := hG.pos_dist_of_ne hxc.symm
  obtain ⟨q, hq⟩ := hHM_conn.exists_walk_length_eq_dist ⟨c, Or.inr rfl⟩ ⟨x, Or.inl hxK⟩
  have hqlen : q.length = k := hq.trans (hHM_dist _ _)
  let p : ℕ → V := fun i => (q.getVert i).1
  have hp0 : p 0 = c := by simp [p]
  have hpk : p k = x := by simp [p, ← hqlen]
  have hp_dist : ∀ i ≤ k, G.dist c (p i) = i := by
    intro i hi
    have h1 := dist_getVert_left hHM_conn hq (by omega : i ≤ q.length)
    rw [hHM_dist] at h1
    exact h1
  have hp_in_K : ∀ i, 1 ≤ i → i ≤ k → p i ∈ K := by
    intro i hi1 hik
    rcases (q.getVert i).2 with hK' | hc'
    · exact hK'
    · have h1 := hp_dist i hik
      have hpc : p i = c := Set.mem_singleton_iff.mp hc'
      rw [hpc, SimpleGraph.dist_self] at h1
      omega
  have hK_eq : K = {v : V | ∃ i, 1 ≤ i ∧ i ≤ k ∧ v = p i} := by
    ext v
    constructor
    · intro hvK
      by_contra hvnot
      let U : Finset V := Finset.univ.filter (fun u => u ∈ K ∧ ¬ ∃ i, 1 ≤ i ∧ i ≤ k ∧ u = p i)
      have hUne : U.Nonempty := ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvK, hvnot⟩⟩
      obtain ⟨y, hy_mem, hy_max⟩ := Finset.exists_max_image U (fun u => G.dist c u) hUne
      have hyK : y ∈ K := (Finset.mem_filter.mp hy_mem).2.1
      have hynot : ¬ ∃ i, 1 ≤ i ∧ i ≤ k ∧ y = p i := (Finset.mem_filter.mp hy_mem).2.2
      have hyc : y ≠ c := fun h => hcK (h ▸ hyK)
      have hy_HM_conn : (HM.induce ({⟨y, Or.inl hyK⟩}ᶜ : Set M)).Connected := by
        have : Nonempty ({⟨y, Or.inl hyK⟩}ᶜ : Set M) :=
          ⟨⟨⟨c, Or.inr rfl⟩, fun h => hyc (congrArg Subtype.val h).symm⟩⟩
        refine SimpleGraph.Connected.mk fun u₁ u₂ => ?_
        have hreach_c : ∀ u : ({⟨y, Or.inl hyK⟩}ᶜ : Set M),
            (HM.induce ({⟨y, Or.inl hyK⟩}ᶜ : Set M)).Reachable
              ⟨⟨c, Or.inr rfl⟩, fun h => hyc (congrArg Subtype.val h).symm⟩ u := by
          intro u
          by_cases hu_on : ∃ i, i ≤ k ∧ u.1.1 = p i
          · obtain ⟨i, hik, hui⟩ := hu_on
            have hprefix : ∀ j (hjk : j ≤ k),
                (HM.induce ({⟨y, Or.inl hyK⟩}ᶜ : Set M)).Reachable
                  ⟨⟨c, Or.inr rfl⟩, fun h => hyc (congrArg Subtype.val h).symm⟩
                  ⟨q.getVert j, fun heq => by
                    have hval : p j = y := congrArg Subtype.val heq
                    rcases Nat.eq_zero_or_pos j with rfl | hj1
                    · exact hyc (hval.symm.trans hp0)
                    · exact hynot ⟨j, hj1, hjk, hval.symm⟩⟩ := by
              intro j hjk
              induction j with
              | zero =>
                convert Reachable.refl _
                ext; simp
              | succ j ih =>
                have hadj_step : HM.Adj (q.getVert j) (q.getVert (j + 1)) :=
                  q.adj_getVert_succ (by omega)
                exact (ih (by omega)).trans (Adj.reachable hadj_step)
            convert hprefix i hik
            apply Subtype.ext; exact hui
          · have huK : u.1.1 ∈ K := by
              rcases u.1.2 with h1 | h2
              · exact h1
              · exfalso; exact hu_on ⟨0, Nat.zero_le k, (Set.mem_singleton_iff.mp h2).trans hp0.symm⟩
            have huU : u.1.1 ∈ U := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, huK, ?_⟩
              rintro ⟨i, _, hik, heq⟩
              exact hu_on ⟨i, hik, heq⟩
            obtain ⟨qu, hqu⟩ := hHM_conn.exists_walk_length_eq_dist ⟨c, Or.inr rfl⟩ u.1
            refine ⟨walkInduce qu ?_⟩
            intro w hw hwy
            have hwy' : w = ⟨y, Or.inl hyK⟩ := Set.mem_singleton_iff.mp (by simpa using hwy)
            subst hwy'
            obtain ⟨idx, hidx_eq, hidx_le⟩ := Walk.mem_support_iff_exists_getVert.mp hw
            have hlt : idx < qu.length := by
              by_contra hge
              have heq : idx = qu.length := by omega
              subst heq
              rw [Walk.getVert_length] at hidx_eq
              exact u.2 hidx_eq
            have hdy : G.dist c y = idx := by
              have h1 := dist_getVert_left hHM_conn hqu hidx_le
              rw [hidx_eq, hHM_dist] at h1
              exact h1
            have hdu : G.dist c u.1.1 = qu.length := by
              rw [hqu, hHM_dist]
            have hmax_u := hy_max u.1.1 huU
            omega
        exact (hreach_c u₁).symm.trans (hreach_c u₂)
      have hy_noncut : ¬ IsCutVertex G y := hnoncut_lift ⟨y, Or.inl hyK⟩ hyK hy_HM_conn
      have hyx : y = x := huniq y x hyK hxK hy_noncut hx_noncut
      exact hynot ⟨k, hk_pos, le_rfl, hyx.trans hpk.symm⟩
    · rintro ⟨i, hi1, hik, rfl⟩
      exact hp_in_K i hi1 hik
  refine ⟨⟨K, k, p, hcK, hk_pos, hp0, hK_eq, ?_, ?_, ?_⟩, rfl⟩
  · intro i hi j hj heq
    have h1 := hp_dist i hi.2
    have h2 := hp_dist j hj.2
    rw [heq] at h1
    omega
  · intro i hi
    exact q.adj_getVert_succ (by omega)
  · intro i hi1 hik w hadj
    have hpiK : p i ∈ K := hp_in_K i hi1 hik
    rcases hsep (p i) hpiK w hadj with hwK | hwc
    · rw [hK_eq] at hwK
      obtain ⟨j, hj1, hjk, rfl⟩ := hwK
      have hdi := hp_dist i hik
      have hdj := hp_dist j hjk
      have h1 : G.dist (p i) (p j) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
      have h2 : G.dist (p j) (p i) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
      have ht1 : G.dist c (p j) ≤ G.dist c (p i) + G.dist (p i) (p j) := hG.dist_triangle
      have ht2 : G.dist c (p i) ≤ G.dist c (p j) + G.dist (p j) (p i) := hG.dist_triangle
      have hne : i ≠ j := fun h => hadj.ne (congrArg p h)
      rcases (by omega : j = i - 1 ∨ (i < k ∧ j = i + 1)) with rfl | ⟨hlt, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hlt, rfl⟩
    · rw [hwc] at hadj ⊢
      have hdi := hp_dist i hik
      have h1 : G.dist c (p i) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
      have hi_eq : i = 1 := by omega
      subst hi_eq
      exact Or.inl hp0.symm

/-- Lemma 1 (Universal Witness Lemma): in a minimal counterexample `H`, every non-cut vertex `x`
has a witness `w ≠ x` at distance `r` from `x` and `≤ r - 1` from every other vertex. -/
private lemma minimal_universal_witness {H : SimpleGraph V}
    (hH : H.Connected) (hcut : HasCutVertex H) (hr2 : 2 ≤ H.radius.toNat)
    (hmin : ∀ x : V, ¬ IsCutVertex H x →
      HasCutVertex (H.induce ({x}ᶜ : Set V)) →
      (H.induce ({x}ᶜ : Set V)).radius.toNat ≤ H.radius.toNat - 1) :
    ∀ x : V, ¬ IsCutVertex H x →
      ∃ w : V, w ≠ x ∧ H.dist w x = H.radius.toNat ∧
        ∀ u : V, u ≠ x → H.dist w u ≤ H.radius.toNat - 1 := by
  classical
  set r := H.radius.toNat
  have hcard4 : 4 ≤ Fintype.card V := by
    have := two_mul_radius_le_card hH
    omega
  have hwitness_of_rad : ∀ x : V, ¬ IsCutVertex H x →
      (H.induce ({x}ᶜ : Set V)).radius.toNat ≤ r - 1 →
      ∃ w : V, w ≠ x ∧ H.dist w x = r ∧ ∀ u : V, u ≠ x → H.dist w u ≤ r - 1 := by
    intro x hnc hrad
    have hconn' : (H.induce ({x}ᶜ : Set V)).Connected := not_not.mp hnc
    obtain ⟨w', hw'⟩ := exists_center_dist_le hconn'
    refine ⟨w'.1, w'.2, ?_, ?_⟩
    · have hle_other : ∀ u : V, u ≠ x → H.dist w'.1 u ≤ r - 1 := by
        intro u hu
        have h1 := dist_le_induce_dist (G := H) (s := ({x}ᶜ : Set V)) (hconn' w' ⟨u, hu⟩)
        have h2 := hw' ⟨u, hu⟩
        change H.dist w'.1 u ≤ (H.induce ({x}ᶜ : Set V)).dist w' ⟨u, hu⟩ at h1
        omega
      have hge : r ≤ H.dist w'.1 x := by
        obtain ⟨y, hy⟩ := exists_dist_ge_radius hH w'.1
        by_cases hyx : y = x
        · subst hyx; exact hy
        · have := hle_other y hyx; omega
      have hle : H.dist w'.1 x ≤ r := by
        obtain ⟨q, hq⟩ := hH.exists_walk_length_eq_dist w'.1 x
        have hqpos : 0 < q.length := by
          have := hH.pos_dist_of_ne w'.2
          omega
        set u := q.getVert (q.length - 1)
        have hu_adj : H.Adj u x := by
          have := q.adj_getVert_succ (by omega : q.length - 1 < q.length)
          simpa [show q.length - 1 + 1 = q.length by omega, Walk.getVert_length] using this
        have htri : H.dist w'.1 x ≤ H.dist w'.1 u + H.dist u x := hH.dist_triangle
        have h1 : H.dist u x = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hu_adj
        have h2 := hle_other u hu_adj.ne
        omega
      exact le_antisymm hle hge
    · intro u hu
      have h1 := dist_le_induce_dist (G := H) (s := ({x}ᶜ : Set V)) (hconn' w' ⟨u, hu⟩)
      have h2 := hw' ⟨u, hu⟩
      change H.dist w'.1 u ≤ (H.induce ({x}ᶜ : Set V)).dist w' ⟨u, hu⟩ at h1
      omega
  intro x hnc
  by_cases hcutx : HasCutVertex (H.induce ({x}ᶜ : Set V))
  · exact hwitness_of_rad x hnc (hmin x hnc hcutx)
  · exfalso
    obtain ⟨c, hc⟩ := hcut
    have hcx : c ≠ x := fun h => hnc (h ▸ hc)
    have hconnx : (H.induce ({x}ᶜ : Set V)).Connected := not_not.mp hnc
    have hno_cut : ∀ v : ({x}ᶜ : Set V),
        ((H.induce ({x}ᶜ : Set V)).induce ({v}ᶜ : Set ({x}ᶜ : Set V))).Connected := by
      intro v
      by_contra hdisc
      exact hcutx ⟨v, hdisc⟩
    have hconn_xc := hno_cut ⟨c, hcx⟩
    have hx_only_c : ∀ u : V, H.Adj x u → u = c := by
      intro u hxu
      by_contra huc
      have hux : u ≠ x := hxu.ne.symm
      apply hc
      have : Nonempty ({c}ᶜ : Set V) := ⟨⟨x, hcx.symm⟩⟩
      refine SimpleGraph.Connected.mk fun a b => ?_
      have hreach_x : ∀ z : ({c}ᶜ : Set V), (H.induce ({c}ᶜ : Set V)).Reachable ⟨x, hcx.symm⟩ z := by
        intro z
        by_cases hzx : z.1 = x
        · convert Reachable.refl _; exact Subtype.ext hzx
        · have h1 : (H.induce ({c}ᶜ : Set V)).Reachable ⟨x, hcx.symm⟩ ⟨u, huc⟩ := Adj.reachable hxu
          have hu' : (⟨u, hux⟩ : ({x}ᶜ : Set V)) ≠ ⟨c, hcx⟩ := fun h => huc (congrArg Subtype.val h)
          have hz' : (⟨z.1, hzx⟩ : ({x}ᶜ : Set V)) ≠ ⟨c, hcx⟩ := fun h => z.2 (congrArg Subtype.val h)
          obtain ⟨q⟩ := hconn_xc ⟨⟨u, hux⟩, hu'⟩ ⟨⟨z.1, hzx⟩, hz'⟩
          let f : ((H.induce ({x}ᶜ : Set V)).induce ({⟨c, hcx⟩}ᶜ : Set ({x}ᶜ : Set V))) →g
              H.induce ({c}ᶜ : Set V) :=
            { toFun := fun t => ⟨t.1.1, fun h => t.2 (Subtype.ext h)⟩
              map_rel' := fun h => h }
          exact h1.trans ⟨q.map f⟩
      exact (hreach_x a).symm.trans (hreach_x b)
    have hxc_adj : H.Adj x c := by
      obtain ⟨q, hq⟩ := hH.exists_walk_length_eq_dist x c
      have hqpos : 0 < q.length := by
        have := hH.pos_dist_of_ne hcx.symm
        omega
      have hadj1 : H.Adj x (q.getVert 1) := by
        simpa using q.adj_getVert_succ hqpos
      have := hx_only_c _ hadj1
      rwa [this] at hadj1
    have hex_other : ∃ y : V, y ≠ c ∧ y ≠ x := by
      have hlt : ({c, x} : Finset V).card < (Finset.univ : Finset V).card := by
        have h1 : ({c, x} : Finset V).card ≤ 2 := Finset.card_le_two
        rw [Finset.card_univ]
        omega
      obtain ⟨y, _, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
      exact ⟨y, hy.1, hy.2⟩
    obtain ⟨y0, hy0c, hy0x⟩ := hex_other
    obtain ⟨qy, hqy⟩ := hconnx.exists_walk_length_eq_dist ⟨c, hcx⟩ ⟨y0, hy0x⟩
    have hqy_pos : 0 < qy.length := by
      have := hconnx.pos_dist_of_ne (u := ⟨c, hcx⟩) (v := ⟨y0, hy0x⟩)
        (fun h => hy0c (congrArg Subtype.val h).symm)
      omega
    set z' := qy.getVert 1
    set z := z'.1
    have hzx : z ≠ x := z'.2
    have hcz_adj : H.Adj c z := by
      have := qy.adj_getVert_succ hqy_pos
      simpa [z', z] using this
    have hzc : z ≠ c := hcz_adj.ne.symm
    have hz_noncut : ¬ IsCutVertex H z := by
      intro hcutz
      apply hcutz
      have : Nonempty ({z}ᶜ : Set V) := ⟨⟨c, hzc.symm⟩⟩
      refine SimpleGraph.Connected.mk fun a b => ?_
      have hreach_c : ∀ u : ({z}ᶜ : Set V), (H.induce ({z}ᶜ : Set V)).Reachable ⟨c, hzc.symm⟩ u := by
        intro u
        by_cases hux : u.1 = x
        · convert Adj.reachable (G := H.induce ({z}ᶜ : Set V)) (u := ⟨c, hzc.symm⟩)
            (v := ⟨x, hzx.symm⟩) hxc_adj.symm
          exact Subtype.ext hux
        · have hconn_xz := hno_cut ⟨z, hzx⟩
          have hc' : (⟨c, hcx⟩ : ({x}ᶜ : Set V)) ≠ ⟨z, hzx⟩ :=
            fun h => hzc (congrArg Subtype.val h).symm
          have hu' : (⟨u.1, hux⟩ : ({x}ᶜ : Set V)) ≠ ⟨z, hzx⟩ :=
            fun h => u.2 (congrArg Subtype.val h)
          obtain ⟨q⟩ := hconn_xz ⟨⟨c, hcx⟩, hc'⟩ ⟨⟨u.1, hux⟩, hu'⟩
          let f : ((H.induce ({x}ᶜ : Set V)).induce ({⟨z, hzx⟩}ᶜ : Set ({x}ᶜ : Set V))) →g
              H.induce ({z}ᶜ : Set V) :=
            { toFun := fun t => ⟨t.1.1, fun h => t.2 (Subtype.ext h)⟩
              map_rel' := fun h => h }
          exact ⟨q.map f⟩
      exact (hreach_c a).symm.trans (hreach_c b)
    have hex_fourth : ∃ y : V, y ≠ c ∧ y ≠ x ∧ y ≠ z := by
      have hlt : ({c, x, z} : Finset V).card < (Finset.univ : Finset V).card := by
        have h1 : ({c, x, z} : Finset V).card ≤ 3 := by
          calc ({c, x, z} : Finset V).card
              ≤ ({x, z} : Finset V).card + 1 := Finset.card_insert_le _ _
            _ ≤ 2 + 1 := Nat.add_le_add_right Finset.card_le_two 1
        rw [Finset.card_univ]
        omega
      obtain ⟨y, _, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
      exact ⟨y, hy.1, hy.2.1, hy.2.2⟩
    obtain ⟨y, hyc, hyx, hyz⟩ := hex_fourth
    have hcut_Hz : HasCutVertex (H.induce ({z}ᶜ : Set V)) := by
      refine ⟨⟨c, hzc.symm⟩, fun hconn => ?_⟩
      have hx_ne : (⟨x, hzx.symm⟩ : ({z}ᶜ : Set V)) ≠ ⟨c, hzc.symm⟩ :=
        fun h => hcx (congrArg Subtype.val h).symm
      have hy_ne : (⟨y, hyz⟩ : ({z}ᶜ : Set V)) ≠ ⟨c, hzc.symm⟩ :=
        fun h => hyc (congrArg Subtype.val h)
      obtain ⟨q⟩ := hconn ⟨⟨x, hzx.symm⟩, hx_ne⟩ ⟨⟨y, hyz⟩, hy_ne⟩
      cases q with
      | nil => exact hyx rfl
      | @cons _ next _ hadj _ =>
        have hnext : next.1.1 = c := hx_only_c next.1.1 hadj
        exact next.2 (Subtype.ext hnext)
    obtain ⟨wz, hwz_ne, hwz_z, hwz_other⟩ := hwitness_of_rad z hz_noncut (hmin z hz_noncut hcut_Hz)
    have hwz_ne_x : wz ≠ x := by
      intro heq
      have hxz : H.dist x z ≤ 2 := by
        have htri : H.dist x z ≤ H.dist x c + H.dist c z := hH.dist_triangle
        have h1 : H.dist x c = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxc_adj
        have h2 : H.dist c z = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hcz_adj
        omega
      rw [heq] at hwz_z hwz_other
      have hr_eq2 : r = 2 := by omega
      have hxy : H.dist x y ≤ 1 := by
        have := hwz_other y hyz
        omega
      have hxy_pos : 0 < H.dist x y := hH.pos_dist_of_ne hyx.symm
      have hxy1 : H.dist x y = 1 := by omega
      have hadj_xy : H.Adj x y := SimpleGraph.dist_eq_one_iff_adj.mp hxy1
      exact hyc (hx_only_c y hadj_xy)
    have hwx_eq : H.dist wz x = H.dist wz c + 1 := by
      have hsep_x : ∀ u ∈ ({x} : Set V), ∀ w : V, H.Adj u w → w ∈ ({x} : Set V) ∨ w = c := by
        intro u hu w hadj
        rw [Set.mem_singleton_iff.mp hu] at hadj
        exact Or.inr (hx_only_c w hadj)
      have := dist_through_cut_symm hH hsep_x (by simp [hwz_ne_x] : wz ∉ ({x} : Set V))
        (Set.mem_singleton x)
      have hcx1 : H.dist c x = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxc_adj.symm
      omega
    have hwx_le : H.dist wz x ≤ r - 1 := hwz_other x hzx.symm
    have htri : H.dist wz z ≤ H.dist wz c + H.dist c z := hH.dist_triangle
    have hcz1 : H.dist c z = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hcz_adj
    omega

/-- Lemma 3: For any cut vertex `c` and two disjoint components of `H - c`, at least one
is a pendant path. -/
private lemma minimal_at_most_one_non_pendant {H : SimpleGraph V} (hH : H.Connected)
    (hr1 : 1 ≤ H.radius.toNat)
    (hUnivWitness : ∀ x : V, ¬ IsCutVertex H x →
      ∃ w : V, w ≠ x ∧ H.dist w x = H.radius.toNat ∧
        ∀ u : V, u ≠ x → H.dist w u ≤ H.radius.toNat - 1)
    {c : V} {K₁ K₂ : Set V}
    (hK₁ : IsCompOfCut H c K₁) (hK₂ : IsCompOfCut H c K₂) (hdisj : Disjoint K₁ K₂) :
    IsPendantPath H c K₁ ∨ IsPendantPath H c K₂ := by
  set r := H.radius.toNat
  have hr1' : 1 ≤ r := hr1
  by_contra hboth
  push Not at hboth
  have hex_in : ∀ K : Set V, IsCompOfCut H c K → ¬ IsPendantPath H c K →
      ∃ x w : V, x ∈ K ∧ w ∈ K ∧ H.dist w x = r ∧ ∀ u : V, u ≠ x → H.dist w u ≤ r - 1 := by
    intro K hK hnotP
    have htwo : ∃ x₁ x₂ : V, x₁ ∈ K ∧ x₂ ∈ K ∧ ¬ IsCutVertex H x₁ ∧ ¬ IsCutVertex H x₂ ∧ x₁ ≠ x₂ := by
      by_contra hall
      push Not at hall
      exact hnotP (pendant_of_at_most_one_noncut hH hK hall)
    obtain ⟨x₁, x₂, hx₁K, hx₂K, hnc₁, hnc₂, hne⟩ := htwo
    obtain ⟨w₁, _, hw₁x, hw₁u⟩ := hUnivWitness x₁ hnc₁
    by_cases hw₁K : w₁ ∈ K
    · exact ⟨x₁, w₁, hx₁K, hw₁K, hw₁x, hw₁u⟩
    · obtain ⟨w₂, _, hw₂x, hw₂u⟩ := hUnivWitness x₂ hnc₂
      by_cases hw₂K : w₂ ∈ K
      · exact ⟨x₂, w₂, hx₂K, hw₂K, hw₂x, hw₂u⟩
      · exfalso
        have hsep : ∀ u ∈ K, ∀ w : V, H.Adj u w → w ∈ K ∨ w = c :=
          fun u hu w hadj => compOfCut_adj_mem hK hu hadj
        have h11 := dist_through_cut_symm hH hsep hw₁K hx₁K
        have h12 := dist_through_cut_symm hH hsep hw₁K hx₂K
        have h21 := dist_through_cut_symm hH hsep hw₂K hx₁K
        have h22 := dist_through_cut_symm hH hsep hw₂K hx₂K
        have hb1 : H.dist w₁ x₂ ≤ r - 1 := hw₁u x₂ hne.symm
        have hb2 : H.dist w₂ x₁ ≤ r - 1 := hw₂u x₁ hne
        have hr1_eq : H.dist w₁ x₁ = r := hw₁x
        have hr2_eq : H.dist w₂ x₂ = r := hw₂x
        omega
  obtain ⟨x₁, w₁, hx₁, hw₁, hr₁, hu₁⟩ := hex_in K₁ hK₁ hboth.1
  obtain ⟨x₂, w₂, hx₂, hw₂, hr₂, hu₂⟩ := hex_in K₂ hK₂ hboth.2
  have hsep₁ : ∀ u ∈ K₁, ∀ w : V, H.Adj u w → w ∈ K₁ ∨ w = c :=
    fun u hu w hadj => compOfCut_adj_mem hK₁ hu hadj
  have hsep₂ : ∀ u ∈ K₂, ∀ w : V, H.Adj u w → w ∈ K₂ ∨ w = c :=
    fun u hu w hadj => compOfCut_adj_mem hK₂ hu hadj
  have hx₂_not1 : x₂ ∉ K₁ := Set.disjoint_right.mp hdisj hx₂
  have hx₁_not2 : x₁ ∉ K₂ := Set.disjoint_left.mp hdisj hx₁
  have hne12 : x₁ ≠ x₂ := fun h => hx₂_not1 (h ▸ hx₁)
  have hd1 : H.dist w₁ x₂ = H.dist w₁ c + H.dist c x₂ := dist_through_cut hH hsep₁ hw₁ hx₂_not1
  have hd2 : H.dist w₂ x₁ = H.dist w₂ c + H.dist c x₁ := dist_through_cut hH hsep₂ hw₂ hx₁_not2
  have ht1 : H.dist w₁ x₁ ≤ H.dist w₁ c + H.dist c x₁ := hH.dist_triangle
  have ht2 : H.dist w₂ x₂ ≤ H.dist w₂ c + H.dist c x₂ := hH.dist_triangle
  have hb1 : H.dist w₁ x₂ ≤ r - 1 := hu₁ x₂ hne12.symm
  have hb2 : H.dist w₂ x₁ ≤ r - 1 := hu₂ x₁ hne12
  omega

/-- Lemma 4: No cut vertex `c` has two disjoint pendant-path components. -/
private lemma minimal_at_most_one_pendant {H : SimpleGraph V} (hH : H.Connected)
    (hr2 : 2 ≤ H.radius.toNat)
    (htree : largestInducedTreeSize H ≤ 2 * H.radius.toNat - 1)
    (hUnivWitness : ∀ x : V, ¬ IsCutVertex H x →
      ∃ w : V, w ≠ x ∧ H.dist w x = H.radius.toNat ∧
        ∀ u : V, u ≠ x → H.dist w u ≤ H.radius.toNat - 1)
    {c : V} {P Q : Set V}
    (hPP : IsPendantPath H c P) (hPQ : IsPendantPath H c Q) (hdisj : Disjoint P Q) :
    False := by
  set r := H.radius.toNat
  have hcard4 : 4 ≤ Fintype.card V := by
    have := two_mul_radius_le_card hH
    omega
  have haux : ∀ (dP dQ : PendantData H c), dQ.k ≤ dP.k → Disjoint dP.K dQ.K → False := by
    intro dP dQ hba hdisj'
    have hsepP := pendant_sep ⟨dP, rfl⟩
    have hsepQ := pendant_sep ⟨dQ, rfl⟩
    have hab_bound : dP.k + dQ.k + 1 ≤ 2 * r - 1 := by
      let f : ℕ → V := fun t => if t ≤ dP.k then dP.p (dP.k - t) else dQ.p (t - dP.k)
      have hle := induced_path_card_le_tree (G := H) (dP.k + dQ.k) f ?_ ?_ ?_
      · omega
      · intro i hi j hj heq
        simp only [Set.mem_Icc] at hi hj
        dsimp only [f] at heq
        split_ifs at heq with hi' hj' hj'
        · have := dP.hinj ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ heq
          omega
        · by_cases hia : i = dP.k
          · subst hia
            have hq_mem : dQ.p (j - dP.k) ∈ dQ.K := by
              rw [dQ.hK]; exact ⟨j - dP.k, by omega, by omega, rfl⟩
            rw [Nat.sub_self, dP.hp0] at heq
            rw [← heq] at hq_mem
            exact (dQ.hcK hq_mem).elim
          · have hp_mem : dP.p (dP.k - i) ∈ dP.K := by
              rw [dP.hK]; exact ⟨dP.k - i, by omega, by omega, rfl⟩
            have hq_mem : dQ.p (j - dP.k) ∈ dQ.K := by
              rw [dQ.hK]; exact ⟨j - dP.k, by omega, by omega, rfl⟩
            exact (Set.disjoint_left.mp hdisj' hp_mem (heq ▸ hq_mem)).elim
        · by_cases hja : j = dP.k
          · subst hja
            have hq_mem : dQ.p (i - dP.k) ∈ dQ.K := by
              rw [dQ.hK]; exact ⟨i - dP.k, by omega, by omega, rfl⟩
            rw [Nat.sub_self, dP.hp0] at heq
            rw [heq] at hq_mem
            exact (dQ.hcK hq_mem).elim
          · have hp_mem : dP.p (dP.k - j) ∈ dP.K := by
              rw [dP.hK]; exact ⟨dP.k - j, by omega, by omega, rfl⟩
            have hq_mem : dQ.p (i - dP.k) ∈ dQ.K := by
              rw [dQ.hK]; exact ⟨i - dP.k, by omega, by omega, rfl⟩
            exact (Set.disjoint_left.mp hdisj' hp_mem (heq.symm ▸ hq_mem)).elim
        · have := dQ.hinj ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ heq
          omega
      · intro i hi
        dsimp only [f]
        by_cases hlt : i + 1 ≤ dP.k
        · rw [if_pos (by omega), if_pos hlt]
          have h1 : dP.k - i = (dP.k - (i + 1)) + 1 := by omega
          rw [h1]
          exact (dP.hadj (dP.k - (i + 1)) (by omega)).symm
        · by_cases heq : i = dP.k
          · subst heq
            rw [if_pos le_rfl, if_neg (by omega)]
            rw [Nat.sub_self, show dP.k + 1 - dP.k = 1 by omega, dP.hp0]
            have h0 := dQ.hadj 0 dQ.hk
            rwa [dQ.hp0] at h0
          · rw [if_neg (by omega), if_neg (by omega)]
            have h1 : i + 1 - dP.k = (i - dP.k) + 1 := by omega
            rw [h1]
            exact dQ.hadj (i - dP.k) (by omega)
      · intro i j hji hi hadj
        dsimp only [f] at hadj
        split_ifs at hadj with hi' hj' hj'
        · by_cases hia : i = dP.k
          · subst hia
            rw [Nat.sub_self] at hadj
            rcases dP.hnbr (dP.k - j) (by omega) (by omega) (dP.p 0) hadj.symm with heq | ⟨hlt, heq⟩
            · have := dP.hinj ⟨Nat.zero_le _, by omega⟩ ⟨le_rfl, by omega⟩ heq.symm
              omega
            · have := dP.hinj ⟨le_rfl, by omega⟩ ⟨Nat.zero_le _, by omega⟩ heq
              omega
          · rcases dP.hnbr (dP.k - i) (by omega) (by omega) (dP.p (dP.k - j)) hadj with heq | ⟨hlt, heq⟩
            · have := dP.hinj ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ heq
              omega
            · have := dP.hinj ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ heq
              omega
        · omega
        · rcases dQ.hnbr (i - dP.k) (by omega) (by omega) (dP.p (dP.k - j)) hadj with heq | ⟨hlt, heq⟩
          · by_cases hia1 : i - dP.k = 1
            · rw [hia1] at heq
              simp only [Nat.sub_self, dQ.hp0, ← dP.hp0] at heq
              have := dP.hinj ⟨Nat.zero_le _, by omega⟩ ⟨le_rfl, by omega⟩ heq
              omega
            · have hq_mem : dQ.p (i - dP.k - 1) ∈ dQ.K := by
                rw [dQ.hK]; exact ⟨i - dP.k - 1, by omega, by omega, rfl⟩
              by_cases hja : j = dP.k
              · subst hja
                rw [Nat.sub_self, dP.hp0] at heq
                rw [← heq] at hq_mem
                exact (dQ.hcK hq_mem).elim
              · have hp_mem : dP.p (dP.k - j) ∈ dP.K := by
                  rw [dP.hK]; exact ⟨dP.k - j, by omega, by omega, rfl⟩
                exact (Set.disjoint_left.mp hdisj' hp_mem (heq ▸ hq_mem)).elim
          · have hq_mem : dQ.p (i - dP.k + 1) ∈ dQ.K := by
              rw [dQ.hK]; exact ⟨i - dP.k + 1, by omega, by omega, rfl⟩
            by_cases hja : j = dP.k
            · subst hja
              rw [Nat.sub_self, dP.hp0] at heq
              rw [← heq] at hq_mem
              exact (dQ.hcK hq_mem).elim
            · have hp_mem : dP.p (dP.k - j) ∈ dP.K := by
                rw [dP.hK]; exact ⟨dP.k - j, by omega, by omega, rfl⟩
              exact (Set.disjoint_left.mp hdisj' hp_mem (heq ▸ hq_mem)).elim
        · rcases dQ.hnbr (i - dP.k) (by omega) (by omega) (dQ.p (j - dP.k)) hadj with heq | ⟨hlt, heq⟩
          · have := dQ.hinj ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ heq
            omega
          · have := dQ.hinj ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ heq
            omega
    have hqb_nc : ¬ IsCutVertex H (dQ.p dQ.k) :=
      not_isCutVertex_of_unique_adj hH (dQ.p dQ.k) (dQ.p (dQ.k - 1))
        (fun w hw => by
          rcases dQ.hnbr dQ.k dQ.hk le_rfl w hw with h1 | ⟨hlt, _⟩
          · exact h1
          · omega) (by omega)
    obtain ⟨w, hwne, hwr, hwu⟩ := hUnivWitness (dQ.p dQ.k) hqb_nc
    have hpa_ne_qb : dP.p dP.k ≠ dQ.p dQ.k := by
      intro heq
      have hp_mem : dP.p dP.k ∈ dP.K := by rw [dP.hK]; exact ⟨dP.k, dP.hk, le_rfl, rfl⟩
      have hq_mem : dQ.p dQ.k ∈ dQ.K := by rw [dQ.hK]; exact ⟨dQ.k, dQ.hk, le_rfl, rfl⟩
      exact Set.disjoint_left.mp hdisj' hp_mem (heq ▸ hq_mem)
    by_cases hwQ : w ∈ dQ.K
    · rw [dQ.hK] at hwQ
      obtain ⟨j, hj1, hjb, rfl⟩ := hwQ
      have hd := pendant_dist_eq hH dQ hjb le_rfl
      omega
    · by_cases hwP : w ∈ dP.K
      · rw [dP.hK] at hwP
        obtain ⟨j, hj1, hja, rfl⟩ := hwP
        have hdj_c : H.dist (dP.p j) c = j := by
          have h0 := pendant_dist_eq hH dP hja (Nat.zero_le _)
          rw [dP.hp0] at h0; omega
        have hc_qb : H.dist c (dQ.p dQ.k) = dQ.k := by
          have h0 := pendant_dist_eq hH dQ (Nat.zero_le _) le_rfl
          rw [dQ.hp0] at h0; omega
        have hqb_notP : dQ.p dQ.k ∉ dP.K :=
          Set.disjoint_right.mp hdisj' (by rw [dQ.hK]; exact ⟨dQ.k, dQ.hk, le_rfl, rfl⟩)
        have hr_eq : r = j + dQ.k := by
          have := dist_through_cut hH hsepP (by rw [dP.hK]; exact ⟨j, hj1, hja, rfl⟩) hqb_notP
          omega
        obtain ⟨u, hu_ge⟩ := exists_dist_ge_radius hH (dP.p (j - 1))
        let tail : Set V := {v : V | ∃ t, j ≤ t ∧ t ≤ dP.k ∧ v = dP.p t}
        have hsep_tail : ∀ v ∈ tail, ∀ z : V, H.Adj v z → z ∈ tail ∨ z = dP.p (j - 1) := by
          rintro v ⟨t, htj, hta, rfl⟩ z hadj
          rcases dP.hnbr t (by omega) hta z hadj with rfl | ⟨hlt, rfl⟩
          · rcases eq_or_lt_of_le htj with rfl | hgt
            · exact Or.inr rfl
            · exact Or.inl ⟨t - 1, by omega, by omega, rfl⟩
          · exact Or.inl ⟨t + 1, by omega, by omega, rfl⟩
        by_cases hu_tail : u ∈ tail
        · obtain ⟨t, htj, hta, rfl⟩ := hu_tail
          have hd := pendant_dist_eq hH dP (by omega : j - 1 ≤ dP.k) hta
          omega
        · have hdt := dist_through_cut hH hsep_tail ⟨j, le_rfl, hja, rfl⟩ hu_tail
          have hadj_j : H.Adj (dP.p j) (dP.p (j - 1)) := by
            have := dP.hadj (j - 1) (by omega)
            rw [show j - 1 + 1 = j by omega] at this
            exact this.symm
          have h1 : H.dist (dP.p j) (dP.p (j - 1)) = 1 :=
            SimpleGraph.dist_eq_one_iff_adj.mpr hadj_j
          by_cases huqb : u = dQ.p dQ.k
          · subst huqb; omega
          · have := hwu u huqb; omega
      · have h1 := dist_through_cut_symm hH hsepQ hwQ (by rw [dQ.hK]; exact ⟨dQ.k, dQ.hk, le_rfl, rfl⟩)
        have h2 := dist_through_cut_symm hH hsepP hwP (by rw [dP.hK]; exact ⟨dP.k, dP.hk, le_rfl, rfl⟩)
        have hc_qb : H.dist c (dQ.p dQ.k) = dQ.k := by
          have h0 := pendant_dist_eq hH dQ (Nat.zero_le _) le_rfl
          rw [dQ.hp0] at h0; omega
        have hc_pa : H.dist c (dP.p dP.k) = dP.k := by
          have h0 := pendant_dist_eq hH dP (Nat.zero_le _) le_rfl
          rw [dP.hp0] at h0; omega
        have := hwu (dP.p dP.k) hpa_ne_qb
        omega
  obtain ⟨dP, rfl⟩ := hPP
  obtain ⟨dQ, rfl⟩ := hPQ
  rcases le_total dQ.k dP.k with hba | hab
  · exact haux dP dQ hba hdisj
  · exact haux dQ dP hab hdisj.symm

/-- Core contradiction for a minimal counterexample to Gebendorfer's theorem:
every connected graph with a cut vertex satisfies `2 * rad(H) ≤ tree(H)`. -/
private lemma cut_vertex_minimal_contradiction {H : SimpleGraph V}
    (hH : H.Connected) (hcut : HasCutVertex H)
    (hr2 : 2 ≤ H.radius.toNat)
    (htree : largestInducedTreeSize H ≤ 2 * H.radius.toNat - 1)
    (hmin : ∀ x : V, ¬ IsCutVertex H x →
      HasCutVertex (H.induce ({x}ᶜ : Set V)) →
      (H.induce ({x}ᶜ : Set V)).radius.toNat ≤ H.radius.toNat - 1) :
    False := by
  classical
  set r := H.radius.toNat
  have hcard4 : 4 ≤ Fintype.card V := by
    have := two_mul_radius_le_card hH
    omega
  have hUnivWitness := minimal_universal_witness hH hcut hr2 hmin
  have hAtMostOneNonPendant : ∀ {c : V} {K₁ K₂ : Set V},
      IsCompOfCut H c K₁ → IsCompOfCut H c K₂ → Disjoint K₁ K₂ →
      IsPendantPath H c K₁ ∨ IsPendantPath H c K₂ :=
    fun hK₁ hK₂ hdisj => minimal_at_most_one_non_pendant hH (by omega) hUnivWitness hK₁ hK₂ hdisj
  have hAtMostOnePendant : ∀ {c : V} {P Q : Set V},
      IsPendantPath H c P → IsPendantPath H c Q → Disjoint P Q → False :=
    fun hPP hPQ hdisj => minimal_at_most_one_pendant hH hr2 htree hUnivWitness hPP hPQ hdisj
  have hex_pendant_of_cut : ∀ c : V, IsCutVertex H c → ∃ P : Set V, IsPendantPath H c P := by
    intro c hc
    have hex_ne : ∃ a b : ({c}ᶜ : Set V), ¬ (H.induce ({c}ᶜ : Set V)).Reachable a b := by
      by_contra hall
      push Not at hall
      have hne_c : ∃ x : V, x ≠ c := by
        have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
        exact exists_ne c
      obtain ⟨x0, hx0⟩ := hne_c
      have : Nonempty ({c}ᶜ : Set V) := ⟨⟨x0, hx0⟩⟩
      exact hc (SimpleGraph.Connected.mk hall)
    obtain ⟨a, b, hab⟩ := hex_ne
    let K₁ : Set V := {v : V | ∃ hv : v ≠ c, (H.induce ({c}ᶜ : Set V)).Reachable a ⟨v, hv⟩}
    let K₂ : Set V := {v : V | ∃ hv : v ≠ c, (H.induce ({c}ᶜ : Set V)).Reachable b ⟨v, hv⟩}
    have hdisj : Disjoint K₁ K₂ := by
      rw [Set.disjoint_left]
      rintro v ⟨_, h1⟩ ⟨_, h2⟩
      exact hab (h1.trans h2.symm)
    rcases hAtMostOneNonPendant ⟨a, rfl⟩ ⟨b, rfl⟩ hdisj with h1 | h2
    · exact ⟨K₁, h1⟩
    · exact ⟨K₂, h2⟩
  -- Define the 2-connected core `C`
  let C : Set V := {v : V | ∀ c : V, ∀ K : Set V, IsPendantPath H c K → v ∉ K}
  have hnot_tree : ¬ H.IsTree := by
    intro hT
    have h1 : (Finset.univ : Finset V).card ≤ largestInducedTreeSize H := by
      apply card_le_largestInducedTreeSize
      let e : H.induce ((Finset.univ : Finset V) : Set V) ≃g H :=
        { toFun := Subtype.val
          invFun := fun x => ⟨x, Finset.mem_univ x⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_rel_iff' := by intro a b; rfl }
      exact (e.isTree_iff).mpr hT
    rw [Finset.card_univ] at h1
    have h2 := two_mul_radius_le_card hH
    omega
  have hnot_acyclic : ¬ H.IsAcyclic := fun hA => hnot_tree ⟨hH, hA⟩
  have hex_cycle : ∃ v : V, ∃ Z : H.Walk v v, Z.IsCycle := by
    unfold SimpleGraph.IsAcyclic at hnot_acyclic
    push Not at hnot_acyclic
    exact hnot_acyclic
  obtain ⟨vZ, Z, hZ⟩ := hex_cycle
  have hZ_in_C : ∀ w ∈ Z.support, w ∈ C := fun w hw c K hP => pendant_cycle_disjoint hP hZ w hw
  have hC_card3 : 3 ≤ Fintype.card C := by
    have h3 : 3 ≤ Z.length := hZ.three_le_length
    let f : Fin 3 → C := fun i =>
      ⟨Z.getVert i.1, hZ_in_C _ (Z.getVert_mem_support i.1)⟩
    have hfinj : Function.Injective f := by
      intro i j heq
      have hval : Z.getVert i.1 = Z.getVert j.1 := congrArg Subtype.val heq
      have h1 := hZ.getVert_injOn' (by omega : i.1 ≤ Z.length - 1) (by omega : j.1 ≤ Z.length - 1) hval
      exact Fin.ext h1
    simpa using Fintype.card_le_of_injective f hfinj
  have hC_nonempty : C.Nonempty := ⟨vZ, hZ_in_C vZ Z.start_mem_support⟩
  have hpath_C : ∀ {u v : V} (q : H.Walk u v), q.IsPath → u ∈ C → v ∈ C → ∀ w ∈ q.support, w ∈ C :=
    fun q hq hu hv w hw c K hP => pendant_path_disjoint hP hq (hu c K hP) (hv c K hP) w hw
  have hHC_conn : (H.induce C).Connected := by
    have : Nonempty C := hC_nonempty.to_subtype
    refine SimpleGraph.Connected.mk fun u v => ?_
    obtain ⟨q⟩ := hH u.1 v.1
    let p := q.toPath
    exact ⟨walkInduce p.1 (hpath_C p.1 p.2 u.2 v.2)⟩
  have hHC_dist : ∀ u v : C, (H.induce C).dist u v = H.dist u.1 v.1 := by
    intro u v
    refine le_antisymm ?_ (dist_le_induce_dist (hHC_conn u v))
    obtain ⟨p, hp⟩ := hH.exists_walk_length_eq_dist u.1 v.1
    have hle := (H.induce C).dist_le (walkInduce p (hpath_C p (p.isPath_of_length_eq_dist hp) u.2 v.2))
    rw [walkInduce_length, hp] at hle
    exact hle
  have hpendant_uniq : ∀ (c : V) (P₁ P₂ : Set V),
      IsPendantPath H c P₁ → IsPendantPath H c P₂ → P₁ = P₂ := by
    intro c P₁ P₂ h1 h2
    rcases compOfCut_eq_or_disjoint (pendant_isCompOfCut h1) (pendant_isCompOfCut h2) with heq | hdisj
    · exact heq
    · exact (hAtMostOnePendant h1 h2 hdisj).elim
  have hpendant_disj_C : ∀ {u v : V}, u ∈ C → v ∈ C → u ≠ v →
      ∀ {Pu Pv : Set V}, IsPendantPath H u Pu → IsPendantPath H v Pv → Disjoint Pu Pv := by
    intro u v huC hvC huv Pu Pv hPu hPv
    obtain ⟨du, rfl⟩ := hPu
    rw [Set.disjoint_left]
    intro y hyPu hyPv
    have hnotPv : ∀ j ≤ du.k, du.p j ∉ Pv := by
      intro j hjk
      induction j with
      | zero =>
        rw [du.hp0]
        exact huC v Pv hPv
      | succ j ih =>
        intro hmem
        have hprev := ih (by omega)
        have hadj : H.Adj (du.p (j + 1)) (du.p j) := (du.hadj j (by omega)).symm
        rcases pendant_sep hPv (du.p (j + 1)) hmem (du.p j) hadj with h1 | h2
        · exact hprev h1
        · rcases Nat.eq_zero_or_pos j with rfl | hj1
          · exact huv (du.hp0.symm.trans h2)
          · exact hvC u du.K ⟨du, rfl⟩ (by rw [du.hK]; exact ⟨j, hj1, by omega, h2.symm⟩)
    rw [du.hK] at hyPu
    obtain ⟨i, _, hiku, rfl⟩ := hyPu
    exact hnotPv i hiku hyPv
  have hcompl_C : ∀ y : V, y ∉ C → ∃ v : V, v ∈ C ∧ ∃ Pv : Set V, IsPendantPath H v Pv ∧ y ∈ Pv := by
    intro y hyC
    let Cfin : Finset V := Finset.univ.filter (fun v => v ∈ C)
    have hCfin_ne : Cfin.Nonempty := by
      obtain ⟨v0, hv0⟩ := hC_nonempty
      exact ⟨v0, Finset.mem_filter.mpr ⟨Finset.mem_univ v0, hv0⟩⟩
    obtain ⟨v, hv_mem, hv_min⟩ := Finset.exists_min_image Cfin (fun u => H.dist y u) hCfin_ne
    have hvC : v ∈ C := (Finset.mem_filter.mp hv_mem).2
    have hyv : y ≠ v := fun h => hyC (h ▸ hvC)
    obtain ⟨q, hq⟩ := hH.exists_walk_length_eq_dist y v
    have hqpos : 0 < q.length := by
      have := hH.pos_dist_of_ne hyv
      omega
    set y' := q.getVert (q.length - 1)
    have hy'_adj : H.Adj y' v := by
      have := q.adj_getVert_succ (by omega : q.length - 1 < q.length)
      simpa [show q.length - 1 + 1 = q.length by omega, Walk.getVert_length] using this
    have hy'_notC : y' ∉ C := by
      intro hmem
      have h1 : H.dist y y' = q.length - 1 := dist_getVert_left hH hq (by omega)
      have h2 := hv_min y' (Finset.mem_filter.mpr ⟨Finset.mem_univ y', hmem⟩)
      omega
    have hex_P : ∃ c : V, ∃ P : Set V, IsPendantPath H c P ∧ y' ∈ P := by
      by_contra hno
      apply hy'_notC
      intro c P hP hyP
      exact hno ⟨c, P, hP, hyP⟩
    obtain ⟨c, P, hP, hy'P⟩ := hex_P
    have hvc : v = c := by
      rcases pendant_sep hP y' hy'P v hy'_adj with hvP | rfl
      · exact (hvC c P hP hvP).elim
      · rfl
    subst hvc
    refine ⟨v, hvC, P, hP, ?_⟩
    have hwalk_in_P : ∀ i < q.length, q.getVert i ∈ P := by
      intro i hi
      suffices ∀ d, d ≤ q.length - 1 → q.getVert (q.length - 1 - d) ∈ P by
        have := this (q.length - 1 - i) (by omega)
        rwa [show q.length - 1 - (q.length - 1 - i) = i by omega] at this
      intro d hd
      induction d with
      | zero => simpa using hy'P
      | succ d ih =>
        have hprev := ih (by omega)
        have hadj_step : H.Adj (q.getVert (q.length - 1 - d)) (q.getVert (q.length - 1 - (d + 1))) := by
          have := q.adj_getVert_succ (by omega : q.length - 1 - (d + 1) < q.length)
          rw [show q.length - 1 - (d + 1) + 1 = q.length - 1 - d by omega] at this
          exact this.symm
        rcases pendant_sep hP _ hprev _ hadj_step with hmem | hEqv
        · exact hmem
        · exfalso
          have h1 := dist_getVert_left hH hq (by omega : q.length - 1 - (d + 1) ≤ q.length)
          rw [hEqv] at h1
          omega
    simpa [Walk.getVert_zero] using hwalk_in_P 0 hqpos
  -- Single-`Classical.choose` parametrization of pendant paths on `C` via `PendantData`
  let hasP : V → Prop := fun v => Nonempty (PendantData H v)
  let dv : ∀ v : V, hasP v → PendantData H v := fun _ h => Classical.choice h
  let kv : V → ℕ := fun v => if h : hasP v then (dv v h).k else 0
  let pv : V → ℕ → V := fun v => if h : hasP v then (dv v h).p else fun _ => v
  have hpv0 : ∀ v : V, pv v 0 = v := by
    intro v
    by_cases h : hasP v
    · simp only [pv, dif_pos h]; exact (dv v h).hp0
    · simp [pv, dif_neg h]
  have hkv0 : ∀ v : V, ¬ hasP v → kv v = 0 := fun v h => dif_neg h
  have hdecomp : ∀ y : V, ∃ v : V, v ∈ C ∧ ∃ t : ℕ, t ≤ kv v ∧ y = pv v t := by
    intro y
    by_cases hyC : y ∈ C
    · exact ⟨y, hyC, 0, Nat.zero_le _, (hpv0 y).symm⟩
    · obtain ⟨v, hvC, P, ⟨d, rfl⟩, hyP⟩ := hcompl_C y hyC
      have hhas : hasP v := ⟨d⟩
      have hPeq : d.K = (dv v hhas).K := hpendant_uniq v d.K (dv v hhas).K ⟨d, rfl⟩ ⟨dv v hhas, rfl⟩
      rw [hPeq, (dv v hhas).hK] at hyP
      obtain ⟨t, _, ht, rfl⟩ := hyP
      refine ⟨v, hvC, t, ?_, ?_⟩
      · simp only [kv, dif_pos hhas]; exact ht
      · simp only [pv, dif_pos hhas]
  have htip_noncut : ∀ v : V, v ∈ C → ¬ IsCutVertex H (pv v (kv v)) := by
    intro v hvC
    by_cases hhas : hasP v
    · simp only [kv, pv, dif_pos hhas]
      set d := dv v hhas
      exact not_isCutVertex_of_unique_adj hH (d.p d.k) (d.p (d.k - 1))
        (fun w hw => by
          rcases d.hnbr d.k d.hk le_rfl w hw with h1 | ⟨hlt, _⟩
          · exact h1
          · omega) (by omega)
    · rw [hkv0 v hhas, hpv0 v]
      intro hcutv
      obtain ⟨P, ⟨d, rfl⟩⟩ := hex_pendant_of_cut v hcutv
      exact hhas ⟨d⟩
  have hdist_same : ∀ (u : V) (s t : ℕ), s ≤ kv u → t ≤ kv u →
      H.dist (pv u s) (pv u t) = max s t - min s t := by
    intro u s t hs ht
    by_cases hhas : hasP u
    · simp only [kv, pv, dif_pos hhas] at hs ht ⊢
      exact pendant_dist_eq hH (dv u hhas) hs ht
    · rw [hkv0 u hhas] at hs ht
      have hs0 : s = 0 := by omega
      have ht0 : t = 0 := by omega
      subst hs0; subst ht0; simp
  have hdist_diff : ∀ {u v : V}, u ∈ C → v ∈ C → u ≠ v →
      ∀ (s t : ℕ), s ≤ kv u → t ≤ kv v →
      H.dist (pv u s) (pv v t) = s + H.dist u v + t := by
    intro u v huC hvC huv s t hs ht
    have hstep1 : H.dist (pv u s) (pv v t) = s + H.dist u (pv v t) := by
      rcases Nat.eq_zero_or_pos s with rfl | hspos
      · simp [hpv0 u]
      · have hhasu : hasP u := by
          by_contra hno; rw [hkv0 u hno] at hs; omega
        set du := dv u hhasu
        have hpus_eq : pv u s = du.p s := by simp [pv, dif_pos hhasu, du]
        have hs' : s ≤ du.k := by simpa [kv, dif_pos hhasu, du] using hs
        have hpus_in : pv u s ∈ du.K := by
          rw [hpus_eq, du.hK]; exact ⟨s, hspos, hs', rfl⟩
        have hpvt_not : pv v t ∉ du.K := by
          rcases Nat.eq_zero_or_pos t with rfl | htpos
          · rw [hpv0 v]; exact hvC u du.K ⟨du, rfl⟩
          · have hhasv : hasP v := by
              by_contra hno; rw [hkv0 v hno] at ht; omega
            set d_v := dv v hhasv
            have ht' : t ≤ d_v.k := by simpa [kv, dif_pos hhasv, d_v] using ht
            have hpvt_in : pv v t ∈ d_v.K := by
              simp only [pv, dif_pos hhasv]; rw [d_v.hK]; exact ⟨t, htpos, ht', rfl⟩
            exact Set.disjoint_right.mp (hpendant_disj_C huC hvC huv ⟨du, rfl⟩ ⟨d_v, rfl⟩) hpvt_in
        rw [dist_through_cut hH (pendant_sep ⟨du, rfl⟩) hpus_in hpvt_not]
        have hd1 : H.dist (pv u s) u = s := by
          have h0 := hdist_same u s 0 hs (Nat.zero_le _)
          rw [hpv0 u] at h0; omega
        omega
    have hstep2 : H.dist u (pv v t) = H.dist u v + t := by
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · simp [hpv0 v]
      · have hhasv : hasP v := by
          by_contra hno; rw [hkv0 v hno] at ht; omega
        set d_v := dv v hhasv
        have ht' : t ≤ d_v.k := by simpa [kv, dif_pos hhasv, d_v] using ht
        have hpvt_in : pv v t ∈ d_v.K := by
          simp only [pv, dif_pos hhasv]; rw [d_v.hK]; exact ⟨t, htpos, ht', rfl⟩
        have hu_not : u ∉ d_v.K := huC v d_v.K ⟨d_v, rfl⟩
        rw [dist_through_cut_symm hH (pendant_sep ⟨d_v, rfl⟩) hu_not hpvt_in]
        have hd2 : H.dist v (pv v t) = t := by
          have h0 := hdist_same v 0 t (Nat.zero_le _) ht
          rw [hpv0 v] at h0; omega
        omega
    omega
  have hedge_path_bound : ∀ {u v : V}, u ∈ C → v ∈ C → H.Adj u v →
      kv u + kv v + 2 ≤ 2 * r - 1 := by
    intro u v huC hvC hadj_uv
    have huv : u ≠ v := hadj_uv.ne
    let a := kv u
    let b := kv v
    let f : ℕ → V := fun i => if i ≤ a then pv u (a - i) else pv v (i - a - 1)
    have hle := induced_path_card_le_tree (G := H) (a + b + 1) f ?_ ?_ ?_
    · omega
    · intro i hi j hj heq
      simp only [Set.mem_Icc] at hi hj
      dsimp only [f] at heq
      split_ifs at heq with hi' hj' hj'
      · have h1 := hdist_same u (a - i) 0 (by omega) (Nat.zero_le _)
        have h2 := hdist_same u (a - j) 0 (by omega) (Nat.zero_le _)
        rw [heq] at h1; omega
      · have h1 := hdist_diff huC hvC huv (a - i) (j - a - 1) (by omega) (by omega)
        rw [heq, SimpleGraph.dist_self] at h1
        have := hH.pos_dist_of_ne huv
        omega
      · have h1 := hdist_diff huC hvC huv (a - j) (i - a - 1) (by omega) (by omega)
        rw [heq, SimpleGraph.dist_self] at h1
        have := hH.pos_dist_of_ne huv
        omega
      · have h1 := hdist_same v (i - a - 1) 0 (by omega) (Nat.zero_le _)
        have h2 := hdist_same v (j - a - 1) 0 (by omega) (Nat.zero_le _)
        rw [heq] at h1; omega
    · intro i hi
      dsimp only [f]
      by_cases h1 : i + 1 ≤ a
      · rw [if_pos (by omega), if_pos h1]
        have hhasu : hasP u := by
          by_contra hno; have := hkv0 u hno; omega
        simp only [pv, dif_pos hhasu]
        have ha_eq : a = (dv u hhasu).k := dif_pos hhasu
        have heq : a - i = (a - (i + 1)) + 1 := by omega
        rw [heq]
        exact ((dv u hhasu).hadj (a - (i + 1)) (by omega)).symm
      · by_cases h2 : i = a
        · subst h2
          rw [if_pos le_rfl, if_neg (by omega)]
          rw [Nat.sub_self, show a + 1 - a - 1 = 0 by omega, hpv0 u, hpv0 v]
          exact hadj_uv
        · rw [if_neg (by omega), if_neg (by omega)]
          have hhasv : hasP v := by
            by_contra hno; have := hkv0 v hno; omega
          simp only [pv, dif_pos hhasv]
          have hb_eq : b = (dv v hhasv).k := dif_pos hhasv
          have heq : i + 1 - a - 1 = (i - a - 1) + 1 := by omega
          rw [heq]
          exact (dv v hhasv).hadj (i - a - 1) (by omega)
    · intro i j hji hi hadj
      dsimp only [f] at hadj
      split_ifs at hadj with hi' hj' hj'
      · have h1 := hdist_same u (a - i) (a - j) (by omega) (by omega)
        have h2 : H.dist (pv u (a - i)) (pv u (a - j)) = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.mpr hadj
        omega
      · omega
      · have h1 := hdist_diff huC hvC huv (a - j) (i - a - 1) (by omega) (by omega)
        have h2 : H.dist (pv u (a - j)) (pv v (i - a - 1)) = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
        have h3 : H.dist u v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj_uv
        omega
      · have h1 := hdist_same v (i - a - 1) (j - a - 1) (by omega) (by omega)
        have h2 : H.dist (pv v (i - a - 1)) (pv v (j - a - 1)) = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.mpr hadj
        omega
  -- Step 4: Uniform pendant path length across edges of `C`
  have hkv_edge_le : ∀ {u v : V}, u ∈ C → v ∈ C → H.Adj u v → kv u ≤ kv v := by
    intro u v huC hvC hadj_uv
    by_contra hgt
    push Not at hgt
    have huv : u ≠ v := hadj_uv.ne
    have hduv : H.dist u v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj_uv
    set x := pv v (kv v)
    obtain ⟨w, hwne, hwr, hwu⟩ := hUnivWitness x (htip_noncut v hvC)
    change H.dist w (pv v (kv v)) = r at hwr
    have hwu' : ∀ u' : V, u' ≠ pv v (kv v) → H.dist w u' ≤ r - 1 := hwu
    obtain ⟨z, hzC, s, hs, hw_eq⟩ := hdecomp w
    rw [hw_eq] at hwr hwu'
    by_cases hzu : z = u
    · have hs_u : s ≤ kv u := hzu ▸ hs
      have hwr_u : H.dist (pv u s) (pv v (kv v)) = r := hzu ▸ hwr
      have hwu_u : ∀ u' : V, u' ≠ pv v (kv v) → H.dist (pv u s) u' ≤ r - 1 := hzu ▸ hwu'
      have hr_eq : r = s + 1 + kv v := by
        have := hdist_diff huC hvC huv s (kv v) hs_u le_rfl
        omega
      rcases Nat.eq_zero_or_pos s with rfl | hspos
      · have hne_ux : pv u (kv u) ≠ pv v (kv v) := by
          intro heq
          have := hdist_diff huC hvC huv (kv u) (kv v) le_rfl le_rfl
          rw [heq, SimpleGraph.dist_self] at this
          omega
        have h1 := hwu_u (pv u (kv u)) hne_ux
        have h2 := hdist_same u 0 (kv u) (Nat.zero_le _) le_rfl
        omega
      · obtain ⟨y, hy_ge⟩ := exists_dist_ge_radius hH (pv u (s - 1))
        obtain ⟨a, haC, t, ht, hy_eq⟩ := hdecomp y
        rw [hy_eq] at hy_ge
        by_cases hau : a = u
        · have ht_u : t ≤ kv u := hau ▸ ht
          have hy_ge_u : r ≤ H.dist (pv u (s - 1)) (pv u t) := hau ▸ hy_ge
          have hd1 := hdist_same u (s - 1) t (by omega) ht_u
          have hd2 := hdist_same u s t hs_u ht_u
          by_cases hts : t < s
          · have hne_x : pv u t ≠ pv v (kv v) := by
              intro heq
              have := hdist_diff huC hvC huv t (kv v) ht_u le_rfl
              rw [heq, SimpleGraph.dist_self] at this
              omega
            have := hwu_u (pv u t) hne_x
            omega
          · have hbound := hedge_path_bound huC hvC hadj_uv
            omega
        · have hd1 := hdist_diff huC haC (Ne.symm hau) (s - 1) t (by omega) ht
          have hd2 := hdist_diff huC haC (Ne.symm hau) s t hs_u ht
          by_cases hyx : pv a t = pv v (kv v)
          · rw [hyx] at hd2; omega
          · have := hwu_u (pv a t) hyx; omega
    · by_cases hzv : z = v
      · have hs_v : s ≤ kv v := hzv ▸ hs
        have hwr_v : H.dist (pv v s) (pv v (kv v)) = r := hzv ▸ hwr
        have h1 := hdist_same v s (kv v) hs_v le_rfl
        have hbound := hedge_path_bound huC hvC hadj_uv
        omega
      · have h1 := hdist_diff hzC hvC hzv s (kv v) hs le_rfl
        have h2 := hdist_diff hzC huC hzu s (kv u) hs le_rfl
        have hne_ux : pv u (kv u) ≠ pv v (kv v) := by
          intro heq
          have := hdist_diff huC hvC huv (kv u) (kv v) le_rfl le_rfl
          rw [heq, SimpleGraph.dist_self] at this
          omega
        have h3 := hwu' (pv u (kv u)) hne_ux
        have htri : H.dist z v ≤ H.dist z u + H.dist u v := hH.dist_triangle
        omega
  obtain ⟨c_cut, hc_cut⟩ := hcut
  obtain ⟨P0, hP0⟩ := hex_pendant_of_cut c_cut hc_cut
  obtain ⟨y0, hy0P⟩ := compOfCut_nonempty (pendant_isCompOfCut hP0)
  have hy0_notC : y0 ∉ C := fun h => h c_cut P0 hP0 hy0P
  obtain ⟨v0, hv0C, P_v0, ⟨d_v0, rfl⟩, _⟩ := hcompl_C y0 hy0_notC
  set k := kv v0
  have hk_pos : 1 ≤ k := by
    have hhas0 : hasP v0 := ⟨d_v0⟩
    have : k = (dv v0 hhas0).k := dif_pos hhas0
    have := (dv v0 hhas0).hk
    omega
  have hkv_const : ∀ v : V, v ∈ C → kv v = k := by
    intro v hvC
    obtain ⟨q⟩ := hHC_conn ⟨v0, hv0C⟩ ⟨v, hvC⟩
    have hwalk_eq : ∀ {a b : C} (w : (H.induce C).Walk a b), kv a.1 = kv b.1 := by
      intro a b w
      induction w with
      | nil => rfl
      | @cons a b d hab _ ih =>
        have h1 := hkv_edge_le a.2 b.2 hab
        have h2 := hkv_edge_le b.2 a.2 hab.symm
        omega
    exact (hwalk_eq q).symm
  -- Step 5: Compute `r ≤ rC + k` and build an induced tree of size `≥ 2 * r`
  set rC := (H.induce C).radius.toNat
  have hrC_pos : 1 ≤ rC := by
    have : Nontrivial C := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hne0 : (H.induce C).radius ≠ 0 := SimpleGraph.radius_ne_zero_of_nontrivial
    have hcoe : ((rC : ℕ) : ℕ∞) ≠ 0 := by
      rw [← radius_eq_coe_toNat hHC_conn]
      exact hne0
    have : rC ≠ 0 := by simpa using hcoe
    omega
  have hr_le : r ≤ rC + k := by
    obtain ⟨u0, hu0⟩ := exists_center_dist_le hHC_conn
    refine radius_toNat_le_of_exists hH ⟨u0.1, fun y => ?_⟩
    obtain ⟨v, hvC, t, ht, rfl⟩ := hdecomp y
    have hkv_eq := hkv_const v hvC
    have hdu : H.dist u0.1 v ≤ rC := by
      rw [← hHC_dist u0 ⟨v, hvC⟩]
      exact hu0 ⟨v, hvC⟩
    by_cases huv : u0.1 = v
    · subst huv
      have hd := hdist_same u0.1 0 t (Nat.zero_le _) ht
      rw [hpv0 u0.1] at hd
      omega
    · have hd := hdist_diff u0.2 hvC huv 0 t (Nat.zero_le _) ht
      rw [hpv0 u0.1] at hd
      omega
  have hex_core_tree : ∃ S_core : Finset V, (∀ v ∈ S_core, v ∈ C) ∧
      (H.induce (S_core : Set V)).IsTree ∧ max 2 (2 * rC - 1) ≤ S_core.card := by
    by_cases hrC1 : rC = 1
    · have hex_adj : ∃ u v : C, (H.induce C).Adj u v := by
        have : Nontrivial C := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
        obtain ⟨a, b, hab⟩ := exists_pair_ne C
        obtain ⟨q, hq⟩ := hHC_conn.exists_walk_length_eq_dist a b
        have hpos : 0 < q.length := by
          have := hHC_conn.pos_dist_of_ne hab
          omega
        exact ⟨q.getVert 0, q.getVert 1, q.adj_getVert_succ hpos⟩
      obtain ⟨u, v, huv⟩ := hex_adj
      have hne : v.1 ∉ ({u.1} : Finset V) := by
        rw [Finset.mem_singleton]
        exact fun h => huv.ne (Subtype.ext h.symm)
      refine ⟨insert v.1 {u.1}, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw'
        · exact v.2
        · rw [Finset.mem_singleton.mp hw']; exact u.2
      · refine IsTree.induce_insert_of_unique_adj (isTree_singleton u.1) hne
          (Finset.mem_singleton_self u.1) huv.symm ?_
        intro b hb _; exact Finset.mem_singleton.mp hb
      · rw [Finset.card_insert_of_notMem hne, Finset.card_singleton, hrC1]
        omega
    · have hchung : 2 * rC - 1 ≤ largestInducedTreeSize (H.induce C) :=
        chung_induced_tree_bound hHC_conn
      have hne_set :
          ({ n | ∃ t : Finset C, t.card = n ∧ ((H.induce C).induce (t : Set C)).IsTree }).Nonempty := by
        have : Nonempty C := hC_nonempty.to_subtype
        let x0 : C := Classical.arbitrary C
        exact ⟨1, {x0}, Finset.card_singleton x0, isTree_singleton x0⟩
      have hbdd : BddAbove { n | ∃ t : Finset C, t.card = n ∧ ((H.induce C).induce (t : Set C)).IsTree } := by
        refine ⟨Fintype.card C, ?_⟩
        rintro n ⟨t, rfl, _⟩
        exact Finset.card_le_univ t
      have hmem_sup : largestInducedTreeSize (H.induce C) ∈
          { n | ∃ t : Finset C, t.card = n ∧ ((H.induce C).induce (t : Set C)).IsTree } :=
        Nat.sSup_mem hne_set hbdd
      obtain ⟨t, htcard, httree⟩ := hmem_sup
      let S_core : Finset V := t.map ⟨Subtype.val, Subtype.val_injective⟩
      refine ⟨S_core, ?_, ?_, ?_⟩
      · intro w hw
        simp only [S_core, Finset.mem_map, Function.Embedding.coeFn_mk] at hw
        obtain ⟨a, _, rfl⟩ := hw
        exact a.2
      · let e : ((H.induce C).induce (t : Set C)) ≃g (H.induce (S_core : Set V)) :=
          { toFun := fun x => ⟨x.1.1, by
              simp only [Finset.mem_coe, S_core, Finset.mem_map, Function.Embedding.coeFn_mk]
              exact ⟨x.1, x.2, rfl⟩⟩
            invFun := fun y =>
              ⟨⟨y.1, by
                  have hy := y.2
                  simp only [Finset.mem_coe, S_core, Finset.mem_map, Function.Embedding.coeFn_mk] at hy
                  obtain ⟨a, _, hval⟩ := hy
                  rw [← hval]; exact a.2⟩,
                by
                  have hy := y.2
                  simp only [Finset.mem_coe, S_core, Finset.mem_map, Function.Embedding.coeFn_mk] at hy
                  obtain ⟨a, ha, hval⟩ := hy
                  have hsub : (⟨y.1, by rw [← hval]; exact a.2⟩ : C) = a := Subtype.ext hval.symm
                  rw [hsub]; exact ha⟩
            left_inv := fun x => by ext; rfl
            right_inv := fun y => by ext; rfl
            map_rel_iff' := by intro a b; rfl }
        exact (e.isTree_iff).mp httree
      · have hcard : S_core.card = t.card := Finset.card_map _
        omega
  obtain ⟨S_core, hS_sub, hS_tree, hS_card⟩ := hex_core_tree
  -- Attach all `S_core` pendant paths of length `k`
  have hattach_all : ∀ A : Finset V, A ⊆ S_core →
      let T := S_core ∪ A.biUnion (fun v => (Finset.Icc 1 k).image (pv v))
      (H.induce (T : Set V)).IsTree ∧ T.card = S_core.card + A.card * k := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      intro _
      dsimp only
      rw [Finset.biUnion_empty, Finset.union_empty, Finset.card_empty, zero_mul, add_zero]
      exact ⟨hS_tree, rfl⟩
    | @insert v A hvA ih =>
      intro hsub
      have hAsub : A ⊆ S_core := Finset.Subset.trans (Finset.subset_insert v A) hsub
      have hvS : v ∈ S_core := hsub (Finset.mem_insert_self v A)
      have hvC : v ∈ C := hS_sub v hvS
      have hprev := ih hAsub
      set T_prev := S_core ∪ A.biUnion (fun u => (Finset.Icc 1 k).image (pv u))
      have hkv_eq : kv v = k := hkv_const v hvC
      have hhasv : hasP v := by
        by_contra hno; have := hkv0 v hno; omega
      set d_v := dv v hhasv
      have hdv_k : d_v.k = k := by simpa [kv, dif_pos hhasv, d_v] using hkv_eq
      have hpv_eq : pv v = d_v.p := dif_pos hhasv
      have hnot_in_Tprev : ∀ w ∈ d_v.K, w ∉ T_prev := by
        intro w hwK hmem
        rcases Finset.mem_union.mp hmem with hS | hbi
        · exact hS_sub w hS v d_v.K ⟨d_v, rfl⟩ hwK
        · obtain ⟨u, huA, hmem_u⟩ := Finset.mem_biUnion.mp hbi
          obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hmem_u
          simp only [Finset.mem_Icc] at hj
          have huC : u ∈ C := hS_sub u (hAsub huA)
          have hku_eq : kv u = k := hkv_const u huC
          have hhasu : hasP u := by
            by_contra hno; have := hkv0 u hno; omega
          set d_u := dv u hhasu
          have hdu_k : d_u.k = k := by simpa [kv, dif_pos hhasu, d_u] using hku_eq
          have hpu_in : pv u j ∈ d_u.K := by
            simp only [pv, dif_pos hhasu]; rw [d_u.hK]; exact ⟨j, hj.1, by omega, rfl⟩
          have huv : v ≠ u := fun h => hvA (h ▸ huA)
          exact Set.disjoint_left.mp (hpendant_disj_C hvC huC huv ⟨d_v, rfl⟩ ⟨d_u, rfl⟩)
            hwK (heq ▸ hpu_in)
      have hchain := induce_attach_chain_isTree hprev.1 k (pv v)
        (Finset.mem_union_left _ (by rw [hpv0 v]; exact hvS))
        (fun i hi1 hik => hnot_in_Tprev (pv v i) (by
          rw [hpv_eq, d_v.hK]; exact ⟨i, hi1, by omega, rfl⟩))
        (by rw [hpv_eq, ← hdv_k]; exact d_v.hinj)
        (fun i hi => by rw [hpv_eq]; exact d_v.hadj i (by omega))
        (fun i hi1 hik w hw hadj => by
          rw [hpv_eq] at hadj
          rcases d_v.hnbr i hi1 (by omega) w hadj with rfl | ⟨hlt, rfl⟩
          · rcases eq_or_lt_of_le hi1 with rfl | hgt
            · exact ⟨rfl, by rw [hpv_eq]⟩
            · exfalso
              exact hnot_in_Tprev (d_v.p (i - 1))
                (by rw [d_v.hK]; exact ⟨i - 1, by omega, by omega, rfl⟩) hw
          · exfalso
            exact hnot_in_Tprev (d_v.p (i + 1))
              (by rw [d_v.hK]; exact ⟨i + 1, by omega, by omega, rfl⟩) hw)
        (fun i j hj1 hji hik hadj => by
          rw [hpv_eq] at hadj
          rcases d_v.hnbr i (by omega) (by omega) (d_v.p j) hadj with heq | ⟨hlt, heq⟩
          · have := d_v.hinj ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ heq
            omega
          · have := d_v.hinj ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ heq
            omega)
      have hTeq : S_core ∪ (insert v A).biUnion (fun u => (Finset.Icc 1 k).image (pv u)) =
          T_prev ∪ (Finset.Icc 1 k).image (pv v) := by
        ext x
        simp only [T_prev, Finset.mem_union, Finset.biUnion_insert]
        tauto
      rw [hTeq]
      refine ⟨hchain.1, ?_⟩
      rw [hchain.2, hprev.2, Finset.card_insert_of_notMem hvA, Nat.add_mul, Nat.one_mul]
      omega
  have hfinal := hattach_all S_core Finset.Subset.rfl
  have hcard_le : (S_core ∪ S_core.biUnion (fun v => (Finset.Icc 1 k).image (pv v))).card ≤
      largestInducedTreeSize H := card_le_largestInducedTreeSize hfinal.1
  have hmul : 2 * (rC + k) ≤ S_core.card + S_core.card * k := by
    rcases eq_or_lt_of_le hrC_pos with hrC1 | hrC2
    · rw [← hrC1] at hS_card ⊢
      have h2 : 2 ≤ S_core.card := le_trans (le_max_left _ _) hS_card
      nlinarith
    · have h2 : 2 * rC - 1 ≤ S_core.card := le_trans (le_max_right _ _) hS_card
      have hS_ge : 2 * rC ≤ S_core.card + 1 := by omega
      nlinarith
  omega

/-- Gebendorfer's Theorem: every connected finite graph with a cut vertex satisfies
`2 * rad(G) ≤ largestInducedTreeSize G`. -/
private lemma gebendorfer_cut_vertex_bound {G : SimpleGraph V}
    (hG : G.Connected) (hcut : HasCutVertex G) :
    2 * G.radius.toNat ≤ largestInducedTreeSize G := by
  classical
  have hstrong : ∀ (n : ℕ) (S : Finset V), S.card = n →
      (G.induce (S : Set V)).Connected → HasCutVertex (G.induce (S : Set V)) →
      2 * (G.induce (S : Set V)).radius.toNat ≤ largestInducedTreeSize (G.induce (S : Set V)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hScard hSconn hScut
      set H := G.induce (S : Set V)
      set r := H.radius.toNat
      by_cases hr2 : r < 2
      · rcases Nat.eq_zero_or_pos r with hr0 | hr1
        · omega
        · obtain ⟨u, v, huv⟩ : ∃ u v : (S : Set V), H.Adj u v := by
            obtain ⟨a, b, hab⟩ : ∃ a b : (S : Set V), a ≠ b := by
              by_contra hsub
              push Not at hsub
              have : Subsingleton (S : Set V) := ⟨hsub⟩
              have : Nonempty (S : Set V) := hSconn.nonempty
              have hr0 : H.radius = 0 :=
                SimpleGraph.radius_eq_zero_iff.mpr ⟨inferInstance, inferInstance⟩
              have : r = 0 := by simp [r, hr0]
              omega
            obtain ⟨q, hq⟩ := hSconn.exists_walk_length_eq_dist a b
            have hpos : 0 < q.length := by
              have := hSconn.pos_dist_of_ne hab
              omega
            exact ⟨q.getVert 0, q.getVert 1, q.adj_getVert_succ hpos⟩
          have h2 := two_le_largestInducedTreeSize_of_adj huv
          omega
      · by_contra hlt
        have htree : largestInducedTreeSize H ≤ 2 * r - 1 := by omega
        refine cut_vertex_minimal_contradiction hSconn hScut (by omega) htree ?_
        intro x hnc hcutx
        let S' := S.erase x.1
        let e' : H.induce ({x}ᶜ : Set (S : Set V)) ≃g G.induce (S' : Set V) :=
          { toFun := fun y => ⟨y.1.1, by
              simp only [S', Finset.mem_coe, Finset.mem_erase]
              exact ⟨fun hval => y.2 (Subtype.ext hval), y.1.2⟩⟩
            invFun := fun y => ⟨⟨y.1, (Finset.mem_erase.mp y.2).2⟩, by
              simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
              exact fun hsub => (Finset.mem_erase.mp y.2).1 (congrArg Subtype.val hsub)⟩
            left_inv := fun y => by ext; rfl
            right_inv := fun y => by ext; rfl
            map_rel_iff' := by intro a b; rfl }
        have hS'_conn : (G.induce (S' : Set V)).Connected := e'.connected_iff.mp (not_not.mp hnc)
        have hS'_cut : HasCutVertex (G.induce (S' : Set V)) := by
          obtain ⟨c', hc'⟩ := hcutx
          refine ⟨e' c', fun hconn => hc' ?_⟩
          let e'' : (H.induce ({x}ᶜ : Set (S : Set V))).induce ({c'}ᶜ : Set _) ≃g
              (G.induce (S' : Set V)).induce ({e' c'}ᶜ : Set _) :=
            { toFun := fun y => ⟨e' y.1, fun h => y.2 (e'.injective h)⟩
              invFun := fun y => ⟨e'.symm y.1, fun h => y.2 (by
                have := congrArg e' h
                simpa using this)⟩
              left_inv := fun y => by apply Subtype.ext; exact e'.symm_apply_apply y.1
              right_inv := fun y => by apply Subtype.ext; exact e'.apply_symm_apply y.1
              map_rel_iff' := by intro a b; exact e'.map_rel_iff }
          exact e''.connected_iff.mpr hconn
        have hS'_card : S'.card < n := by
          rw [← hScard]
          exact Finset.card_erase_lt_of_mem x.2
        have hih := ih S'.card hS'_card S' rfl hS'_conn hS'_cut
        have hrad_eq : (H.induce ({x}ᶜ : Set (S : Set V))).radius = (G.induce (S' : Set V)).radius :=
          iso_radius_eq e'
        have htree_eq : largestInducedTreeSize (H.induce ({x}ᶜ : Set (S : Set V))) =
            largestInducedTreeSize (G.induce (S' : Set V)) :=
          iso_largestInducedTreeSize_eq e'
        have htree_le : largestInducedTreeSize (H.induce ({x}ᶜ : Set (S : Set V))) ≤
            largestInducedTreeSize H :=
          largestInducedTreeSize_ge_of_induce ({x}ᶜ : Set (S : Set V))
        rw [hrad_eq]
        omega
  let e : G.induce ((Finset.univ : Finset V) : Set V) ≃g G :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, Finset.mem_univ x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := by intro a b; rfl }
  have hcut_univ : HasCutVertex (G.induce ((Finset.univ : Finset V) : Set V)) := by
    obtain ⟨c, hc⟩ := hcut
    refine ⟨e.symm c, fun hconn => hc ?_⟩
    let e'' : (G.induce ((Finset.univ : Finset V) : Set V)).induce ({e.symm c}ᶜ : Set _) ≃g
        G.induce ({c}ᶜ : Set V) :=
      { toFun := fun y => ⟨e y.1, fun h => y.2 (e.injective (by simpa using h))⟩
        invFun := fun y => ⟨e.symm y.1, fun h => y.2 (by
          have := congrArg e h
          simpa using this)⟩
        left_inv := fun y => by apply Subtype.ext; exact e.symm_apply_apply y.1
        right_inv := fun y => by apply Subtype.ext; exact e.apply_symm_apply y.1
        map_rel_iff' := by intro a b; exact e.map_rel_iff }
    exact e''.connected_iff.mp hconn
  have hres := hstrong (Fintype.card V) Finset.univ Finset.card_univ (e.connected_iff.mpr hG) hcut_univ
  rw [iso_radius_eq e, iso_largestInducedTreeSize_eq e] at hres
  exact hres

end CutVertexTheorem

end GraphConjecture84Proof

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture84.conjecture84 := by
  intro α _ _ _ G _ h hδ
  by_cases hδ2 : 2 ≤ G.minDegree
  · have hgeo : G.radius.toNat + 1 ≤ largestInducedTreeSize G :=
      GraphConjecture84Proof.geodesic_tree_bound h
    have hδ_pos : (0 : ℝ) < (G.minDegree : ℝ) := Nat.cast_pos.mpr hδ
    have hδ2_real : (2 : ℝ) ≤ (G.minDegree : ℝ) := Nat.ofNat_le_cast.mpr hδ2
    have hgeo_real : (G.radius.toNat : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) := by
      exact_mod_cast hgeo
    rw [div_le_iff₀ hδ_pos]
    nlinarith
  · have hδ1 : G.minDegree = 1 := by omega
    rw [hδ1, Nat.cast_one, div_one]
    suffices hnat : 2 * G.radius.toNat ≤ largestInducedTreeSize G by
      exact_mod_cast hnat
    by_cases hr2 : G.radius.toNat < 2
    · obtain ⟨a, b, hab⟩ := exists_pair_ne α
      obtain ⟨q, hq⟩ := h.exists_walk_length_eq_dist a b
      have hpos : 0 < q.length := by
        have := h.pos_dist_of_ne hab
        omega
      have h2 := GraphConjecture84Proof.two_le_largestInducedTreeSize_of_adj
        (q.adj_getVert_succ hpos)
      omega
    · obtain ⟨x, hxdeg⟩ := G.exists_minimal_degree_vertex
      rw [hδ1] at hxdeg
      have hcard1 : (G.neighborFinset x).card = 1 := hxdeg.symm
      obtain ⟨c, hc_eq⟩ := Finset.card_eq_one.mp hcard1
      have hx_only_c : ∀ w : α, G.Adj x w → w = c := by
        intro w hw
        have hmem : w ∈ G.neighborFinset x := (G.mem_neighborFinset x w).mpr hw
        rw [hc_eq, Finset.mem_singleton] at hmem
        exact hmem
      have hxc_adj : G.Adj x c := by
        have hmem : c ∈ G.neighborFinset x := by rw [hc_eq]; exact Finset.mem_singleton_self c
        exact (G.mem_neighborFinset x c).mp hmem
      have hcut : GraphConjecture84Proof.HasCutVertex G := by
        refine ⟨c, fun hconn => ?_⟩
        obtain ⟨y, hy⟩ := GraphConjecture84Proof.exists_dist_ge_radius h c
        have hyc : y ≠ c := by
          intro heq
          rw [heq, SimpleGraph.dist_self] at hy
          omega
        have hxc : x ≠ c := hxc_adj.ne
        have hyx : y ≠ x := by
          intro heq
          have h1 : G.dist c x = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxc_adj.symm
          rw [heq, h1] at hy
          omega
        obtain ⟨q⟩ := hconn ⟨x, hxc⟩ ⟨y, hyc⟩
        cases q with
        | nil => exact hyx rfl
        | @cons _ next _ hadj _ =>
          exact next.2 (hx_only_c next.1 hadj)
      exact GraphConjecture84Proof.gebendorfer_cut_vertex_bound h hcut
