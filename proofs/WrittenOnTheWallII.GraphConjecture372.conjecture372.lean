import FormalConjectures.WrittenOnTheWallII.GraphConjecture372

/-!
Proof of `WrittenOnTheWallII.GraphConjecture372.conjecture372` via the sharp
additive tree inequality `τ(T) ≤ γ_t(T) + (p(T) - 2)` for every finite tree `T`
with `|V(T)| ≥ 2`.
-/

namespace OMAWowii372

open SimpleGraph Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

private lemma fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩
  have : v = 0 ∨ v = 1 := by omega
  rcases this with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [Fintype α] in
/-- A 2-coloring of `T` yields on any finite subset `S` a vertex cover of `T[S]`
of size at most `S.card / 2`. -/
lemma exists_half_cover_of_colorable (T : SimpleGraph α) (c : T.Coloring (Fin 2)) (S : Finset α) :
    ∃ C : Finset α, C ⊆ S ∧ 2 * C.card ≤ S.card ∧
      ∀ u ∈ S, ∀ v ∈ S, T.Adj u v → u ∈ C ∨ v ∈ C := by
  obtain ⟨S0, hS0⟩ : ∃ X, X = S.filter (fun v => c v = 0) := ⟨_, rfl⟩
  obtain ⟨S1, hS1⟩ : ∃ X, X = S.filter (fun v => c v = 1) := ⟨_, rfl⟩
  have hdisj : Disjoint S0 S1 := by
    rw [hS0, hS1, Finset.disjoint_filter]
    intro v _ h0 h1
    rw [h0] at h1
    exact absurd h1 (by decide)
  have hunion : S0 ∪ S1 = S := by
    ext v
    simp only [hS0, hS1, mem_union, mem_filter]
    constructor
    · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
    · intro hv
      rcases fin2_cases (c v) with h0 | h1
      · exact Or.inl ⟨hv, h0⟩
      · exact Or.inr ⟨hv, h1⟩
  have hsum : S0.card + S1.card = S.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hcov0 : ∀ u ∈ S, ∀ v ∈ S, T.Adj u v → u ∈ S0 ∨ v ∈ S0 := by
    intro u hu v hv hadj
    have hne : c u ≠ c v := c.valid hadj
    simp only [hS0, mem_filter]
    rcases fin2_cases (c u) with h0 | h1
    · exact Or.inl ⟨hu, h0⟩
    · rcases fin2_cases (c v) with hv0 | hv1
      · exact Or.inr ⟨hv, hv0⟩
      · exact absurd (h1.trans hv1.symm) hne
  have hcov1 : ∀ u ∈ S, ∀ v ∈ S, T.Adj u v → u ∈ S1 ∨ v ∈ S1 := by
    intro u hu v hv hadj
    have hne : c u ≠ c v := c.valid hadj
    simp only [hS1, mem_filter]
    rcases fin2_cases (c u) with h0 | h1
    · rcases fin2_cases (c v) with hv0 | hv1
      · exact absurd (h0.trans hv0.symm) hne
      · exact Or.inr ⟨hv, hv1⟩
    · exact Or.inl ⟨hu, h1⟩
  by_cases hle : S0.card ≤ S1.card
  · exact ⟨S0, hS0 ▸ filter_subset _ _, by omega, hcov0⟩
  · exact ⟨S1, hS1 ▸ filter_subset _ _, by omega, hcov1⟩

omit [Fintype α] [DecidableEq α] in
/-- Every finite vertex cover `C` bounds `T.vertexCoverNum.toNat`. -/
lemma vertexCoverNum_toNat_le (T : SimpleGraph α) (C : Finset α)
    (hC : T.IsVertexCover (C : Set α)) : T.vertexCoverNum.toNat ≤ C.card := by
  have h1 : T.vertexCoverNum ≤ (C : Set α).encard := hC.vertexCoverNum_le
  rw [Set.encard_coe_eq_coe_finsetCard] at h1
  exact ENat.toNat_le_of_le_natCast h1

omit [Fintype α] in
/-- In an acyclic graph, any path is induced: vertices at positions `i` and `j`
are adjacent iff `|i - j| = 1`. -/
lemma isAcyclic_adj_getVert_iff (T : SimpleGraph α) (hA : T.IsAcyclic) :
    ∀ {u v : α} {p : T.Walk u v}, p.IsPath →
      ∀ {i j : ℕ}, i ≤ p.length → j ≤ p.length →
        (T.Adj (p.getVert i) (p.getVert j) ↔ i + 1 = j ∨ j + 1 = i) := by
  intro u v p
  induction p with
  | nil =>
    intro _ i j hi hj
    simp only [Walk.length_nil, Nat.le_zero] at hi hj
    subst hi; subst hj
    simp
  | @cons a b c hab q ih =>
    intro hp i j hi hj
    rw [Walk.cons_isPath_iff] at hp
    rcases hp with ⟨hq, haq⟩
    simp only [Walk.length_cons] at hi hj
    cases i with
    | zero =>
      cases j with
      | zero => simp
      | succ k =>
        simp only [Walk.getVert_zero, Walk.getVert_cons_succ]
        constructor
        · intro hadj
          left
          suffices hk : k = 0 by omega
          have hmem : q.getVert k ∈ q.support := q.getVert_mem_support k
          let q1 : T.Walk b (q.getVert k) := q.takeUntil (q.getVert k) hmem
          have hq1_path : q1.IsPath := hq.takeUntil hmem
          have ha_not : a ∉ q1.support :=
            fun h => haq (Walk.support_takeUntil_subset_support q hmem h)
          let p1 : T.Path a (q.getVert k) := ⟨Walk.cons hab q1, hq1_path.cons ha_not⟩
          let p2 : T.Path a (q.getVert k) := ⟨Walk.cons hadj Walk.nil,
            Walk.IsPath.cons Walk.IsPath.nil (by simp [hadj.ne])⟩
          have heq : p1 = p2 := (hA.subsingleton_path a (q.getVert k)).elim p1 p2
          have hlen : p1.1.length = p2.1.length := congrArg (fun x => x.1.length) heq
          simp only [p1, p2, Walk.length_cons, Walk.length_nil] at hlen
          have hq1_len : q1.length = 0 := by omega
          have hnil : q1.Nil := Walk.length_eq_zero_iff.mp hq1_len
          have hb_eq : b = q.getVert k := Walk.Nil.eq hnil
          have h0 : q.getVert 0 = q.getVert k := by simpa using hb_eq
          have hinj := (Walk.IsPath.getVert_injOn_iff q).mpr hq
          exact (hinj (by simp) (by simp; omega) h0).symm
        · intro h
          have hk : k = 0 := by omega
          subst hk
          simpa using hab
    | succ k =>
      cases j with
      | zero =>
        simp only [Walk.getVert_zero, Walk.getVert_cons_succ]
        constructor
        · intro hadj
          right
          suffices hk : k = 0 by omega
          have hmem : q.getVert k ∈ q.support := q.getVert_mem_support k
          let q1 : T.Walk b (q.getVert k) := q.takeUntil (q.getVert k) hmem
          have hq1_path : q1.IsPath := hq.takeUntil hmem
          have ha_not : a ∉ q1.support :=
            fun h => haq (Walk.support_takeUntil_subset_support q hmem h)
          let p1 : T.Path a (q.getVert k) := ⟨Walk.cons hab q1, hq1_path.cons ha_not⟩
          let p2 : T.Path a (q.getVert k) := ⟨Walk.cons hadj.symm Walk.nil,
            Walk.IsPath.cons Walk.IsPath.nil (by simp [hadj.symm.ne])⟩
          have heq : p1 = p2 := (hA.subsingleton_path a (q.getVert k)).elim p1 p2
          have hlen : p1.1.length = p2.1.length := congrArg (fun x => x.1.length) heq
          simp only [p1, p2, Walk.length_cons, Walk.length_nil] at hlen
          have hq1_len : q1.length = 0 := by omega
          have hnil : q1.Nil := Walk.length_eq_zero_iff.mp hq1_len
          have hb_eq : b = q.getVert k := Walk.Nil.eq hnil
          have h0 : q.getVert 0 = q.getVert k := by simpa using hb_eq
          have hinj := (Walk.IsPath.getVert_injOn_iff q).mpr hq
          exact (hinj (by simp) (by simp; omega) h0).symm
        · intro h
          have hk : k = 0 := by omega
          subst hk
          simpa using hab.symm
      | succ l =>
        simp only [Walk.getVert_cons_succ]
        rw [ih hq (by omega) (by omega)]
        omega

omit [Fintype α] [DecidableEq α] in
private lemma getVert_succ_mem_edges (T : SimpleGraph α) :
    ∀ {u v : α} (p : T.Walk u v) {i : ℕ}, i < p.length →
      s(p.getVert i, p.getVert (i + 1)) ∈ p.edges := by
  intro u v p
  induction p with
  | nil => intro i hi; simp at hi
  | cons _ q ih =>
    intro i hi
    cases i with
    | zero => simp [Walk.edges_cons]
    | succ k =>
      simp only [Walk.edges_cons, Walk.getVert_cons_succ, List.mem_cons]
      exact Or.inr (ih (by simp only [Walk.length_cons] at hi; omega))

omit [Fintype α] in
/-- In an acyclic graph, an edge between two vertices of a path belongs to `p.edges`. -/
lemma isAcyclic_mem_edges_of_adj (T : SimpleGraph α) (hA : T.IsAcyclic)
    {u v x y : α} {p : T.Walk u v} (hp : p.IsPath)
    (hx : x ∈ p.support) (hy : y ∈ p.support) (hadj : T.Adj x y) :
    s(x, y) ∈ p.edges := by
  obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  obtain ⟨j, rfl, hj⟩ := Walk.mem_support_iff_exists_getVert.mp hy
  have h := (isAcyclic_adj_getVert_iff T hA hp hi hj).mp hadj
  rcases h with rfl | rfl
  · exact getVert_succ_mem_edges T p (by omega)
  · rw [Sym2.eq_swap]
    exact getVert_succ_mem_edges T p (by omega)

/-- Double-counting lemma on a bipartite relation between two finite sets `A` and `B`:
if every `x ∈ A` has exactly 1 neighbor in `B` and every `y ∈ B` has exactly 2 neighbors in `A`,
then `A.card = 2 * B.card`. -/
private lemma card_eq_two_mul_of_deg_one_two (G : SimpleGraph α) [DecidableRel G.Adj]
    (A B : Finset α)
    (hA : ∀ x ∈ A, (G.neighborFinset x ∩ B).card = 1)
    (hB : ∀ y ∈ B, (G.neighborFinset y ∩ A).card = 2) :
    A.card = 2 * B.card := by
  have hl : ∀ x ∈ A, (G.neighborFinset x ∩ B).card = ∑ y ∈ B, if G.Adj x y then 1 else 0 := by
    intro x _
    rw [Finset.sum_boole, Nat.cast_id]
    congr 1; ext y; simp only [mem_inter, mem_filter, mem_neighborFinset]; tauto
  have hr : ∀ y ∈ B, (G.neighborFinset y ∩ A).card = ∑ x ∈ A, if G.Adj x y then 1 else 0 := by
    intro y _
    rw [Finset.sum_boole, Nat.cast_id]
    congr 1; ext x; simp only [mem_inter, mem_filter, mem_neighborFinset, adj_comm]; tauto
  have hswap : ∑ x ∈ A, (G.neighborFinset x ∩ B).card = ∑ y ∈ B, (G.neighborFinset y ∩ A).card := by
    calc ∑ x ∈ A, (G.neighborFinset x ∩ B).card
        = ∑ x ∈ A, ∑ y ∈ B, (if G.Adj x y then 1 else 0) := Finset.sum_congr rfl hl
      _ = ∑ y ∈ B, ∑ x ∈ A, (if G.Adj x y then 1 else 0) := Finset.sum_comm
      _ = ∑ y ∈ B, (G.neighborFinset y ∩ A).card := Finset.sum_congr rfl (fun y hy => (hr y hy).symm)
  have h1 : ∑ x ∈ A, (G.neighborFinset x ∩ B).card = A.card := by
    rw [Finset.sum_congr rfl hA]; simp
  have h2 : ∑ y ∈ B, (G.neighborFinset y ∩ A).card = 2 * B.card := by
    rw [Finset.sum_congr rfl hB]; simp [mul_comm]
  omega

/-- For a nontrivial tree, `totalDominationNumber` is attained by a finite total dominating set
of cardinality at least 2. -/
lemma exists_min_totalDom (T : SimpleGraph α) (hT : T.IsTree) (hn : 2 ≤ Fintype.card α) :
    ∃ D : Finset α, T.IsTotalDominating (D : Set α) ∧ D.card = T.totalDominationNumber ∧
      2 ≤ D.card := by
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have huniv : T.IsTotalDominating ((Finset.univ : Finset α) : Set α) := by
    intro v
    obtain ⟨x, hx⟩ := exists_ne v
    obtain ⟨p⟩ := hT.connected.preconnected v x
    cases p with
    | nil => exact absurd rfl hx
    | cons hadj _ => exact ⟨_, mem_coe.mpr (mem_univ _), hadj⟩
  have hne : {n | ∃ D : Finset α, T.IsTotalNDominatingSet n D}.Nonempty :=
    ⟨Fintype.card α, Finset.univ, ⟨huniv, Finset.card_univ⟩⟩
  obtain ⟨D, hD⟩ := Nat.sInf_mem hne
  refine ⟨D, hD.isTotalDominating, hD.card_eq, ?_⟩
  obtain ⟨v⟩ : Nonempty α := inferInstance
  obtain ⟨w, hwD, _⟩ := hD.isTotalDominating v
  obtain ⟨u, huD, hwu⟩ := hD.isTotalDominating w
  have hne_uw : u ≠ w := (T.ne_of_adj hwu).symm
  have hsub : ({u, w} : Finset α) ⊆ D := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_coe.mp huD
    · exact mem_coe.mp hwD
  have h2 : ({u, w} : Finset α).card = 2 := card_pair hne_uw
  calc 2 = ({u, w} : Finset α).card := h2.symm
    _ ≤ D.card := card_le_card hsub

/-- Every finite graph has a minimum path cover, and if `|V| ≥ 1`, its size is at least `1`. -/
lemma exists_min_pathCover (T : SimpleGraph α) (hn : 1 ≤ Fintype.card α) :
    ∃ P : Finset (Finset α), T.IsPathCover P ∧ P.card = T.pathCoverNumber ∧ 1 ≤ P.card := by
  let P0 : Finset (Finset α) := Finset.univ.image (fun v => ({v} : Finset α))
  have hP0 : T.IsPathCover P0 := by
    refine ⟨?_, ?_, ?_⟩
    · intro s1 hs1 s2 hs2 hne
      rw [mem_image] at hs1 hs2
      obtain ⟨v1, _, rfl⟩ := hs1
      obtain ⟨v2, _, rfl⟩ := hs2
      rw [disjoint_singleton]
      intro h
      exact hne (congrArg singleton h)
    · intro v _
      rw [mem_biUnion]
      exact ⟨{v}, mem_image_of_mem _ (mem_univ v), mem_singleton_self v⟩
    · intro s hs
      rw [mem_image] at hs
      obtain ⟨v, _, rfl⟩ := hs
      exact ⟨v, v, Walk.nil, Walk.IsPath.nil, by simp⟩
  have hne : {k | ∃ P : Finset (Finset α), P.card = k ∧ T.IsPathCover P}.Nonempty :=
    ⟨P0.card, P0, rfl, hP0⟩
  obtain ⟨P, hcard, hP⟩ := Nat.sInf_mem hne
  refine ⟨P, hP, hcard, ?_⟩
  have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v⟩ : Nonempty α := inferInstance
  have hv := hP.2.1 (mem_univ v)
  rw [mem_biUnion] at hv
  obtain ⟨s, hs, _⟩ := hv
  exact Finset.card_pos.mpr ⟨s, hs⟩

/-- Parity helper for a prefix `{g i | i < jmin}` of a path before its first cross-vertex `g jmin`. -/
private lemma prefix_card_odd
    (T F Gcross : SimpleGraph α) [DecidableRel T.Adj] [DecidableRel F.Adj]
    [DecidableRel Gcross.Adj]
    (D s U Q : Finset α) (L jmin : ℕ) (g : ℕ → α)
    (hF_le_T : F ≤ T)
    (hC_iff : ∀ {x y}, Gcross.Adj x y ↔ T.Adj x y ∧ ¬ F.Adj x y)
    (huniq : ∀ x : α, (T.neighborFinset x ∩ D).card = 1)
    (hFdeg2 : ∀ d ∈ D, F.degree d = 2)
    (hU_def : ∀ x, x ∈ U ↔ x ∈ s ∧ 0 < Gcross.degree x)
    (hU_sub_D : U ⊆ s ∩ D)
    (hU_no_F_D : ∀ x ∈ U, ∀ y, F.Adj x y → y ∉ D)
    (hget_mem : ∀ i ≤ L, g i ∈ s)
    (hget_surj : ∀ x ∈ s, ∃ i ≤ L, g i = x)
    (hget_inj : ∀ i ≤ L, ∀ j ≤ L, g i = g j → i = j)
    (hF_s : ∀ {x y}, x ∈ s → F.Adj x y → y ∈ s)
    (hF_adj_idx : ∀ i ≤ L, ∀ j ≤ L, F.Adj (g i) (g j) ↔ i + 1 = j ∨ j + 1 = i)
    (hF_deg_int : ∀ i ≤ L, g i ∈ D → 0 < i ∧ i < L)
    (hjmin_le : jmin ≤ L) (hjmin_pos : 0 < jmin)
    (hjmin_U : g jmin ∈ U)
    (hjmin_min : ∀ i ≤ L, g i ∈ U → jmin ≤ i)
    (hmem_Q : ∀ x, x ∈ Q ↔ ∃ i ≤ L, i < jmin ∧ g i = x) :
    Q.card % 2 = 1 := by
  have huniq_nbr : ∀ {x y1 y2 : α}, T.Adj x y1 → y1 ∈ D → T.Adj x y2 → y2 ∈ D → y1 = y2 := by
    intro x y1 y2 h1 hy1 h2 hy2
    exact Finset.card_le_one.mp (le_of_eq (huniq x))
      y1 (mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr h1, hy1⟩)
      y2 (mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr h2, hy2⟩)
  obtain ⟨w0, hw0⟩ : ∃ w, w = g (jmin - 1) := ⟨_, rfl⟩
  have hw0_Q : w0 ∈ Q := (hmem_Q w0).mpr ⟨jmin - 1, by omega, by omega, hw0.symm⟩
  have hw0_adj : F.Adj w0 (g jmin) := by
    rw [hw0]; exact (hF_adj_idx (jmin - 1) (by omega) jmin hjmin_le).mpr (by omega)
  have hw0_notD : w0 ∉ D := hU_no_F_D (g jmin) hjmin_U w0 hw0_adj.symm
  have h2m : (Q \ {w0}).card = 2 * (Q ∩ D).card := by
    apply card_eq_two_mul_of_deg_one_two F (Q \ {w0}) (Q ∩ D)
    · intro x hx
      rw [mem_sdiff, mem_singleton] at hx
      obtain ⟨i, hi, hilt, rfl⟩ := (hmem_Q x).mp hx.1
      have hi_lt' : i + 1 < jmin := by
        by_contra hge
        have heq : i = jmin - 1 := by omega
        exact hx.2 (by rw [hw0, heq])
      have hx_notU : g i ∉ U := fun hmem => by have := hjmin_min i hi hmem; omega
      have hC0 : Gcross.degree (g i) = 0 := by
        by_contra hpos; exact hx_notU ((hU_def (g i)).mpr ⟨hget_mem i hi, by omega⟩)
      have hsub_eq : F.neighborFinset (g i) ∩ (Q ∩ D) = T.neighborFinset (g i) ∩ D := by
        ext y
        simp only [mem_inter, mem_neighborFinset]
        constructor
        · rintro ⟨hxy, _, hyD⟩; exact ⟨hF_le_T hxy, hyD⟩
        · rintro ⟨hxy, hyD⟩
          have hFxy : F.Adj (g i) y := by
            by_contra hnF
            have hpos : 0 < Gcross.degree (g i) := by
              rw [← card_neighborFinset_eq_degree]
              exact Finset.card_pos.mpr ⟨y, (mem_neighborFinset _ _ _).mpr (hC_iff.mpr ⟨hxy, hnF⟩)⟩
            omega
          obtain ⟨j, hj, rfl⟩ := hget_surj y (hF_s (hget_mem i hi) hFxy)
          have hij := (hF_adj_idx i hi j hj).mp hFxy
          exact ⟨hFxy, (hmem_Q _).mpr ⟨j, hj, by omega, rfl⟩, hyD⟩
      rw [hsub_eq]; exact huniq (g i)
    · intro d hd
      rw [mem_inter] at hd
      obtain ⟨i, hi, hilt, rfl⟩ := (hmem_Q d).mp hd.1
      have hi_pos : 0 < i ∧ i < L := hF_deg_int i hi hd.2
      have hi_ne1 : i ≠ jmin - 1 := fun heq => hw0_notD (by rw [hw0, ← heq]; exact hd.2)
      have hi_ne2 : i + 1 ≠ jmin - 1 := by
        intro heq
        have hadj_dw : F.Adj (g i) w0 := by
          rw [hw0]; exact (hF_adj_idx i hi (jmin - 1) (by omega)).mpr (Or.inl heq)
        have hEq : g i = g jmin :=
          huniq_nbr (hF_le_T hadj_dw.symm) hd.2 (hF_le_T hw0_adj) (mem_inter.mp (hU_sub_D hjmin_U)).2
        have := hget_inj i hi jmin hjmin_le hEq; omega
      have hsub_eq : F.neighborFinset (g i) ∩ (Q \ {w0}) = F.neighborFinset (g i) := by
        ext y
        simp only [mem_inter, mem_sdiff, mem_singleton, mem_neighborFinset]
        constructor
        · rintro ⟨h, _⟩; exact h
        · intro hdy
          obtain ⟨j, hj, rfl⟩ := hget_surj y (hF_s (hget_mem i hi) hdy)
          have hij := (hF_adj_idx i hi j hj).mp hdy
          refine ⟨hdy, (hmem_Q _).mpr ⟨j, hj, by omega, rfl⟩, fun heqw => ?_⟩
          have := hget_inj j hj (jmin - 1) (by omega) (heqw.trans hw0); omega
      rw [hsub_eq, card_neighborFinset_eq_degree]
      exact hFdeg2 (g i) hd.2
  have hcard_sdiff : (Q \ {w0}).card + 1 = Q.card := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_add_one hw0_Q]
  omega

/-- Local cover construction on a single path `p` of a path cover in the sharp equality case. -/
private lemma local_path_cover
    (T F Gcross : SimpleGraph α) [DecidableRel T.Adj] [DecidableRel F.Adj]
    [DecidableRel Gcross.Adj]
    (hA : T.IsAcyclic) (col : T.Coloring (Fin 2)) (D s : Finset α)
    (u v : α) (p : T.Walk u v) (hp : p.IsPath) (hseq : s = p.support.toFinset)
    (hF_le_T : F ≤ T)
    (hF_s : ∀ {x y}, x ∈ s → F.Adj x y → y ∈ s)
    (hF_iff : ∀ {x y}, x ∈ s → y ∈ s → (F.Adj x y ↔ T.Adj x y))
    (hC_iff : ∀ {x y}, Gcross.Adj x y ↔ T.Adj x y ∧ ¬ F.Adj x y)
    (huniq : ∀ x : α, (T.neighborFinset x ∩ D).card = 1)
    (hFdeg2 : ∀ d ∈ D, F.degree d = 2)
    (hCzero : ∀ x : α, x ∉ D → Gcross.degree x = 0)
    (hU_ne : (s.filter (fun x => 0 < Gcross.degree x)).Nonempty) :
    ∃ Cs : Finset α, Cs ⊆ s ∧
      (∀ x ∈ s, 0 < Gcross.degree x → x ∈ Cs) ∧
      (∀ x ∈ s, ∀ y ∈ s, T.Adj x y → x ∈ Cs ∨ y ∈ Cs) ∧
      Cs.card + 1 ≤ (s ∩ D).card + (s.filter (fun x => 0 < Gcross.degree x)).card := by
  obtain ⟨L, hL⟩ : ∃ n, n = p.length := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ X, X = s.filter (fun x => 0 < Gcross.degree x) := ⟨_, rfl⟩
  have hU_def : ∀ x, x ∈ U ↔ x ∈ s ∧ 0 < Gcross.degree x := fun x => by rw [hU, mem_filter]
  have hU_ne' : U.Nonempty := hU ▸ hU_ne
  have huniq_nbr : ∀ {x y1 y2 : α}, T.Adj x y1 → y1 ∈ D → T.Adj x y2 → y2 ∈ D → y1 = y2 := by
    intro x y1 y2 h1 hy1 h2 hy2
    exact Finset.card_le_one.mp (le_of_eq (huniq x))
      y1 (mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr h1, hy1⟩)
      y2 (mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr h2, hy2⟩)
  have hC_mem_D : ∀ {x y : α}, Gcross.Adj x y → x ∈ D ∧ y ∈ D := by
    intro x y hxy
    have hx_pos : 0 < Gcross.degree x := by
      rw [← card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨y, (mem_neighborFinset _ _ _).mpr hxy⟩
    have hy_pos : 0 < Gcross.degree y := by
      rw [← card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨x, (mem_neighborFinset _ _ _).mpr hxy.symm⟩
    constructor
    · by_contra hx; exact absurd (hCzero x hx) (by omega)
    · by_contra hy; exact absurd (hCzero y hy) (by omega)
  have hU_sub_D : U ⊆ s ∩ D := by
    intro x hx
    rw [hU_def] at hx
    refine mem_inter.mpr ⟨hx.1, ?_⟩
    by_contra hxnD
    exact absurd (hCzero x hxnD) (by omega)
  have hU_no_F_D : ∀ x ∈ U, ∀ y, F.Adj x y → y ∉ D := by
    intro x hx y hxy hyD
    have hpos := ((hU_def x).mp hx).2
    rw [← card_neighborFinset_eq_degree] at hpos
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    rw [mem_neighborFinset] at hz
    have hzD : z ∈ D := (hC_mem_D hz).2
    have heq : y = z := huniq_nbr (hF_le_T hxy) hyD (hC_iff.mp hz).1 hzD
    subst heq
    exact (hC_iff.mp hz).2 hxy
  have hget_mem : ∀ i ≤ L, p.getVert i ∈ s := fun i _ => by
    rw [hseq, List.mem_toFinset]; exact p.getVert_mem_support i
  have hget_surj : ∀ x ∈ s, ∃ i ≤ L, p.getVert i = x := by
    intro x hxs
    obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.mp
      (List.mem_toFinset.mp (hseq ▸ hxs))
    exact ⟨i, hL ▸ hi, rfl⟩
  have hget_inj : ∀ i ≤ L, ∀ j ≤ L, p.getVert i = p.getVert j → i = j :=
    fun i hi j hj h => ((Walk.IsPath.getVert_injOn_iff p).mpr hp) (hL ▸ hi) (hL ▸ hj) h
  have hF_adj_idx : ∀ i ≤ L, ∀ j ≤ L,
      F.Adj (p.getVert i) (p.getVert j) ↔ i + 1 = j ∨ j + 1 = i := by
    intro i hi j hj
    rw [hF_iff (hget_mem i hi) (hget_mem j hj)]
    exact isAcyclic_adj_getVert_iff T hA hp (hL ▸ hi) (hL ▸ hj)
  have hF_deg_int : ∀ i ≤ L, p.getVert i ∈ D → 0 < i ∧ i < L := by
    intro i hi hD_i
    have hdeg := hFdeg2 (p.getVert i) hD_i
    rw [← card_neighborFinset_eq_degree] at hdeg
    constructor
    · by_contra hi0
      have hi0' : i = 0 := by omega
      subst hi0'
      have hsub : F.neighborFinset (p.getVert 0) ⊆ {p.getVert 1} := by
        intro y hy
        rw [mem_neighborFinset] at hy
        obtain ⟨j, hj, rfl⟩ := hget_surj y (hF_s (hget_mem 0 hi) hy)
        have hij := (hF_adj_idx 0 hi j hj).mp hy
        rw [mem_singleton]; congr 1; omega
      have hle : (F.neighborFinset (p.getVert 0)).card ≤ 1 := (card_le_card hsub).trans (by simp)
      omega
    · by_contra hiL
      have hiL' : i = L := by omega
      have hsub : F.neighborFinset (p.getVert i) ⊆ {p.getVert (L - 1)} := by
        intro y hy
        rw [mem_neighborFinset] at hy
        obtain ⟨j, hj, rfl⟩ := hget_surj y (hF_s (hget_mem i hi) hy)
        have hij := (hF_adj_idx i hi j hj).mp hy
        rw [mem_singleton]; congr 1; omega
      have hle : (F.neighborFinset (p.getVert i)).card ≤ 1 := (card_le_card hsub).trans (by simp)
      omega
  -- `(s \ U).card = 2 * (s ∩ D).card`
  have hsU_card : (s \ U).card = 2 * (s ∩ D).card := by
    apply card_eq_two_mul_of_deg_one_two F (s \ U) (s ∩ D)
    · intro x hx
      rw [mem_sdiff] at hx
      have hC0 : Gcross.degree x = 0 := by
        by_contra hpos; exact hx.2 ((hU_def x).mpr ⟨hx.1, by omega⟩)
      have hsub_eq : F.neighborFinset x ∩ (s ∩ D) = T.neighborFinset x ∩ D := by
        ext y
        simp only [mem_inter, mem_neighborFinset]
        constructor
        · rintro ⟨hxy, _, hyD⟩; exact ⟨hF_le_T hxy, hyD⟩
        · rintro ⟨hxy, hyD⟩
          have hFxy : F.Adj x y := by
            by_contra hnF
            have hpos : 0 < Gcross.degree x := by
              rw [← card_neighborFinset_eq_degree]
              exact Finset.card_pos.mpr ⟨y, (mem_neighborFinset _ _ _).mpr (hC_iff.mpr ⟨hxy, hnF⟩)⟩
            omega
          exact ⟨hFxy, hF_s hx.1 hFxy, hyD⟩
      rw [hsub_eq]; exact huniq x
    · intro d hd
      rw [mem_inter] at hd
      have hsub_eq : F.neighborFinset d ∩ (s \ U) = F.neighborFinset d := by
        ext y
        simp only [mem_inter, mem_sdiff, mem_neighborFinset]
        constructor
        · rintro ⟨h, _⟩; exact h
        · intro hdy
          exact ⟨hdy, hF_s hd.1 hdy, fun hyU => hU_no_F_D y hyU d hdy.symm hd.2⟩
      rw [hsub_eq, card_neighborFinset_eq_degree]
      exact hFdeg2 d hd.2
  -- Min and max indices of `U` along `p` (opaque variables)
  obtain ⟨IU, hIU⟩ : ∃ X, X = (Finset.range (L + 1)).filter (fun i => p.getVert i ∈ U) := ⟨_, rfl⟩
  have hIU_ne : IU.Nonempty := by
    obtain ⟨x, hxU⟩ := hU_ne'
    obtain ⟨i, hi, rfl⟩ := hget_surj x ((hU_def x).mp hxU).1
    exact ⟨i, hIU ▸ mem_filter.mpr ⟨mem_range.mpr (by omega), hxU⟩⟩
  obtain ⟨jmin, hjmin_eq⟩ : ∃ n, n = IU.min' hIU_ne := ⟨_, rfl⟩
  obtain ⟨jmax, hjmax_eq⟩ : ∃ n, n = IU.max' hIU_ne := ⟨_, rfl⟩
  have hjmin_mem : jmin ∈ IU := hjmin_eq ▸ min'_mem IU hIU_ne
  have hjmax_mem : jmax ∈ IU := hjmax_eq ▸ max'_mem IU hIU_ne
  have hjmin_le : jmin ≤ L := by
    have := mem_range.mp (mem_filter.mp (hIU ▸ hjmin_mem)).1; omega
  have hjmax_le : jmax ≤ L := by
    have := mem_range.mp (mem_filter.mp (hIU ▸ hjmax_mem)).1; omega
  have hjmin_U : p.getVert jmin ∈ U := by
    have h := hjmin_mem; rw [hIU, mem_filter] at h; exact h.2
  have hjmax_U : p.getVert jmax ∈ U := by
    have h := hjmax_mem; rw [hIU, mem_filter] at h; exact h.2
  have hjmin_b : 0 < jmin ∧ jmin < L := hF_deg_int jmin hjmin_le (mem_inter.mp (hU_sub_D hjmin_U)).2
  have hjmax_b : 0 < jmax ∧ jmax < L := hF_deg_int jmax hjmax_le (mem_inter.mp (hU_sub_D hjmax_U)).2
  have hjmin_le_jmax : jmin ≤ jmax := hjmin_eq ▸ min'_le IU jmax hjmax_mem
  have hjmin_min : ∀ i ≤ L, p.getVert i ∈ U → jmin ≤ i := fun i hi hxU =>
    hjmin_eq ▸ min'_le IU i (hIU ▸ mem_filter.mpr ⟨mem_range.mpr (by omega), hxU⟩)
  have hjmax_max : ∀ i ≤ L, p.getVert i ∈ U → i ≤ jmax := fun i hi hxU =>
    hjmax_eq ▸ le_max' IU i (hIU ▸ mem_filter.mpr ⟨mem_range.mpr (by omega), hxU⟩)
  -- Three disjoint pieces of `s \ U` (opaque variables)
  obtain ⟨Q0, hQ0⟩ : ∃ X, X = ((Finset.range (L + 1)).filter (fun i => i < jmin)).image p.getVert := ⟨_, rfl⟩
  obtain ⟨Q1, hQ1⟩ : ∃ X, X = ((Finset.range (L + 1)).filter (fun i => jmax < i)).image p.getVert := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ X, X = ((Finset.range (L + 1)).filter
      (fun i => jmin < i ∧ i < jmax ∧ p.getVert i ∉ U)).image p.getVert := ⟨_, rfl⟩
  have hmem_Q0 : ∀ x, x ∈ Q0 ↔ ∃ i ≤ L, i < jmin ∧ p.getVert i = x := by
    intro x; simp only [hQ0, mem_image, mem_filter, mem_range]; constructor
    · rintro ⟨i, ⟨hi, hlt⟩, rfl⟩; exact ⟨i, by omega, hlt, rfl⟩
    · rintro ⟨i, hi, hlt, rfl⟩; exact ⟨i, ⟨by omega, hlt⟩, rfl⟩
  have hmem_Q1 : ∀ x, x ∈ Q1 ↔ ∃ i ≤ L, jmax < i ∧ p.getVert i = x := by
    intro x; simp only [hQ1, mem_image, mem_filter, mem_range]; constructor
    · rintro ⟨i, ⟨hi, hgt⟩, rfl⟩; exact ⟨i, by omega, hgt, rfl⟩
    · rintro ⟨i, hi, hgt, rfl⟩; exact ⟨i, ⟨by omega, hgt⟩, rfl⟩
  have hmem_R : ∀ x, x ∈ R ↔ ∃ i ≤ L, jmin < i ∧ i < jmax ∧ p.getVert i ∉ U ∧ p.getVert i = x := by
    intro x; simp only [hR, mem_image, mem_filter, mem_range]; constructor
    · rintro ⟨i, ⟨hi, h1, h2, h3⟩, rfl⟩; exact ⟨i, by omega, h1, h2, h3, rfl⟩
    · rintro ⟨i, hi, h1, h2, h3, rfl⟩; exact ⟨i, ⟨by omega, h1, h2, h3⟩, rfl⟩
  -- Both `Q0.card` and `Q1.card` are odd by `prefix_card_odd` (using `i ↦ p.getVert i` and `i ↦ p.getVert (L - i)`)
  have hQ0_odd : Q0.card % 2 = 1 :=
    prefix_card_odd T F Gcross D s U Q0 L jmin p.getVert hF_le_T hC_iff huniq hFdeg2
      hU_def hU_sub_D hU_no_F_D hget_mem hget_surj hget_inj hF_s hF_adj_idx hF_deg_int
      hjmin_le hjmin_b.1 hjmin_U hjmin_min hmem_Q0
  have hQ1_odd : Q1.card % 2 = 1 := by
    refine prefix_card_odd T F Gcross D s U Q1 L (L - jmax) (fun i => p.getVert (L - i))
      hF_le_T hC_iff huniq hFdeg2 hU_def hU_sub_D hU_no_F_D
      (fun i hi => hget_mem (L - i) (by omega))
      (fun x hx => let ⟨i, hi, heq⟩ := hget_surj x hx; ⟨L - i, by omega, by simpa [Nat.sub_sub_self hi] using heq⟩)
      (fun i hi j hj h => by have := hget_inj (L - i) (by omega) (L - j) (by omega) h; omega)
      hF_s
      (fun i hi j hj => by rw [hF_adj_idx (L - i) (by omega) (L - j) (by omega)]; omega)
      (fun i hi hd => by have := hF_deg_int (L - i) (by omega) hd; omega)
      (by omega) (by omega)
      (by simpa [Nat.sub_sub_self hjmax_le] using hjmax_U)
      (fun i hi hxU => by have := hjmax_max (L - i) (by omega) hxU; omega)
      ?_
    intro x
    rw [hmem_Q1]
    constructor
    · rintro ⟨i, hi, hgt, rfl⟩
      exact ⟨L - i, by omega, by omega, by simp [Nat.sub_sub_self hi]⟩
    · rintro ⟨i, hi, hlt, rfl⟩
      exact ⟨L - i, by omega, by omega, rfl⟩
  -- Partition `s \ U = Q0 ⊔ Q1 ⊔ R`
  have hdisj_Q0Q1 : Disjoint Q0 Q1 := by
    rw [Finset.disjoint_left]
    intro x h0 h1
    obtain ⟨i, hi, hilt, rfl⟩ := (hmem_Q0 x).mp h0
    obtain ⟨j, hj, hjgt, heq⟩ := (hmem_Q1 _).mp h1
    have := hget_inj j hj i hi heq; omega
  have hdisj_Q0R : Disjoint Q0 R := by
    rw [Finset.disjoint_left]
    intro x h0 hR'
    obtain ⟨i, hi, hilt, rfl⟩ := (hmem_Q0 x).mp h0
    obtain ⟨j, hj, hjgt, _, _, heq⟩ := (hmem_R _).mp hR'
    have := hget_inj j hj i hi heq; omega
  have hdisj_Q1R : Disjoint Q1 R := by
    rw [Finset.disjoint_left]
    intro x h1 hR'
    obtain ⟨i, hi, higt, rfl⟩ := (hmem_Q1 x).mp h1
    obtain ⟨j, hj, _, hjlt, _, heq⟩ := (hmem_R _).mp hR'
    have := hget_inj j hj i hi heq; omega
  have hunion_sU : Q0 ∪ Q1 ∪ R = s \ U := by
    ext x
    simp only [mem_union, mem_sdiff]
    constructor
    · rintro ((h0 | h1) | hR')
      · obtain ⟨i, hi, hilt, rfl⟩ := (hmem_Q0 x).mp h0
        exact ⟨hget_mem i hi, fun hxU => by have := hjmin_min i hi hxU; omega⟩
      · obtain ⟨i, hi, higt, rfl⟩ := (hmem_Q1 x).mp h1
        exact ⟨hget_mem i hi, fun hxU => by have := hjmax_max i hi hxU; omega⟩
      · obtain ⟨i, hi, _, _, hnotU, rfl⟩ := (hmem_R x).mp hR'
        exact ⟨hget_mem i hi, hnotU⟩
    · rintro ⟨hxs, hxnotU⟩
      obtain ⟨i, hi, rfl⟩ := hget_surj x hxs
      by_cases h1 : i < jmin
      · exact Or.inl (Or.inl ((hmem_Q0 _).mpr ⟨i, hi, h1, rfl⟩))
      · by_cases h2 : jmax < i
        · exact Or.inl (Or.inr ((hmem_Q1 _).mpr ⟨i, hi, h2, rfl⟩))
        · have hne1 : i ≠ jmin := fun h => hxnotU (h ▸ hjmin_U)
          have hne2 : i ≠ jmax := fun h => hxnotU (h ▸ hjmax_U)
          exact Or.inr ((hmem_R _).mpr ⟨i, hi, by omega, by omega, hxnotU, rfl⟩)
  have hcard_sum : Q0.card + Q1.card + R.card = (s \ U).card := by
    rw [← hunion_sU, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint hdisj_Q0Q1]
    exact Finset.disjoint_union_left.mpr ⟨hdisj_Q0R, hdisj_Q1R⟩
  obtain ⟨C0, hC0_sub, hC0_card, hC0_cov⟩ := exists_half_cover_of_colorable T col Q0
  obtain ⟨C1, hC1_sub, hC1_card, hC1_cov⟩ := exists_half_cover_of_colorable T col Q1
  obtain ⟨CR, hCR_sub, hCR_card, hCR_cov⟩ := exists_half_cover_of_colorable T col R
  obtain ⟨Cs, hCs⟩ : ∃ X, X = U ∪ C0 ∪ C1 ∪ CR := ⟨_, rfl⟩
  refine ⟨Cs, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hCs] at hx
    simp only [mem_union] at hx
    rcases hx with ((hxU | hx0) | hx1) | hxR
    · exact ((hU_def x).mp hxU).1
    · exact (mem_sdiff.mp (hunion_sU ▸ mem_union_left R (mem_union_left Q1 (hC0_sub hx0)))).1
    · exact (mem_sdiff.mp (hunion_sU ▸ mem_union_left R (mem_union_right Q0 (hC1_sub hx1)))).1
    · exact (mem_sdiff.mp (hunion_sU ▸ mem_union_right (Q0 ∪ Q1) (hCR_sub hxR))).1
  · intro x hxs hpos
    rw [hCs]
    exact mem_union_left CR (mem_union_left C1 (mem_union_left C0 ((hU_def x).mpr ⟨hxs, hpos⟩)))
  · intro x hxs y hys hadj
    rw [hCs]
    by_cases hxU : x ∈ U
    · exact Or.inl (mem_union_left CR (mem_union_left C1 (mem_union_left C0 hxU)))
    by_cases hyU : y ∈ U
    · exact Or.inr (mem_union_left CR (mem_union_left C1 (mem_union_left C0 hyU)))
    obtain ⟨i, hi, rfl⟩ := hget_surj x hxs
    obtain ⟨j, hj, rfl⟩ := hget_surj y hys
    have hij := (isAcyclic_adj_getVert_iff T hA hp (hL ▸ hi) (hL ▸ hj)).mp hadj
    have hi_ne_min : i ≠ jmin := fun h => hxU (h ▸ hjmin_U)
    have hi_ne_max : i ≠ jmax := fun h => hxU (h ▸ hjmax_U)
    have hj_ne_min : j ≠ jmin := fun h => hyU (h ▸ hjmin_U)
    have hj_ne_max : j ≠ jmax := fun h => hyU (h ▸ hjmax_U)
    by_cases hi0 : i < jmin
    · have hj0 : j < jmin := by omega
      rcases hC0_cov _ ((hmem_Q0 _).mpr ⟨i, hi, hi0, rfl⟩)
        _ ((hmem_Q0 _).mpr ⟨j, hj, hj0, rfl⟩) hadj with h | h
      · exact Or.inl (mem_union_left CR (mem_union_left C1 (mem_union_right U h)))
      · exact Or.inr (mem_union_left CR (mem_union_left C1 (mem_union_right U h)))
    · by_cases hi1 : jmax < i
      · have hj1 : jmax < j := by omega
        rcases hC1_cov _ ((hmem_Q1 _).mpr ⟨i, hi, hi1, rfl⟩)
          _ ((hmem_Q1 _).mpr ⟨j, hj, hj1, rfl⟩) hadj with h | h
        · exact Or.inl (mem_union_left CR (mem_union_right _ h))
        · exact Or.inr (mem_union_left CR (mem_union_right _ h))
      · have hiR : jmin < i ∧ i < jmax := by omega
        have hjR : jmin < j ∧ j < jmax := by omega
        rcases hCR_cov _ ((hmem_R _).mpr ⟨i, hi, hiR.1, hiR.2, hxU, rfl⟩)
          _ ((hmem_R _).mpr ⟨j, hj, hjR.1, hjR.2, hyU, rfl⟩) hadj with h | h
        · exact Or.inl (mem_union_right _ h)
        · exact Or.inr (mem_union_right _ h)
  · have hCs_le : Cs.card ≤ U.card + C0.card + C1.card + CR.card := by
      rw [hCs]
      calc (U ∪ C0 ∪ C1 ∪ CR).card ≤ (U ∪ C0 ∪ C1).card + CR.card := card_union_le _ _
        _ ≤ (U ∪ C0).card + C1.card + CR.card := by gcongr; exact card_union_le _ _
        _ ≤ U.card + C0.card + C1.card + CR.card := by gcongr; exact card_union_le _ _
    rw [← hU]
    omega

/-- Core additive tree inequality: for any finite tree `T` with `|V(T)| ≥ 2`,
any total dominating set `D`, and any path cover `P`,
`T.vertexCoverNum.toNat ≤ D.card + (P.card - 2)`. -/
theorem tree_vc_le_td_add_pc_sub_two (T : SimpleGraph α) (hT : T.IsTree)
    (hn : 2 ≤ Fintype.card α)
    (D : Finset α) (hD : T.IsTotalDominating (D : Set α))
    (P : Finset (Finset α)) (hP : T.IsPathCover P) :
    T.vertexCoverNum.toNat ≤ D.card + (P.card - 2) := by
  classical
  rcases hP with ⟨hP_disj, hP_cov, hP_paths⟩
  have h_exists_s : ∀ x : α, ∃ s ∈ P, x ∈ s := by
    intro x
    have hx := hP_cov (mem_univ x)
    rw [mem_biUnion] at hx
    exact hx
  have h_uniq_s : ∀ {s1 s2 : Finset α} {x : α}, s1 ∈ P → s2 ∈ P → x ∈ s1 → x ∈ s2 → s1 = s2 := by
    intro s1 s2 x h1 h2 hx1 hx2
    by_contra hne
    exact Finset.disjoint_left.mp (hP_disj s1 h1 s2 h2 hne) hx1 hx2
  have hP_sum_card : ∑ s ∈ P, s.card = Fintype.card α := by
    have huniv : P.biUnion id = Finset.univ :=
      Finset.Subset.antisymm (Finset.subset_univ _) hP_cov
    rw [← Finset.card_univ, ← huniv, Finset.card_biUnion]
    · rfl
    · intro s1 hs1 s2 hs2 hne
      exact hP_disj s1 hs1 s2 hs2 hne
  have hP_nonempty : ∀ s ∈ P, s.Nonempty := by
    intro s hs
    obtain ⟨u, v, p, _, rfl⟩ := hP_paths s hs
    exact ⟨u, List.mem_toFinset.mpr p.start_mem_support⟩
  have hP_pos : 1 ≤ P.card := by
    have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨v⟩ : Nonempty α := inferInstance
    obtain ⟨s, hs, _⟩ := h_exists_s v
    exact Finset.card_pos.mpr ⟨s, hs⟩
  obtain ⟨F, hF_adj⟩ : ∃ F : SimpleGraph α,
      ∀ x y, F.Adj x y ↔ T.Adj x y ∧ ∃ s ∈ P, x ∈ s ∧ y ∈ s :=
    ⟨{ Adj := fun x y => T.Adj x y ∧ ∃ s ∈ P, x ∈ s ∧ y ∈ s
       symm := ⟨fun _ _ h => ⟨h.1.symm, let ⟨s, hs, hx, hy⟩ := h.2; ⟨s, hs, hy, hx⟩⟩⟩
       loopless := ⟨fun x h => T.loopless.irrefl x h.1⟩ }, fun _ _ => Iff.rfl⟩
  obtain ⟨Gcross, hC_adj⟩ : ∃ Gc : SimpleGraph α,
      ∀ x y, Gc.Adj x y ↔ T.Adj x y ∧ ¬ F.Adj x y :=
    ⟨{ Adj := fun x y => T.Adj x y ∧ ¬ F.Adj x y
       symm := ⟨fun _ _ h => ⟨h.1.symm, fun hf => h.2 hf.symm⟩⟩
       loopless := ⟨fun x h => T.loopless.irrefl x h.1⟩ }, fun _ _ => Iff.rfl⟩
  have hF_le_T : F ≤ T := fun x y h => ((hF_adj x y).mp h).1
  have hC_le_T : Gcross ≤ T := fun x y h => ((hC_adj x y).mp h).1
  have hdeg_split : ∀ v : α, T.degree v = F.degree v + Gcross.degree v := by
    intro v
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
      ← card_neighborFinset_eq_degree]
    have hdisj : Disjoint (F.neighborFinset v) (Gcross.neighborFinset v) := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      rw [mem_neighborFinset] at h1 h2
      exact ((hC_adj v w).mp h2).2 h1
    have hunion : F.neighborFinset v ∪ Gcross.neighborFinset v = T.neighborFinset v := by
      ext w
      simp only [mem_union, mem_neighborFinset, hC_adj]
      exact ⟨fun h => h.elim (fun hf => hF_le_T hf) (fun hc => hc.1),
        fun ht => by by_cases hf : F.Adj v w; exact Or.inl hf; exact Or.inr ⟨ht, hf⟩⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hF_deg_le_two : ∀ x : α, F.degree x ≤ 2 := by
    intro x
    obtain ⟨s, hs, hxs⟩ := h_exists_s x
    obtain ⟨u, v, p, hp, hseq⟩ := hP_paths s hs
    have hxs' : x ∈ p.support := List.mem_toFinset.mp (hseq ▸ hxs)
    obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hxs'
    rw [← card_neighborFinset_eq_degree]
    let S2 : Finset α := {p.getVert (i - 1), p.getVert (i + 1)}
    have hsub : F.neighborFinset (p.getVert i) ⊆ S2 := by
      intro y hy
      rw [mem_neighborFinset, hF_adj] at hy
      rcases hy with ⟨hadj, s', hs', hx', hy'⟩
      have hs_eq : s' = s := h_uniq_s hs' hs hx' hxs
      subst hs_eq
      obtain ⟨j, rfl, hj⟩ := Walk.mem_support_iff_exists_getVert.mp
        (List.mem_toFinset.mp (hseq ▸ hy'))
      have hij := (isAcyclic_adj_getVert_iff T hT.isAcyclic hp hi hj).mp hadj
      simp only [S2, mem_insert, mem_singleton]
      rcases hij with rfl | hji
      · exact Or.inr rfl
      · left; congr 1; omega
    exact (card_le_card hsub).trans card_le_two
  have hF_edges : F.edgeFinset.card + P.card = Fintype.card α := by
    have h_edge_count : ∀ s ∈ P, (F.edgeFinset.filter (fun e => ∀ w ∈ e, w ∈ s)).card + 1 = s.card := by
      intro s hs
      obtain ⟨u, v, p, hp, rfl⟩ := hP_paths s hs
      have hset : F.edgeFinset.filter (fun e => ∀ w ∈ e, w ∈ p.support.toFinset) = p.edges.toFinset := by
        ext e
        induction e using Sym2.ind with
        | _ x y =>
          simp only [mem_filter, mem_edgeFinset, mem_edgeSet, hF_adj, List.mem_toFinset,
            Sym2.mem_iff, forall_eq_or_imp, forall_eq]
          constructor
          · rintro ⟨⟨hadj, _⟩, hx, hy⟩
            exact isAcyclic_mem_edges_of_adj T hT.isAcyclic hp hx hy hadj
          · intro hmem
            have hadj : T.Adj x y := p.adj_of_mem_edges hmem
            have hx : x ∈ p.support := Walk.fst_mem_support_of_mem_edges p hmem
            have hy : y ∈ p.support := Walk.snd_mem_support_of_mem_edges p hmem
            exact ⟨⟨hadj, p.support.toFinset, hs, List.mem_toFinset.mpr hx,
              List.mem_toFinset.mpr hy⟩, hx, hy⟩
      rw [hset, List.toFinset_card_of_nodup hp.isTrail.edges_nodup,
        List.toFinset_card_of_nodup hp.support_nodup, Walk.length_edges, Walk.length_support]
    have hpart : F.edgeFinset = P.biUnion (fun s => F.edgeFinset.filter (fun e => ∀ w ∈ e, w ∈ s)) := by
      ext e
      induction e using Sym2.ind with
      | _ x y =>
        simp only [mem_biUnion, mem_filter, mem_edgeFinset, mem_edgeSet, hF_adj, Sym2.mem_iff,
          forall_eq_or_imp, forall_eq]
        constructor
        · intro h; rcases h with ⟨hadj, s, hs, hx, hy⟩
          exact ⟨s, hs, ⟨hadj, s, hs, hx, hy⟩, hx, hy⟩
        · rintro ⟨_, _, h, _, _⟩; exact h
    have hdisj_e : Set.PairwiseDisjoint (P : Set (Finset α))
        (fun s => F.edgeFinset.filter (fun e => ∀ w ∈ e, w ∈ s)) := by
      intro s1 hs1 s2 hs2 hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro e h1 h2
      induction e using Sym2.ind with
      | _ x y =>
        simp only [mem_filter, Sym2.mem_iff, forall_eq_or_imp, forall_eq] at h1 h2
        exact hne (h_uniq_s hs1 hs2 h1.2.1 h2.2.1)
    have hcard_F : F.edgeFinset.card =
        ∑ s ∈ P, (F.edgeFinset.filter (fun e => ∀ w ∈ e, w ∈ s)).card := by
      conv_lhs => rw [hpart]
      exact Finset.card_biUnion hdisj_e
    have hsum : ∑ s ∈ P, ((F.edgeFinset.filter (fun e => ∀ w ∈ e, w ∈ s)).card + 1) =
        ∑ s ∈ P, s.card := Finset.sum_congr rfl h_edge_count
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, ← hcard_F, hP_sum_card] at hsum
    exact hsum
  have hC_edges : Gcross.edgeFinset.card = P.card - 1 := by
    have hdisj : Disjoint F.edgeFinset Gcross.edgeFinset := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      induction e using Sym2.ind with
      | _ x y =>
        simp only [mem_edgeFinset, mem_edgeSet, hC_adj] at h1 h2
        exact h2.2 h1
    have hunion : F.edgeFinset ∪ Gcross.edgeFinset = T.edgeFinset := by
      ext e
      induction e using Sym2.ind with
      | _ x y =>
        simp only [mem_union, mem_edgeFinset, mem_edgeSet, hC_adj]
        exact ⟨fun h => h.elim (fun hf => hF_le_T hf) (fun hc => hc.1),
          fun ht => by by_cases hf : F.Adj x y; exact Or.inl hf; exact Or.inr ⟨ht, hf⟩⟩
    have hT_edges : T.edgeFinset.card + 1 = Fintype.card α := hT.card_edgeFinset
    have hsum : F.edgeFinset.card + Gcross.edgeFinset.card = T.edgeFinset.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    omega
  have hsum_Cdeg : ∑ v : α, Gcross.degree v = 2 * (P.card - 1) := by
    rw [Gcross.sum_degrees_eq_twice_card_edges, hC_edges]
  have hdom_ge1 : ∀ v : α, 1 ≤ (T.neighborFinset v ∩ D).card := by
    intro v
    obtain ⟨w, hwD, hvw⟩ := hD v
    exact Finset.card_pos.mpr ⟨w, mem_inter.mpr ⟨(mem_neighborFinset T v w).mpr hvw, mem_coe.mp hwD⟩⟩
  have h_step1 : Fintype.card α ≤ ∑ v : α, (T.neighborFinset v ∩ D).card := by
    calc Fintype.card α = ∑ _v : α, 1 := by simp
      _ ≤ ∑ v : α, (T.neighborFinset v ∩ D).card := Finset.sum_le_sum (fun v _ => hdom_ge1 v)
  have h_swap : ∑ v : α, (T.neighborFinset v ∩ D).card = ∑ d ∈ D, T.degree d := by
    have hlhs : ∀ v : α, (T.neighborFinset v ∩ D).card = ∑ d ∈ D, if T.Adj v d then 1 else 0 := by
      intro v; rw [Finset.sum_boole, Nat.cast_id]
      congr 1; ext d; simp only [mem_inter, mem_filter, mem_neighborFinset]; tauto
    have hrhs : ∀ d ∈ D, T.degree d = ∑ v : α, if T.Adj v d then 1 else 0 := by
      intro d _; rw [← card_neighborFinset_eq_degree, Finset.sum_boole, Nat.cast_id]
      congr 1; ext v; simp only [mem_neighborFinset, mem_filter, mem_univ, true_and, adj_comm]
    calc ∑ v : α, (T.neighborFinset v ∩ D).card
        = ∑ v : α, ∑ d ∈ D, (if T.Adj v d then 1 else 0) := Finset.sum_congr rfl (fun v _ => hlhs v)
      _ = ∑ d ∈ D, ∑ v : α, (if T.Adj v d then 1 else 0) := Finset.sum_comm
      _ = ∑ d ∈ D, T.degree d := Finset.sum_congr rfl (fun d hd => (hrhs d hd).symm)
  have h_step2 : ∑ d ∈ D, T.degree d = (∑ d ∈ D, F.degree d) + (∑ d ∈ D, Gcross.degree d) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun d _ => hdeg_split d)
  have h_Fsum : ∑ d ∈ D, F.degree d ≤ 2 * D.card := by
    calc ∑ d ∈ D, F.degree d ≤ ∑ _d ∈ D, 2 := Finset.sum_le_sum (fun d _ => hF_deg_le_two d)
      _ = 2 * D.card := by simp [mul_comm]
  have h_Csum : ∑ d ∈ D, Gcross.degree d ≤ 2 * (P.card - 1) := by
    rw [← hsum_Cdeg]
    exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  obtain ⟨col⟩ := hT.colorable_two
  have hvc_half : T.vertexCoverNum.toNat ≤ Fintype.card α / 2 := by
    obtain ⟨C, _, hC2, hCcov⟩ := exists_half_cover_of_colorable T col Finset.univ
    have hCvc : T.IsVertexCover (C : Set α) := fun u v hadj => hCcov u (mem_univ u) v (mem_univ v) hadj
    have h1 := vertexCoverNum_toNat_le T C hCvc
    rw [Finset.card_univ] at hC2
    omega
  by_cases hP1 : P.card = 1
  · have hbound : Fintype.card α ≤ 2 * D.card := by omega
    omega
  have hP2 : 2 ≤ P.card := by omega
  by_cases hlt : Fintype.card α < 2 * D.card + 2 * (P.card - 1)
  · omega
  -- Sharp equality case
  have heq_step1 : ∑ v : α, 1 = ∑ v : α, (T.neighborFinset v ∩ D).card := by
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]; omega
  have heq_Fsum : ∑ d ∈ D, F.degree d = ∑ _d ∈ D, 2 := by
    simp only [Finset.sum_const, smul_eq_mul]; omega
  have heq_Csum : ∑ d ∈ D, Gcross.degree d = ∑ v : α, Gcross.degree v := by omega
  have huniq : ∀ v : α, (T.neighborFinset v ∩ D).card = 1 := by
    have h := (Finset.sum_eq_sum_iff_of_le (fun v _ => hdom_ge1 v)).mp heq_step1
    intro v; exact (h v (mem_univ v)).symm
  have hFdeg2 : ∀ d ∈ D, F.degree d = 2 := by
    have h := (Finset.sum_eq_sum_iff_of_le (fun d _ => hF_deg_le_two d)).mp heq_Fsum
    intro d hd; exact h d hd
  have hCzero : ∀ v : α, v ∉ D → Gcross.degree v = 0 := by
    have hcompl : ∑ v ∈ Dᶜ, Gcross.degree v = 0 := by
      have hadd := Finset.sum_add_sum_compl D (fun v => Gcross.degree v); omega
    intro v hv; exact (Finset.sum_eq_zero_iff.mp hcompl) v (mem_compl.mpr hv)
  have h_local : ∀ s ∈ P, ∃ Cs : Finset α, Cs ⊆ s ∧
      (∀ x ∈ s, 0 < Gcross.degree x → x ∈ Cs) ∧
      (∀ x ∈ s, ∀ y ∈ s, T.Adj x y → x ∈ Cs ∨ y ∈ Cs) ∧
      Cs.card + 1 ≤ (s ∩ D).card + (s.filter (fun x => 0 < Gcross.degree x)).card := by
    intro s hs
    obtain ⟨u, v, p, hp, hseq⟩ := hP_paths s hs
    have hU_ne : (s.filter (fun x => 0 < Gcross.degree x)).Nonempty := by
      obtain ⟨s', hs', hs_ne⟩ : ∃ s' ∈ P, s' ≠ s := by
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
        by_cases has : a = s
        · exact ⟨b, hb, fun h => hab (has.trans h.symm)⟩
        · exact ⟨a, ha, has⟩
      obtain ⟨x0, hx0⟩ := hP_nonempty s hs
      obtain ⟨y0, hy0⟩ := hP_nonempty s' hs'
      have hy0_not : y0 ∉ s := fun h => hs_ne (h_uniq_s hs' hs hy0 h)
      obtain ⟨w⟩ := hT.connected.preconnected x0 y0
      obtain ⟨d, _, hd1, hd2⟩ := w.exists_boundary_dart (s : Set α) (mem_coe.mpr hx0)
        (by simpa using hy0_not)
      have hnotF : ¬ F.Adj d.fst d.snd := by
        rw [hF_adj]
        rintro ⟨_, s'', hs'', h1, h2⟩
        exact hd2 (mem_coe.mpr ((h_uniq_s hs'' hs h1 (mem_coe.mp hd1)) ▸ h2))
      refine ⟨d.fst, mem_filter.mpr ⟨mem_coe.mp hd1, ?_⟩⟩
      rw [← card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨d.snd, (mem_neighborFinset _ _ _).mpr ((hC_adj _ _).mpr ⟨d.adj, hnotF⟩)⟩
    exact local_path_cover T F Gcross hT.isAcyclic col D s u v p hp hseq hF_le_T
      (fun hx hxy => let ⟨_, s', hs', hx', hy'⟩ := (hF_adj _ _).mp hxy; (h_uniq_s hs' hs hx' hx) ▸ hy')
      (fun hx hy => ⟨fun h => hF_le_T h, fun h => (hF_adj _ _).mpr ⟨h, s, hs, hx, hy⟩⟩)
      (hC_adj _ _) huniq hFdeg2 hCzero hU_ne
  choose! f hf_sub hf_U hf_cov hf_card using h_local
  let C : Finset α := P.biUnion f
  have hC_vc : T.IsVertexCover (C : Set α) := by
    intro x y hadj
    by_cases hFxy : F.Adj x y
    · rcases (hF_adj x y).mp hFxy with ⟨_, s, hs, hx, hy⟩
      rcases hf_cov s hs x hx y hy hadj with hxC | hyC
      · exact Or.inl (mem_coe.mpr (mem_biUnion.mpr ⟨s, hs, hxC⟩))
      · exact Or.inr (mem_coe.mpr (mem_biUnion.mpr ⟨s, hs, hyC⟩))
    · obtain ⟨s, hs, hxs⟩ := h_exists_s x
      have hx_pos : 0 < Gcross.degree x := by
        rw [← card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨y, (mem_neighborFinset _ _ _).mpr ((hC_adj x y).mpr ⟨hadj, hFxy⟩)⟩
      exact Or.inl (mem_coe.mpr (mem_biUnion.mpr ⟨s, hs, hf_U s hs x hxs hx_pos⟩))
  have hCdeg_le1 : ∀ x : α, Gcross.degree x ≤ 1 := by
    intro x
    rw [← card_neighborFinset_eq_degree]
    apply Finset.card_le_one.mpr
    intro y1 hy1 y2 hy2
    rw [mem_neighborFinset] at hy1 hy2
    have hD1 : y1 ∈ D := by
      by_contra h; have := hCzero y1 h
      have hpos : 0 < Gcross.degree y1 := by
        rw [← card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨x, (mem_neighborFinset _ _ _).mpr hy1.symm⟩
      omega
    have hD2 : y2 ∈ D := by
      by_contra h; have := hCzero y2 h
      have hpos : 0 < Gcross.degree y2 := by
        rw [← card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨x, (mem_neighborFinset _ _ _).mpr hy2.symm⟩
      omega
    exact Finset.card_le_one.mp (le_of_eq (huniq x))
      y1 (mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr (hC_le_T hy1), hD1⟩)
      y2 (mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr (hC_le_T hy2), hD2⟩)
  have hU_eq_sum : ∀ s ∈ P,
      (s.filter (fun x => 0 < Gcross.degree x)).card = ∑ x ∈ s, Gcross.degree x := by
    intro s _
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro x _
    have hle := hCdeg_le1 x
    split_ifs <;> omega
  have hsum_D : ∑ s ∈ P, (s ∩ D).card = D.card := by
    have hpartD : D = P.biUnion (fun s => s ∩ D) := by
      ext x; simp only [mem_biUnion, mem_inter]
      constructor
      · intro hxD; obtain ⟨s, hs, hxs⟩ := h_exists_s x; exact ⟨s, hs, hxs, hxD⟩
      · rintro ⟨_, _, _, hxD⟩; exact hxD
    have hdisjD : Set.PairwiseDisjoint (P : Set (Finset α)) (fun s => s ∩ D) :=
      fun s1 hs1 s2 hs2 hne => (hP_disj s1 hs1 s2 hs2 hne).mono inter_subset_left inter_subset_left
    conv_rhs => rw [hpartD]
    exact (Finset.card_biUnion hdisjD).symm
  have hsum_U : ∑ s ∈ P, (s.filter (fun x => 0 < Gcross.degree x)).card = 2 * (P.card - 1) := by
    rw [Finset.sum_congr rfl hU_eq_sum]
    have huniv : P.biUnion id = Finset.univ :=
      Finset.Subset.antisymm (Finset.subset_univ _) hP_cov
    have hbi := Finset.sum_biUnion (s := P) (t := id) (f := fun x => Gcross.degree x)
      (fun s1 hs1 s2 hs2 hne => hP_disj s1 hs1 s2 hs2 hne)
    rw [huniv] at hbi
    dsimp only [id] at hbi
    rw [← hbi]
    exact hsum_Cdeg
  have hC_card : C.card + P.card ≤ D.card + 2 * (P.card - 1) := by
    have h1 : C.card ≤ ∑ s ∈ P, (f s).card := Finset.card_biUnion_le
    have h2 : ∑ s ∈ P, ((f s).card + 1) ≤
        ∑ s ∈ P, ((s ∩ D).card + (s.filter (fun x => 0 < Gcross.degree x)).card) :=
      Finset.sum_le_sum (fun s hs => hf_card s hs)
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.sum_add_distrib, hsum_D, hsum_U] at h2
    omega
  have hvc := vertexCoverNum_toNat_le T C hC_vc
  omega

theorem main_conjecture372 (T : SimpleGraph α) (hT : T.IsTree) (hn : 2 < Fintype.card α)
    (hp : 2 ≤ T.pathCoverNumber) :
    (T.vertexCoverNum.toNat : ℝ) / ((T.pathCoverNumber : ℝ) - 1) ≤
      T.totalDominationNumber := by
  obtain ⟨D, hD, hDcard, hD2⟩ := exists_min_totalDom T hT (by omega)
  obtain ⟨P, hP, hPcard, _⟩ := exists_min_pathCover T (by omega)
  have hcore := tree_vc_le_td_add_pc_sub_two T hT (by omega) D hD P hP
  rw [hDcard, hPcard] at hcore
  have hgt2 : 2 ≤ T.totalDominationNumber := by omega
  have hmul : T.vertexCoverNum.toNat ≤ T.totalDominationNumber * (T.pathCoverNumber - 1) := by
    have h1 : T.totalDominationNumber + (T.pathCoverNumber - 2) ≤
        T.totalDominationNumber * (T.pathCoverNumber - 1) := by
      have hsub : T.pathCoverNumber - 1 = 1 + (T.pathCoverNumber - 2) := by omega
      rw [hsub, Nat.mul_add, Nat.mul_one]
      have : 1 * (T.pathCoverNumber - 2) ≤ T.totalDominationNumber * (T.pathCoverNumber - 2) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    omega
  have hdenom : (0 : ℝ) < (T.pathCoverNumber : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (T.pathCoverNumber : ℝ) := by exact_mod_cast hp
    linarith
  rw [div_le_iff₀ hdenom]
  have hmulR : (T.vertexCoverNum.toNat : ℝ) ≤
      (T.totalDominationNumber : ℝ) * ((T.pathCoverNumber - 1 : ℕ) : ℝ) := by exact_mod_cast hmul
  rw [Nat.cast_sub (by omega : 1 ≤ T.pathCoverNumber), Nat.cast_one] at hmulR
  exact hmulR

end OMAWowii372

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture372.conjecture372 := by
  intro α _ _ T hT hn hp
  exact OMAWowii372.main_conjecture372 T hT hn hp
