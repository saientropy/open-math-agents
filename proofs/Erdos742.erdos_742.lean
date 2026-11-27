import FormalConjectures.ErdosProblems.«742»

/-!
Proof of the Murty-Simon conjecture (`Erdos742.erdos_742`) for all finite graphs,
following the combinatorial maximal-matching and switch-exit method of Das and Fox (2026).
-/

namespace Erdos742Proof

open SimpleGraph Finset

section GraphHelpers

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For a finite simple graph `G` with edge set `G.edgeFinset` and non-edges
`nonEdges G`, `2 * (|E| + |F|) = n * (n - 1)`. -/
def nonEdges (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Sym2 V) :=
  Finset.univ.filter (fun p => ¬ p.IsDiag ∧ p ∉ G.edgeFinset)

omit [Fintype V] [DecidableEq V] in
lemma sym2_exists_eq (p : Sym2 V) : ∃ x y : V, p = s(x, y) := by
  induction p using Sym2.ind with
  | _ a b => exact ⟨a, b, rfl⟩

lemma mem_nonEdges {G : SimpleGraph V} [DecidableRel G.Adj] {p : Sym2 V} :
    p ∈ nonEdges G ↔ ¬ p.IsDiag ∧ p ∉ G.edgeFinset := by
  simp [nonEdges]

lemma s_mem_nonEdges {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} :
    s(u, v) ∈ nonEdges G ↔ u ≠ v ∧ ¬ G.Adj u v := by
  simp [nonEdges]

lemma disjoint_edgeFinset_nonEdges (G : SimpleGraph V) [DecidableRel G.Adj] :
    Disjoint G.edgeFinset (nonEdges G) := by
  rw [Finset.disjoint_left]
  intro p hp hne
  exact (mem_nonEdges.mp hne).2 hp

lemma two_mul_card_edges_add_nonEdges (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * (G.edgeFinset.card + (nonEdges G).card) = Fintype.card V * (Fintype.card V - 1) := by
  have hunion : G.edgeFinset ∪ nonEdges G = Finset.univ.filter (fun p : Sym2 V => ¬ p.IsDiag) := by
    ext p
    simp only [Finset.mem_union, mem_nonEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (he | ⟨hnd, _⟩)
      · exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he)
      · exact hnd
    · intro hnd
      by_cases he : p ∈ G.edgeFinset
      · exact Or.inl he
      · exact Or.inr ⟨hnd, he⟩
  have hsum : G.edgeFinset.card + (nonEdges G).card =
      (Finset.univ.filter (fun p : Sym2 V => ¬ p.IsDiag)).card := by
    rw [← Finset.card_union_of_disjoint (disjoint_edgeFinset_nonEdges G), hunion]
  rw [hsum]
  have hfib := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset V).offDiag)
    (t := Finset.univ.filter (fun p : Sym2 V => ¬ p.IsDiag))
    (f := fun q : V × V => s(q.1, q.2))
    (by
      intro q hq
      simp only [Finset.mem_coe, Finset.mem_offDiag, Finset.mem_univ, true_and] at hq
      exact Finset.mem_coe.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [Sym2.mk_isDiag_iff]; exact hq⟩))
  have htwo : ∀ p ∈ Finset.univ.filter (fun p : Sym2 V => ¬ p.IsDiag),
      ((Finset.univ : Finset V).offDiag.filter (fun q : V × V => s(q.1, q.2) = p)).card = 2 := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    induction p using Sym2.ind with
    | _ u v =>
      have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using hp
      have hset : (Finset.univ : Finset V).offDiag.filter (fun q : V × V => s(q.1, q.2) = s(u, v)) =
          {(u, v), (v, u)} := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
          Sym2.eq_iff, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        constructor
        · rintro ⟨_, h⟩; exact h
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact ⟨huv, Or.inl ⟨rfl, rfl⟩⟩
          · exact ⟨huv.symm, Or.inr ⟨rfl, rfl⟩⟩
      rw [hset, Finset.card_pair]
      intro h
      exact huv (Prod.mk.inj h).1
  rw [Finset.sum_congr rfl htwo, Finset.sum_const, smul_eq_mul, mul_comm] at hfib
  rw [← hfib, Finset.offDiag_card, Finset.card_univ, Nat.mul_sub_one]

/-- Common neighbors of the endpoints of a pair `f : Sym2 V`. -/
def commonNbrs (G : SimpleGraph V) [DecidableRel G.Adj] (f : Sym2 V) : Finset V :=
  Finset.univ.filter (fun w => ∀ x ∈ f, G.Adj x w)

lemma mem_commonNbrs {G : SimpleGraph V} [DecidableRel G.Adj] {u v w : V} :
    w ∈ commonNbrs G s(u, v) ↔ G.Adj u w ∧ G.Adj v w := by
  simp [commonNbrs, Sym2.mem_iff]

/-- Critical non-edges: non-edges with exactly one common neighbor. -/
def critNonEdges (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Sym2 V) :=
  (nonEdges G).filter (fun f => (commonNbrs G f).card = 1)

/-- Noncritical non-edges: non-edges with at least two common neighbors. -/
def nonCritNonEdges (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Sym2 V) :=
  (nonEdges G).filter (fun f => 2 ≤ (commonNbrs G f).card)

/-- Edge `e` lies on the critical 2-path of critical non-edge `f`. -/
def OnCritPath (G : SimpleGraph V) [DecidableRel G.Adj] (e f : Sym2 V) : Prop :=
  e ∈ G.edgeFinset ∧ f ∈ critNonEdges G ∧ ∃ w ∈ commonNbrs G f, ∃ x ∈ f, e = s(x, w)

omit [Fintype V] [DecidableEq V] in
lemma ediam_eq_two_of_diam_eq_two {G : SimpleGraph V} (hd : G.diam = 2) :
    G.ediam = 2 := by
  have hne : G.ediam ≠ ⊤ := G.ediam_ne_top_of_diam_ne_zero (by omega)
  have hcoe : (G.diam : ℕ∞) = G.ediam := ENat.natCast_toNat hne
  rw [← hcoe, hd]
  rfl

lemma commonNbrs_nonempty_of_nonEdge {G : SimpleGraph V} [DecidableRel G.Adj]
    (hd : G.diam = 2) {f : Sym2 V} (hf : f ∈ nonEdges G) :
    (commonNbrs G f).Nonempty := by
  induction f using Sym2.ind with
  | _ u v =>
    obtain ⟨huv, hnadj⟩ := s_mem_nonEdges.mp hf
    have hed : G.edist u v ≤ 2 :=
      G.edist_le_ediam.trans (le_of_eq (ediam_eq_two_of_diam_eq_two hd))
    have hgt : ¬ G.edist u v ≤ 1 := by
      rw [G.edist_le_one_iff_adj_or_eq]
      exact fun h => h.elim hnadj huv
    have heq : G.edist u v = 2 := by
      have h2 : (1 : ℕ∞) < G.edist u v := lt_of_not_ge hgt
      have hge : (2 : ℕ∞) ≤ G.edist u v := Order.add_one_le_of_lt h2
      exact le_antisymm hed hge
    obtain ⟨w, hw⟩ := (G.edist_eq_two_iff.mp heq).2.2
    rw [SimpleGraph.mem_commonNeighbors] at hw
    exact ⟨w, mem_commonNbrs.mpr hw⟩

lemma card_crit_add_nonCrit {G : SimpleGraph V} [DecidableRel G.Adj] (hd : G.diam = 2) :
    (critNonEdges G).card + (nonCritNonEdges G).card = (nonEdges G).card := by
  have hdisj : Disjoint (critNonEdges G) (nonCritNonEdges G) := by
    rw [Finset.disjoint_left]
    intro f h1 h2
    simp only [critNonEdges, nonCritNonEdges, Finset.mem_filter] at h1 h2
    omega
  have hunion : critNonEdges G ∪ nonCritNonEdges G = nonEdges G := by
    ext f
    simp only [Finset.mem_union, critNonEdges, nonCritNonEdges, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hf
      have hpos : 0 < (commonNbrs G f).card :=
        Finset.card_pos.mpr (commonNbrs_nonempty_of_nonEdge hd hf)
      by_cases h1 : (commonNbrs G f).card = 1
      · exact Or.inl ⟨hf, h1⟩
      · exact Or.inr ⟨hf, by omega⟩
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

/-- Lemma 2.2 (Das-Fox): Every edge in a triangle lies on a critical 2-path. -/
lemma lemma_2_2 {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcrit : Erdos742.IsDiameter2Critical G) {e : Sym2 V}
    (he : e ∈ G.edgeFinset) (htri : (commonNbrs G e).Nonempty) :
    ∃ f ∈ critNonEdges G, OnCritPath G e f := by
  by_contra hno
  push Not at hno
  set G' : SimpleGraph V := G.deleteEdges {e}
  have hed_le : ∀ a b : V, G'.edist a b ≤ 2 := by
    intro a b
    by_cases hab : a = b
    · subst hab; simp
    · by_cases hadj' : G'.Adj a b
      · exact le_trans (le_of_eq (G'.edist_eq_one_iff_adj.mpr hadj')) (by norm_num)
      · by_cases hs : s(a, b) = e
        · obtain ⟨z, hz⟩ := htri
          rw [← hs, mem_commonNbrs] at hz
          have hza : z ≠ a := (hz.1).ne.symm
          have hzb : z ≠ b := (hz.2).ne.symm
          have haz' : G'.Adj a z := by
            rw [SimpleGraph.deleteEdges_adj]
            refine ⟨hz.1, fun h => ?_⟩
            rw [Set.mem_singleton_iff, ← hs, Sym2.eq_iff] at h
            rcases h with ⟨_, hzb1⟩ | ⟨hab1, _⟩
            · exact hzb hzb1
            · exact hab hab1
          have hzb' : G'.Adj z b := by
            rw [SimpleGraph.deleteEdges_adj]
            refine ⟨hz.2.symm, fun h => ?_⟩
            rw [Set.mem_singleton_iff, ← hs, Sym2.eq_iff] at h
            rcases h with ⟨hza1, _⟩ | ⟨hzb1, _⟩
            · exact hza hza1
            · exact hzb hzb1
          have hw := SimpleGraph.Walk.edist_le (Walk.cons haz' (Walk.cons hzb' Walk.nil))
          simpa using hw
        · have hnadj : ¬ G.Adj a b := fun h =>
            hadj' (SimpleGraph.deleteEdges_adj.mpr ⟨h, by simpa using hs⟩)
          have hf : s(a, b) ∈ nonEdges G := s_mem_nonEdges.mpr ⟨hab, hnadj⟩
          by_cases hfc : s(a, b) ∈ critNonEdges G
          · obtain ⟨w, hw⟩ := commonNbrs_nonempty_of_nonEdge hcrit.1 hf
            have hnot : ¬ OnCritPath G e s(a, b) := hno s(a, b) hfc
            have hne1 : s(a, w) ≠ e := fun h => hnot ⟨he, hfc, w, hw, a, by simp, h.symm⟩
            have hne2 : s(w, b) ≠ e := fun h =>
              hnot ⟨he, hfc, w, hw, b, by simp, by rw [← h, Sym2.eq_swap]⟩
            have hw' := mem_commonNbrs.mp hw
            have haw' : G'.Adj a w :=
              SimpleGraph.deleteEdges_adj.mpr ⟨hw'.1, by simpa using hne1⟩
            have hwb' : G'.Adj w b :=
              SimpleGraph.deleteEdges_adj.mpr ⟨hw'.2.symm, by simpa using hne2⟩
            simpa using SimpleGraph.Walk.edist_le (Walk.cons haw' (Walk.cons hwb' Walk.nil))
          · have hpos : 0 < (commonNbrs G s(a, b)).card :=
              Finset.card_pos.mpr (commonNbrs_nonempty_of_nonEdge hcrit.1 hf)
            have hge2 : 1 < (commonNbrs G s(a, b)).card := by
              have hne1 : (commonNbrs G s(a, b)).card ≠ 1 := fun h =>
                hfc (Finset.mem_filter.mpr ⟨hf, h⟩)
              omega
            obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := Finset.one_lt_card.mp hge2
            have hok : ∀ w ∈ commonNbrs G s(a, b),
                s(a, w) ≠ e → s(w, b) ≠ e → G'.edist a b ≤ 2 := by
              intro w hw h1 h2
              have hw' := mem_commonNbrs.mp hw
              have haw' : G'.Adj a w :=
                SimpleGraph.deleteEdges_adj.mpr ⟨hw'.1, by simpa using h1⟩
              have hwb' : G'.Adj w b :=
                SimpleGraph.deleteEdges_adj.mpr ⟨hw'.2.symm, by simpa using h2⟩
              simpa using SimpleGraph.Walk.edist_le (Walk.cons haw' (Walk.cons hwb' Walk.nil))
            by_cases h1 : s(a, w₁) ≠ e ∧ s(w₁, b) ≠ e
            · exact hok w₁ hw₁ h1.1 h1.2
            · refine hok w₂ hw₂ ?_ ?_
              · intro heq2
                rw [not_and_or, not_not, not_not] at h1
                rcases h1 with heq1 | heq1
                · have h := heq1.trans heq2.symm
                  rw [Sym2.eq_iff] at h
                  rcases h with ⟨_, h⟩ | ⟨h, _⟩
                  · exact hne h
                  · exact (mem_commonNbrs.mp hw₂).1.ne h
                · have h := heq1.trans heq2.symm
                  rw [Sym2.eq_iff] at h
                  rcases h with ⟨h, _⟩ | ⟨_, h⟩
                  · exact (mem_commonNbrs.mp hw₁).1.ne h.symm
                  · exact hab h.symm
              · intro heq2
                rw [not_and_or, not_not, not_not] at h1
                rcases h1 with heq1 | heq1
                · have h := heq1.trans heq2.symm
                  rw [Sym2.eq_iff] at h
                  rcases h with ⟨h, _⟩ | ⟨h, _⟩
                  · exact (mem_commonNbrs.mp hw₂).1.ne h
                  · exact hab h
                · have h := heq1.trans heq2.symm
                  rw [Sym2.eq_iff] at h
                  rcases h with ⟨h, _⟩ | ⟨_, h⟩
                  · exact hne h
                  · exact (mem_commonNbrs.mp hw₂).2.ne h
  have hediam_le : G'.ediam ≤ 2 := SimpleGraph.ediam_le_of_edist_le hed_le
  have hediam_ge : (2 : ℕ∞) ≤ G'.ediam := by
    rw [← ediam_eq_two_of_diam_eq_two hcrit.1]
    exact SimpleGraph.ediam_anti (SimpleGraph.deleteEdges_le {e})
  have hediam_eq : G'.ediam = 2 := le_antisymm hediam_le hediam_ge
  have hdiam_eq : G'.diam = 2 := by
    rw [SimpleGraph.diam, hediam_eq]
    rfl
  exact hcrit.2 e (SimpleGraph.mem_edgeFinset.mp he) hdiam_eq

end GraphHelpers

section Matching

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsMatching (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Sym2 V)) : Prop :=
  M ⊆ G.edgeFinset ∧ ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ x : V, ¬ (x ∈ e₁ ∧ x ∈ e₂)

lemma exists_maximal_matching (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ M : Finset (Sym2 V), IsMatching G M ∧
      ∀ e ∈ G.edgeFinset, ∃ x ∈ e, ∃ m ∈ M, x ∈ m := by
  classical
  let S := G.edgeFinset.powerset.filter (IsMatching G)
  have hS : S.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
    exact ⟨Finset.empty_subset _, fun _ h => (Finset.notMem_empty _ h).elim⟩
  obtain ⟨M, hMS, hMmax⟩ := Finset.exists_max_image S Finset.card hS
  have hM : IsMatching G M := (Finset.mem_filter.mp hMS).2
  refine ⟨M, hM, ?_⟩
  intro e he
  by_contra hnone
  push Not at hnone
  have heM : e ∉ M := by
    intro hm
    induction e using Sym2.ind with
    | _ u v => exact hnone u (by simp) s(u, v) hm (by simp)
  have hM' : IsMatching G (insert e M) := by
    refine ⟨Finset.insert_subset he hM.1, ?_⟩
    intro e₁ he₁ e₂ he₂ hne x ⟨hx₁, hx₂⟩
    rcases Finset.mem_insert.mp he₁ with rfl | h1 <;>
      rcases Finset.mem_insert.mp he₂ with rfl | h2
    · exact hne rfl
    · exact hnone x hx₁ e₂ h2 hx₂
    · exact hnone x hx₂ e₁ h1 hx₁
    · exact hM.2 e₁ h1 e₂ h2 hne x ⟨hx₁, hx₂⟩
  have hM'S : insert e M ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hM'.1, hM'⟩
  have hle := hMmax (insert e M) hM'S
  rw [Finset.card_insert_of_notMem heM] at hle
  omega

/-- Vertices covered by matching `M`. -/
def matchedVerts (M : Finset (Sym2 V)) : Finset V :=
  Finset.univ.filter (fun x => ∃ m ∈ M, x ∈ m)

lemma two_mul_card_matching_le {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Sym2 V)} (hM : IsMatching G M) :
    2 * M.card ≤ Fintype.card V := by
  have hbi : matchedVerts M = M.biUnion (fun e => Finset.univ.filter (· ∈ e)) := by
    ext x
    simp [matchedVerts]
  have hdisj : (M : Set (Sym2 V)).PairwiseDisjoint (fun e => Finset.univ.filter (· ∈ e)) := by
    intro e₁ he₁ e₂ he₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx₁ hx₂
    exact hM.2 e₁ he₁ e₂ he₂ hne x
      ⟨(Finset.mem_filter.mp hx₁).2, (Finset.mem_filter.mp hx₂).2⟩
  have hcard2 : ∀ e ∈ M, (Finset.univ.filter (· ∈ e)).card = 2 := by
    intro e he
    have heG : e ∈ G.edgeFinset := hM.1 he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : u ≠ v := (SimpleGraph.mem_edgeFinset.mp heG).ne
      have hset : Finset.univ.filter (· ∈ s(u, v)) = {u, v} := by
        ext x
        simp [Sym2.mem_iff]
      rw [hset, Finset.card_pair huv]
  have hvm : (matchedVerts M).card = 2 * M.card := by
    rw [hbi, Finset.card_biUnion hdisj, Finset.sum_congr rfl hcard2,
      Finset.sum_const, smul_eq_mul, mul_comm]
  rw [← hvm]
  exact Finset.card_le_univ _

lemma exists_mate_of_mem_matchedVerts {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Sym2 V)} (_hM : IsMatching G M) {x : V} (hx : x ∈ matchedVerts M) :
    ∃ y : V, s(x, y) ∈ M := by
  obtain ⟨m, hmM, hxm⟩ := (Finset.mem_filter.mp hx).2
  induction m using Sym2.ind with
  | _ u v =>
    rw [Sym2.mem_iff] at hxm
    rcases hxm with rfl | rfl
    · exact ⟨v, hmM⟩
    · exact ⟨u, by rwa [Sym2.eq_swap]⟩

noncomputable def mate {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Sym2 V)} (hM : IsMatching G M) (x : V) : V :=
  open Classical in
  if hx : x ∈ matchedVerts M then
    Classical.choose (exists_mate_of_mem_matchedVerts hM hx)
  else x

lemma s_mate_mem {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Sym2 V)} (hM : IsMatching G M) {x : V} (hx : x ∈ matchedVerts M) :
    s(x, mate hM x) ∈ M := by
  classical
  simp only [mate, dif_pos hx]
  exact Classical.choose_spec (exists_mate_of_mem_matchedVerts hM hx)

lemma mate_eq_of_mem {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Sym2 V)} (hM : IsMatching G M) {x y : V} (hxy : s(x, y) ∈ M) :
    mate hM x = y := by
  have hx : x ∈ matchedVerts M := Finset.mem_filter.mpr ⟨Finset.mem_univ _, s(x, y), hxy, by simp⟩
  have hm : s(x, mate hM x) ∈ M := s_mate_mem hM hx
  have heq : s(x, mate hM x) = s(x, y) := by
    by_contra hne
    exact hM.2 _ hm _ hxy hne x ⟨by simp, by simp⟩
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨_, h⟩ | ⟨h1, h2⟩
  · exact h
  · exfalso
    have hadj : G.Adj x y := SimpleGraph.mem_edgeFinset.mp (hM.1 hxy)
    exact hadj.ne h1

lemma mate_mem_matchedVerts {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Sym2 V)} (hM : IsMatching G M) {x : V} (hx : x ∈ matchedVerts M) :
    mate hM x ∈ matchedVerts M :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, s(x, mate hM x), s_mate_mem hM hx, by simp⟩

lemma mate_mate {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Sym2 V)} (hM : IsMatching G M) {x : V} (hx : x ∈ matchedVerts M) :
    mate hM (mate hM x) = x := by
  apply mate_eq_of_mem hM
  rw [Sym2.eq_swap]
  exact s_mate_mem hM hx

lemma mate_adj {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Sym2 V)} (hM : IsMatching G M) {x : V} (hx : x ∈ matchedVerts M) :
    G.Adj x (mate hM x) :=
  SimpleGraph.mem_edgeFinset.mp (hM.1 (s_mate_mem hM hx))

lemma mate_ne {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Sym2 V)} (hM : IsMatching G M) {x : V} (hx : x ∈ matchedVerts M) :
    mate hM x ≠ x :=
  (mate_adj hM hx).ne.symm

end Matching

section BipartiteEdgeCount

/-- In a finite bipartite simple graph partitioned into `A` and `B`, the number of edges
equals the sum of degrees on `A`. -/
lemma card_edgeFinset_bipartite {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (A B : Finset W)
    (hdisj : Disjoint A B)
    (hbip : ∀ u v, H.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)) :
    H.edgeFinset.card = ∑ a ∈ A, (H.neighborFinset a).card := by
  let P : Finset (W × W) := (A ×ˢ B).filter (fun q => H.Adj q.1 q.2)
  have hP_card : P.card = ∑ a ∈ A, (H.neighborFinset a).card := by
    rw [Finset.card_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a ha
    have hsub : H.neighborFinset a ⊆ B := by
      intro b hb
      have hadj : H.Adj a b := (SimpleGraph.mem_neighborFinset H a b).mp hb
      rcases hbip a b hadj with ⟨_, hbB⟩ | ⟨haB, _⟩
      · exact hbB
      · exact (Finset.disjoint_left.mp hdisj ha haB).elim
    have hfilt : B.filter (fun b => H.Adj a b) = H.neighborFinset a := by
      ext b
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨fun h => h.2, fun h => ⟨hsub ((SimpleGraph.mem_neighborFinset H a b).mpr h), h⟩⟩
    rw [← Finset.card_filter, hfilt]
  rw [← hP_card]
  symm
  refine Finset.card_bij (fun q _ => s(q.1, q.2)) ?_ ?_ ?_
  · intro q hq
    simp only [P, Finset.mem_filter, Finset.mem_product] at hq
    exact SimpleGraph.mem_edgeFinset.mpr hq.2
  · intro q₁ hq₁ q₂ hq₂ heq
    simp only [P, Finset.mem_filter, Finset.mem_product] at hq₁ hq₂
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      exact Finset.disjoint_left.mp hdisj hq₁.1.1 (h1 ▸ hq₂.1.2)
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have hadj : H.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      rcases hbip u v hadj with ⟨huA, hvB⟩ | ⟨huB, hvA⟩
      · exact ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huA, hvB⟩, hadj⟩, rfl⟩
      · exact ⟨(v, u), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hvA, huB⟩, hadj.symm⟩,
          Sym2.eq_swap⟩

lemma induce_supp_connected {W : Type*} [DecidableEq W]
    (H : SimpleGraph W) (C : H.ConnectedComponent) :
    (H.induce C.supp).Connected := by
  have : Nonempty C.supp := C.nonempty_supp.to_subtype
  refine ⟨fun ⟨u, hu⟩ ⟨v, hv⟩ => ?_⟩
  have hreach : H.Reachable u v :=
    SimpleGraph.ConnectedComponent.exact (hu.trans hv.symm)
  obtain ⟨w⟩ := hreach
  have hmem : ∀ x ∈ w.support, x ∈ C.supp := by
    intro x hx
    have hrx : H.Reachable u x := (w.takeUntil x hx).reachable
    change H.connectedComponentMk x = C
    rw [← hu]
    exact SimpleGraph.ConnectedComponent.eq.mpr hrx.symm
  exact ⟨w.induce C.supp hmem⟩

end BipartiteEdgeCount

section MainProof

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Core Das-Fox bound (Lemma 1.2): for any maximal matching `M`, `|E \ M| ≤ |F|`. -/
lemma card_sdiff_matching_le_nonEdges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Erdos742.IsDiameter2Critical G)
    (M : Finset (Sym2 V)) (hM : IsMatching G M)
    (hMmax : ∀ e ∈ G.edgeFinset, ∃ x ∈ e, ∃ m ∈ M, x ∈ m) :
    (G.edgeFinset \ M).card ≤ (nonEdges G).card := by
  classical
  let E' : Finset (Sym2 V) := G.edgeFinset \ M
  let Fc : Finset (Sym2 V) := critNonEdges G
  let Fnc : Finset (Sym2 V) := nonCritNonEdges G
  let U : Finset (Sym2 V) := E' ∪ Fc
  have hDisjEF : Disjoint E' Fc := by
    rw [Finset.disjoint_left]
    intro p hpE hpF
    exact Finset.disjoint_left.mp (disjoint_edgeFinset_nonEdges G)
      (Finset.mem_sdiff.mp hpE).1 (Finset.mem_filter.mp hpF).1
  -- Auxiliary bipartite graph `I'` on `U = E' ∪ Fc`.
  let I' : SimpleGraph {p : Sym2 V // p ∈ U} :=
    { Adj := fun p q =>
        (p.1 ∈ E' ∧ q.1 ∈ Fc ∧ OnCritPath G p.1 q.1) ∨
        (q.1 ∈ E' ∧ p.1 ∈ Fc ∧ OnCritPath G q.1 p.1)
      symm := ⟨fun _ _ h => h.symm⟩
      loopless := ⟨fun _ h => by
        rcases h with ⟨hpE, hpF, _⟩ | ⟨hpE, hpF, _⟩
        · exact Finset.disjoint_left.mp hDisjEF hpE hpF
        · exact Finset.disjoint_left.mp hDisjEF hpE hpF⟩ }
  -- Component vertex sets, left/right parts, and left-lopsided predicate.
  let compV : I'.ConnectedComponent → Finset {p : Sym2 V // p ∈ U} :=
    fun C => Finset.univ.filter (fun v => I'.connectedComponentMk v = C)
  let L : I'.ConnectedComponent → Finset {p : Sym2 V // p ∈ U} :=
    fun C => (compV C).filter (fun v => v.1 ∈ E')
  let R : I'.ConnectedComponent → Finset {p : Sym2 V // p ∈ U} :=
    fun C => (compV C).filter (fun v => v.1 ∈ Fc)
  let IsLL : I'.ConnectedComponent → Prop := fun C => (R C).card < (L C).card
  -- Every vertex of `U` is in `E'` or `Fc` (disjointly).
  have hcomp_card : ∀ C, (compV C).card = (L C).card + (R C).card := by
    intro C
    have hdisj : Disjoint (L C) (R C) := by
      rw [Finset.disjoint_left]
      intro v h1 h2
      exact Finset.disjoint_left.mp hDisjEF
        (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    have hunion : L C ∪ R C = compV C := by
      ext v
      simp only [L, R, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro hv
        rcases Finset.mem_union.mp v.2 with hE | hF
        · exact Or.inl ⟨hv, hE⟩
        · exact Or.inr ⟨hv, hF⟩
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  -- Every right vertex `r` has degree at most 2 in `I'`.
  have hdegR_le : ∀ r : {p : Sym2 V // p ∈ U}, r.1 ∈ Fc → (I'.neighborFinset r).card ≤ 2 := by
    intro r hrF
    obtain ⟨hrNE, hcard1⟩ := Finset.mem_filter.mp hrF
    obtain ⟨w, hw_eq⟩ := Finset.card_eq_one.mp hcard1
    rcases sym2_exists_eq r.1 with ⟨x, y, hxy⟩
    have hsub : (I'.neighborFinset r).image Subtype.val ⊆ {s(x, w), s(y, w)} := by
      intro e he
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp he
      have hadj : I'.Adj r l := (SimpleGraph.mem_neighborFinset I' r l).mp hl
      have hon : OnCritPath G l.1 r.1 := by
        rcases hadj with ⟨hrE, _, _⟩ | ⟨_, _, hon⟩
        · exact (Finset.disjoint_left.mp hDisjEF hrE hrF).elim
        · exact hon
      obtain ⟨_, _, w', hw', z, hz, hl_eq⟩ := hon
      have hw'w : w' = w := by
        rw [hw_eq, Finset.mem_singleton] at hw'
        exact hw'
      subst hw'w
      rw [hxy, Sym2.mem_iff] at hz
      rcases hz with rfl | rfl <;> simp [hl_eq]
    have hcard_img : ((I'.neighborFinset r).image Subtype.val).card = (I'.neighborFinset r).card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    calc (I'.neighborFinset r).card
        = ((I'.neighborFinset r).image Subtype.val).card := hcard_img.symm
      _ ≤ ({s(x, w), s(y, w)} : Finset (Sym2 V)).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  -- Helper: edge count of induced component equals sum of degrees on `R C` and on `L C`.
  have hcomp_edges : ∀ C : I'.ConnectedComponent,
      (compV C).card ≤ ∑ r ∈ R C, (I'.neighborFinset r).card + 1 ∧
      ∑ l ∈ L C, (I'.neighborFinset l).card = ∑ r ∈ R C, (I'.neighborFinset r).card := by
    intro C
    let HC := I'.induce C.supp
    have hconn : HC.Connected := induce_supp_connected I' C
    have hcard_le := hconn.card_vert_le_card_edgeSet_add_one
    have hsupp_card : Nat.card C.supp = (compV C).card := by
      rw [Nat.card_eq_fintype_card]
      have hsub : (Finset.univ : Finset C.supp).card = (compV C).card := by
        refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
        · intro x _
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩
        · intro x₁ _ x₂ _ h
          exact Subtype.ext h
        · intro v hv
          exact ⟨⟨v, (Finset.mem_filter.mp hv).2⟩, Finset.mem_univ _, rfl⟩
      simpa using hsub
    have hedge_card : Nat.card HC.edgeSet = HC.edgeFinset.card := by
      rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    let LA : Finset C.supp := Finset.univ.filter (fun v => v.1.1 ∈ E')
    let RB : Finset C.supp := Finset.univ.filter (fun v => v.1.1 ∈ Fc)
    have hdisjAB : Disjoint LA RB := by
      rw [Finset.disjoint_left]
      intro v h1 h2
      exact Finset.disjoint_left.mp hDisjEF
        (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    have hbipLR : ∀ u v : C.supp, HC.Adj u v → (u ∈ LA ∧ v ∈ RB) ∨ (u ∈ RB ∧ v ∈ LA) := by
      intro u v huv
      rcases huv with ⟨huE, hvF, _⟩ | ⟨hvE, huF, _⟩
      · exact Or.inl ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huE⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvF⟩⟩
      · exact Or.inr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huF⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvE⟩⟩
    have hbipRL : ∀ u v : C.supp, HC.Adj u v → (u ∈ RB ∧ v ∈ LA) ∨ (u ∈ LA ∧ v ∈ RB) :=
      fun u v h => (hbipLR u v h).symm
    have hdeg_eq : ∀ v : C.supp, (HC.neighborFinset v).card = (I'.neighborFinset v.1).card := by
      intro v
      refine Finset.card_bij (fun w _ => w.1) ?_ ?_ ?_
      · intro w hw
        exact (SimpleGraph.mem_neighborFinset I' v.1 w.1).mpr
          ((SimpleGraph.mem_neighborFinset HC v w).mp hw)
      · intro w₁ _ w₂ _ h
        exact Subtype.ext h
      · intro u hu
        have hadj : I'.Adj v.1 u := (SimpleGraph.mem_neighborFinset I' v.1 u).mp hu
        have huC : u ∈ C.supp := by
          change I'.connectedComponentMk u = C
          rw [← v.2]
          exact SimpleGraph.ConnectedComponent.eq.mpr hadj.symm.reachable
        exact ⟨⟨u, huC⟩, (SimpleGraph.mem_neighborFinset HC v ⟨u, huC⟩).mpr hadj, rfl⟩
    have hsumR : ∑ r ∈ RB, (HC.neighborFinset r).card = ∑ r ∈ R C, (I'.neighborFinset r).card := by
      refine Finset.sum_bij (fun r _ => r.1) ?_ ?_ ?_ ?_
      · intro r hr
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.2⟩,
          (Finset.mem_filter.mp hr).2⟩
      · intro r₁ _ r₂ _ h
        exact Subtype.ext h
      · intro r hr
        obtain ⟨hrC, hrF⟩ := Finset.mem_filter.mp hr
        have hrmem : r ∈ C.supp := (Finset.mem_filter.mp hrC).2
        exact ⟨⟨r, hrmem⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrF⟩, rfl⟩
      · intro r _
        exact hdeg_eq r
    have hsumL : ∑ l ∈ LA, (HC.neighborFinset l).card = ∑ l ∈ L C, (I'.neighborFinset l).card := by
      refine Finset.sum_bij (fun l _ => l.1) ?_ ?_ ?_ ?_
      · intro l hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, l.2⟩,
          (Finset.mem_filter.mp hl).2⟩
      · intro l₁ _ l₂ _ h
        exact Subtype.ext h
      · intro l hl
        obtain ⟨hlC, hlE⟩ := Finset.mem_filter.mp hl
        have hlmem : l ∈ C.supp := (Finset.mem_filter.mp hlC).2
        exact ⟨⟨l, hlmem⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlE⟩, rfl⟩
      · intro l _
        exact hdeg_eq l
    have hE_eq_R : HC.edgeFinset.card = ∑ r ∈ R C, (I'.neighborFinset r).card := by
      rw [card_edgeFinset_bipartite HC RB LA hdisjAB.symm hbipRL]
      rw [← hsumR]
      refine Finset.sum_congr rfl fun r _ => congrArg Finset.card (by ext w; simp)
    have hE_eq_L : HC.edgeFinset.card = ∑ l ∈ L C, (I'.neighborFinset l).card := by
      rw [card_edgeFinset_bipartite HC LA RB hdisjAB hbipLR]
      rw [← hsumL]
      refine Finset.sum_congr rfl fun l _ => congrArg Finset.card (by ext w; simp)
    rw [hsupp_card, hedge_card, hE_eq_R] at hcard_le
    exact ⟨hcard_le, hE_eq_L.symm.trans hE_eq_R⟩
  -- Lemma 2.4 consequences:
  -- (a) `|L C| ≤ |R C| + 1` for every component `C`.
  have hL_le : ∀ C, (L C).card ≤ (R C).card + 1 := by
    intro C
    have h1 := (hcomp_edges C).1
    rw [hcomp_card C] at h1
    have h2 : ∑ r ∈ R C, (I'.neighborFinset r).card ≤ 2 * (R C).card := by
      calc ∑ r ∈ R C, (I'.neighborFinset r).card
          ≤ ∑ _r ∈ R C, 2 := Finset.sum_le_sum (fun r hr => hdegR_le r (Finset.mem_filter.mp hr).2)
        _ = 2 * (R C).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    omega
  -- (b) In a left-lopsided component `C`, `|L C| = |R C| + 1` and every `r ∈ R C` has degree 2.
  have hLL_degR : ∀ C, IsLL C →
      (L C).card = (R C).card + 1 ∧
      ∀ r ∈ R C, (I'.neighborFinset r).card = 2 := by
    intro C hLL
    have hle := hL_le C
    have heq : (L C).card = (R C).card + 1 := by dsimp [IsLL] at hLL; omega
    have h1 := (hcomp_edges C).1
    rw [hcomp_card C, heq] at h1
    have hsum_ge : 2 * (R C).card ≤ ∑ r ∈ R C, (I'.neighborFinset r).card := by omega
    have hsum_le : ∑ r ∈ R C, (I'.neighborFinset r).card ≤ ∑ _r ∈ R C, 2 :=
      Finset.sum_le_sum (fun r hr => hdegR_le r (Finset.mem_filter.mp hr).2)
    have hsum_eq : ∑ r ∈ R C, (I'.neighborFinset r).card = ∑ _r ∈ R C, 2 := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm] at hsum_le ⊢
      omega
    refine ⟨heq, fun r hr => ?_⟩
    by_contra hne
    have hlt : (I'.neighborFinset r).card < 2 :=
      lt_of_le_of_ne (hdegR_le r (Finset.mem_filter.mp hr).2) hne
    have hstrict : ∑ r' ∈ R C, (I'.neighborFinset r').card < ∑ _r' ∈ R C, 2 :=
      Finset.sum_lt_sum (fun r' hr' => hdegR_le r' (Finset.mem_filter.mp hr').2) ⟨r, hr, hlt⟩
    omega
  -- (c) In a left-lopsided component with `|L C| ≥ 2`, there are at least 2 leaves in `L C`.
  have hLL_two_leaves : ∀ C, IsLL C → 2 ≤ (L C).card →
      ∃ e₁ ∈ L C, ∃ e₂ ∈ L C, e₁ ≠ e₂ ∧
        (I'.neighborFinset e₁).card = 1 ∧ (I'.neighborFinset e₂).card = 1 := by
    intro C hLL hge2
    have ⟨heqLR, hdeg2⟩ := hLL_degR C hLL
    have hsumL : ∑ l ∈ L C, (I'.neighborFinset l).card = 2 * (R C).card := by
      rw [(hcomp_edges C).2, Finset.sum_congr rfl hdeg2, Finset.sum_const, smul_eq_mul, mul_comm]
    have hdeg_pos : ∀ l ∈ L C, 1 ≤ (I'.neighborFinset l).card := by
      intro l hl
      have hRpos : 0 < (R C).card := by omega
      obtain ⟨r, hr⟩ := Finset.card_pos.mp hRpos
      have hlC : I'.connectedComponentMk l = C :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2
      have hrC : I'.connectedComponentMk r = C :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
      have hne : l ≠ r := fun h =>
        Finset.disjoint_left.mp hDisjEF (Finset.mem_filter.mp hl).2
          (h ▸ (Finset.mem_filter.mp hr).2)
      obtain ⟨w⟩ := SimpleGraph.ConnectedComponent.exact (hlC.trans hrC.symm)
      cases w with
      | nil => exact (hne rfl).elim
      | cons hadj _ =>
        exact Finset.card_pos.mpr ⟨_, (SimpleGraph.mem_neighborFinset I' l _).mpr hadj⟩
    let A := (L C).filter (fun l => (I'.neighborFinset l).card = 1)
    let B := (L C).filter (fun l => (I'.neighborFinset l).card ≠ 1)
    have hAB_card : A.card + B.card = (L C).card := by
      have hdisjAB' : Disjoint A B := by
        rw [Finset.disjoint_left]
        intro l h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hunionAB' : A ∪ B = L C := by
        ext l
        simp only [A, B, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro hl
          by_cases h1 : (I'.neighborFinset l).card = 1
          · exact Or.inl ⟨hl, h1⟩
          · exact Or.inr ⟨hl, h1⟩
      rw [← Finset.card_union_of_disjoint hdisjAB', hunionAB']
    have hsum_split : ∑ l ∈ L C, (I'.neighborFinset l).card =
        ∑ l ∈ A, (I'.neighborFinset l).card + ∑ l ∈ B, (I'.neighborFinset l).card :=
      (Finset.sum_filter_add_sum_filter_not (L C) (fun l => (I'.neighborFinset l).card = 1) _).symm
    have hA_sum : ∑ l ∈ A, (I'.neighborFinset l).card = A.card := by
      rw [Finset.sum_congr rfl (fun l hl => (Finset.mem_filter.mp hl).2),
        Finset.sum_const, smul_eq_mul, mul_one]
    have hB_sum : 2 * B.card ≤ ∑ l ∈ B, (I'.neighborFinset l).card := by
      calc 2 * B.card
          = ∑ _l ∈ B, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ l ∈ B, (I'.neighborFinset l).card := Finset.sum_le_sum (fun l hl => by
            have h1 := hdeg_pos l (Finset.mem_filter.mp hl).1
            have h2 := (Finset.mem_filter.mp hl).2
            omega)
    have hAge2 : 1 < A.card := by omega
    obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := Finset.one_lt_card.mp hAge2
    exact ⟨e₁, (Finset.mem_filter.mp he₁).1, e₂, (Finset.mem_filter.mp he₂).1, hne,
      (Finset.mem_filter.mp he₁).2, (Finset.mem_filter.mp he₂).2⟩
  -- Switch exit definitions.
  let IsSwitchExit : I'.ConnectedComponent → V → V → Prop := fun C p q =>
    s(p, q) ∈ Fnc ∧ p ∈ matchedVerts M ∧
      ∃ h : s(mate hM p, q) ∈ U, I'.connectedComponentMk ⟨s(mate hM p, q), h⟩ = C
  let IsSafeSwitchExit : I'.ConnectedComponent → V → V → Prop := fun C p q =>
    IsSwitchExit C p q ∧ q ∉ matchedVerts M
  -- Lemma 2.9: switching an edge in a left-lopsided component to a non-edge yields a noncritical non-edge.
  have lemma_2_9 : ∀ (C : I'.ConnectedComponent), IsLL C → ∀ (p q : V),
      s(p, q) ∈ nonEdges G → p ∈ matchedVerts M →
      (∃ h : s(mate hM p, q) ∈ U, s(mate hM p, q) ∈ E' ∧
        I'.connectedComponentMk ⟨s(mate hM p, q), h⟩ = C) →
      IsSwitchExit C p q := by
    intro C hLL p q hpq hpM ⟨hU, hE', hC⟩
    refine ⟨?_, hpM, hU, hC⟩
    have hpos : 0 < (commonNbrs G s(p, q)).card :=
      Finset.card_pos.mpr (commonNbrs_nonempty_of_nonEdge hcrit.1 hpq)
    suffices hne1 : (commonNbrs G s(p, q)).card ≠ 1 by
      exact Finset.mem_filter.mpr ⟨hpq, by omega⟩
    intro hcard1
    have hfc : s(p, q) ∈ Fc := Finset.mem_filter.mpr ⟨hpq, hcard1⟩
    have hfcU : s(p, q) ∈ U := Finset.mem_union_right _ hfc
    have hpm_adj : G.Adj p (mate hM p) := mate_adj hM hpM
    have hmq_adj : G.Adj (mate hM p) q :=
      SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hE').1
    have hmp_cn : mate hM p ∈ commonNbrs G s(p, q) :=
      mem_commonNbrs.mpr ⟨hpm_adj, hmq_adj.symm⟩
    have hon : OnCritPath G s(mate hM p, q) s(p, q) :=
      ⟨(Finset.mem_sdiff.mp hE').1, hfc, mate hM p, hmp_cn, q, by simp, Sym2.eq_swap⟩
    have hadjI : I'.Adj ⟨s(mate hM p, q), hU⟩ ⟨s(p, q), hfcU⟩ :=
      Or.inl ⟨hE', hfc, hon⟩
    have hfcC : I'.connectedComponentMk ⟨s(p, q), hfcU⟩ = C := by
      rw [← hC]
      exact SimpleGraph.ConnectedComponent.eq.mpr hadjI.symm.reachable
    have hfcR : ⟨s(p, q), hfcU⟩ ∈ R C :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfcC⟩, hfc⟩
    have hdeg2 : (I'.neighborFinset ⟨s(p, q), hfcU⟩).card = 2 :=
      (hLL_degR C hLL).2 _ hfcR
    -- Every neighbor of `s(p, q)` in `I'` must be `s(mate hM p, q)` since `s(p, mate hM p) ∈ M`.
    have hcn_eq : commonNbrs G s(p, q) = {mate hM p} := by
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
      have : mate hM p = w := by rw [hw, Finset.mem_singleton] at hmp_cn; exact hmp_cn
      rw [hw, this]
    have hsub1 : (I'.neighborFinset ⟨s(p, q), hfcU⟩).image Subtype.val ⊆ {s(mate hM p, q)} := by
      intro e he
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp he
      have hadj' : I'.Adj ⟨s(p, q), hfcU⟩ l :=
        (SimpleGraph.mem_neighborFinset I' _ l).mp hl
      have hlE' : l.1 ∈ E' := by
        rcases hadj' with ⟨hF_in_E, _, _⟩ | ⟨hlE', _, _⟩
        · exact (Finset.disjoint_left.mp hDisjEF hF_in_E hfc).elim
        · exact hlE'
      have hon' : OnCritPath G l.1 s(p, q) := by
        rcases hadj' with ⟨hF_in_E, _, _⟩ | ⟨_, _, hon'⟩
        · exact (Finset.disjoint_left.mp hDisjEF hF_in_E hfc).elim
        · exact hon'
      obtain ⟨_, _, w', hw', z, hz, hl_eq⟩ := hon'
      rw [hcn_eq, Finset.mem_singleton] at hw'
      subst hw'
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exfalso
        exact (Finset.mem_sdiff.mp hlE').2 (hl_eq ▸ s_mate_mem hM hpM)
      · rw [Finset.mem_singleton, hl_eq, Sym2.eq_swap]
    have hcard_img : ((I'.neighborFinset ⟨s(p, q), hfcU⟩).image Subtype.val).card = 2 := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective, hdeg2]
    have hle1 : 2 ≤ 1 := by
      calc 2 = ((I'.neighborFinset ⟨s(p, q), hfcU⟩).image Subtype.val).card := hcard_img.symm
        _ ≤ ({s(mate hM p, q)} : Finset (Sym2 V)).card := Finset.card_le_card hsub1
        _ = 1 := Finset.card_singleton _
    omega
  -- Lemma 2.10: singleton left-lopsided component has a safe switch exit or two switch exits.
  have lemma_2_10 : ∀ C, IsLL C → (L C).card = 1 →
      (∃ p q, IsSafeSwitchExit C p q) ∨
      (∃ a b : V × V, a ≠ b ∧ IsSwitchExit C a.1 a.2 ∧ IsSwitchExit C b.1 b.2) := by
    intro C hLL hL1
    have hR0 : (R C).card = 0 := by
      have := (hLL_degR C hLL).1
      omega
    obtain ⟨e, he_eq⟩ := Finset.card_eq_one.mp hL1
    have heL : e ∈ L C := by rw [he_eq]; simp
    have heC : I'.connectedComponentMk e = C :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp heL).1).2
    have heE' : e.1 ∈ E' := (Finset.mem_filter.mp heL).2
    have heG : e.1 ∈ G.edgeFinset := (Finset.mem_sdiff.mp heE').1
    have heNotM : e.1 ∉ M := (Finset.mem_sdiff.mp heE').2
    -- `e` lies on no critical 2-path, hence in no triangle (by Lemma 2.2).
    have hnotri : ¬ (commonNbrs G e.1).Nonempty := by
      intro htri
      obtain ⟨f, hfFc, hon⟩ := lemma_2_2 hcrit heG htri
      have hfU : f ∈ U := Finset.mem_union_right _ hfFc
      have hadj : I'.Adj e ⟨f, hfU⟩ := Or.inl ⟨heE', hfFc, hon⟩
      have hfC : I'.connectedComponentMk ⟨f, hfU⟩ = C := by
        rw [← heC]
        exact SimpleGraph.ConnectedComponent.eq.mpr hadj.symm.reachable
      have hfR : ⟨f, hfU⟩ ∈ R C :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfC⟩, hfFc⟩
      have hpos : 0 < (R C).card := Finset.card_pos.mpr ⟨_, hfR⟩
      omega
    rcases sym2_exists_eq e.1 with ⟨u, v, huv_eq⟩
    have huv_adj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (huv_eq ▸ heG)
    have hmk_exit : ∀ a b : V, s(a, b) = e.1 → a ∈ matchedVerts M →
        IsSwitchExit C (mate hM a) b := by
      intro a b hab haM
      have hab_adj : G.Adj a b := SimpleGraph.mem_edgeFinset.mp (hab ▸ heG)
      have hne : mate hM a ≠ b := by
        intro h
        exact heNotM (hab ▸ h ▸ s_mate_mem hM haM)
      have hnadj : ¬ G.Adj (mate hM a) b := by
        intro h
        apply hnotri
        refine ⟨mate hM a, ?_⟩
        rw [← hab, mem_commonNbrs]
        exact ⟨mate_adj hM haM, h.symm⟩
      have hne_mem : s(mate hM a, b) ∈ nonEdges G := s_mem_nonEdges.mpr ⟨hne, hnadj⟩
      have hmaM : mate hM a ∈ matchedVerts M := mate_mem_matchedVerts hM haM
      apply lemma_2_9 C hLL (mate hM a) b hne_mem hmaM
      rw [mate_mate hM haM]
      refine ⟨hab ▸ e.2, hab ▸ heE', ?_⟩
      have hsub : (⟨s(a, b), hab ▸ e.2⟩ : {p : Sym2 V // p ∈ U}) = e := Subtype.ext hab
      rw [hsub]
      exact heC
    -- By maximality of `M`, at least one of `u, v` is in `matchedVerts M`.
    have hor : u ∈ matchedVerts M ∨ v ∈ matchedVerts M := by
      obtain ⟨x, hx, m, hmM, hxm⟩ := hMmax e.1 heG
      rw [huv_eq, Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, m, hmM, hxm⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, m, hmM, hxm⟩)
    by_cases hu : u ∈ matchedVerts M
    · by_cases hv : v ∈ matchedVerts M
      · refine Or.inr ⟨(mate hM u, v), (mate hM v, u), ?_,
          hmk_exit u v huv_eq.symm hu,
          hmk_exit v u (by rw [Sym2.eq_swap, huv_eq]) hv⟩
        intro h
        exact huv_adj.ne (Prod.mk.inj h).2.symm
      · exact Or.inl ⟨mate hM u, v, hmk_exit u v huv_eq.symm hu, hv⟩
    · have hv : v ∈ matchedVerts M := hor.resolve_left hu
      exact Or.inl ⟨mate hM v, u, hmk_exit v u (by rw [Sym2.eq_swap, huv_eq]) hv, hu⟩
  -- Helper for Lemma 2.11: analyze a single leaf `e` of `C`.
  have leaf_analysis : ∀ C, IsLL C →
      ∀ e ∈ L C, (I'.neighborFinset e).card = 1 →
        ((∃ p q, IsSafeSwitchExit C p q) ∨
         (∃ a b : V × V, a ≠ b ∧ IsSwitchExit C a.1 a.2 ∧ IsSwitchExit C b.1 b.2)) ∨
        ∃ p q : V, IsSwitchExit C p q ∧
          (s(mate hM p, q) = e.1 ∨
           (∃ f ∈ R C, s(mate hM p, q) = f.1 ∧
             ∃ u ∈ commonNbrs G f.1, e.1 = s(u, q))) := by
    intro C hLL e heL hdeg1
    have heC : I'.connectedComponentMk e = C :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp heL).1).2
    have heE' : e.1 ∈ E' := (Finset.mem_filter.mp heL).2
    obtain ⟨f, hf_eq⟩ := Finset.card_eq_one.mp hdeg1
    have hf_nbr : f ∈ I'.neighborFinset e := by rw [hf_eq]; simp
    have hadj_ef : I'.Adj e f := (SimpleGraph.mem_neighborFinset I' e f).mp hf_nbr
    have hfFc : f.1 ∈ Fc := by
      rcases hadj_ef with ⟨_, hfFc, _⟩ | ⟨_, heFc, _⟩
      · exact hfFc
      · exact (Finset.disjoint_left.mp hDisjEF heE' heFc).elim
    have hon_ef : OnCritPath G e.1 f.1 := by
      rcases hadj_ef with ⟨_, _, hon⟩ | ⟨_, heFc, _⟩
      · exact hon
      · exact (Finset.disjoint_left.mp hDisjEF heE' heFc).elim
    have hfC : I'.connectedComponentMk f = C := by
      rw [← heC]
      exact SimpleGraph.ConnectedComponent.eq.mpr hadj_ef.symm.reachable
    have hfR : f ∈ R C :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfC⟩, hfFc⟩
    obtain ⟨_, _, u, hu_cn, y, hy_f, he_uy⟩ := hon_ef
    obtain ⟨hfNE, hf_cn1⟩ := Finset.mem_filter.mp hfFc
    have hcn_eq : commonNbrs G f.1 = {u} := by
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hf_cn1
      have : u = w := by rw [hw, Finset.mem_singleton] at hu_cn; exact hu_cn
      rw [hw, this]
    -- Name the other endpoint `x` of `f` so that `f.1 = s(x, y)`.
    obtain ⟨x, hf_xy⟩ : ∃ x : V, f.1 = s(x, y) := by
      rcases sym2_exists_eq f.1 with ⟨a, b, hab⟩
      rw [hab, Sym2.mem_iff] at hy_f
      rcases hy_f with rfl | rfl
      · exact ⟨b, by rw [hab, Sym2.eq_swap]⟩
      · exact ⟨a, hab⟩
    have hxy_ne : x ≠ y := (s_mem_nonEdges.mp (hf_xy ▸ hfNE)).1
    have hxy_nadj : ¬ G.Adj x y := (s_mem_nonEdges.mp (hf_xy ▸ hfNE)).2
    have hux_adj : G.Adj u x := (mem_commonNbrs.mp (hf_xy ▸ hu_cn)).1.symm
    have huy_adj : G.Adj u y := (mem_commonNbrs.mp (hf_xy ▸ hu_cn)).2.symm
    -- Since `C` is left-lopsided, `f` has degree 2 in `I'`, so `s(u, x)` must also be in `L C`.
    have hux_in_E' : s(u, x) ∈ E' := by
      have hfdeg2 : (I'.neighborFinset f).card = 2 := (hLL_degR C hLL).2 f hfR
      have hne_edges : s(u, x) ≠ s(u, y) := by
        intro h
        rw [Sym2.eq_iff] at h
        rcases h with ⟨_, hxy⟩ | ⟨h1, _⟩
        · exact hxy_ne hxy
        · exact huy_adj.ne h1
      by_contra hnotE'
      have hsub1 : (I'.neighborFinset f).image Subtype.val ⊆ {e.1} := by
        intro e' he'
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp he'
        have hadj' : I'.Adj f l := (SimpleGraph.mem_neighborFinset I' f l).mp hl
        have hlE' : l.1 ∈ E' := by
          rcases hadj' with ⟨hfE', _, _⟩ | ⟨hlE', _, _⟩
          · exact (Finset.disjoint_left.mp hDisjEF hfE' hfFc).elim
          · exact hlE'
        have hon' : OnCritPath G l.1 f.1 := by
          rcases hadj' with ⟨hfE', _, _⟩ | ⟨_, _, hon'⟩
          · exact (Finset.disjoint_left.mp hDisjEF hfE' hfFc).elim
          · exact hon'
        obtain ⟨_, _, w', hw', z, hz, hl_eq⟩ := hon'
        rw [hcn_eq, Finset.mem_singleton] at hw'
        subst hw'
        rw [hf_xy, Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exfalso
          exact hnotE' (by rw [Sym2.eq_swap, ← hl_eq]; exact hlE')
        · rw [Finset.mem_singleton, he_uy, hl_eq]
      have hle1 : 2 ≤ 1 := by
        calc 2 = (I'.neighborFinset f).card := hfdeg2.symm
          _ = ((I'.neighborFinset f).image Subtype.val).card :=
            (Finset.card_image_of_injective _ Subtype.val_injective).symm
          _ ≤ ({e.1} : Finset (Sym2 V)).card := Finset.card_le_card hsub1
          _ = 1 := Finset.card_singleton _
      omega
    have hux_U : s(u, x) ∈ U := Finset.mem_union_left _ hux_in_E'
    have hux_C : I'.connectedComponentMk ⟨s(u, x), hux_U⟩ = C := by
      have hon_ux : OnCritPath G s(u, x) f.1 :=
        ⟨(Finset.mem_sdiff.mp hux_in_E').1, hfFc, u, hu_cn, x, by rw [hf_xy]; simp, Sym2.eq_swap⟩
      have hadj_ux : I'.Adj ⟨s(u, x), hux_U⟩ f := Or.inl ⟨hux_in_E', hfFc, hon_ux⟩
      rw [← hfC]
      exact SimpleGraph.ConnectedComponent.eq.mpr hadj_ux.reachable
    -- Helper: Branch 1 (`u ∈ matchedVerts M`) yields either `(u*, x)` or `(u*, y)`.
    have branch1 : u ∈ matchedVerts M →
        IsSwitchExit C (mate hM u) x ∨ IsSwitchExit C (mate hM u) y := by
      intro huM
      have hum_ne_x : mate hM u ≠ x := by
        intro h
        exact (Finset.mem_sdiff.mp hux_in_E').2 (h ▸ s_mate_mem hM huM)
      have hum_ne_y : mate hM u ≠ y := by
        intro h
        have huy_notM : s(u, y) ∉ M := by
          rw [Sym2.eq_swap, ← he_uy]
          exact (Finset.mem_sdiff.mp heE').2
        exact huy_notM (h ▸ s_mate_mem hM huM)
      have hnotboth : ¬ (G.Adj (mate hM u) x ∧ G.Adj (mate hM u) y) := by
        rintro ⟨h1, h2⟩
        have hmem : mate hM u ∈ commonNbrs G f.1 := by
          rw [hf_xy, mem_commonNbrs]
          exact ⟨h1.symm, h2.symm⟩
        rw [hcn_eq, Finset.mem_singleton] at hmem
        exact mate_ne hM huM hmem
      by_cases h1 : G.Adj (mate hM u) x
      · have h2 : ¬ G.Adj (mate hM u) y := fun h2 => hnotboth ⟨h1, h2⟩
        refine Or.inr (lemma_2_9 C hLL (mate hM u) y (s_mem_nonEdges.mpr ⟨hum_ne_y, h2⟩)
          (mate_mem_matchedVerts hM huM) ?_)
        rw [mate_mate hM huM]
        have heq_e : s(u, y) = e.1 := by rw [he_uy, Sym2.eq_swap]
        refine ⟨heq_e ▸ e.2, heq_e ▸ heE', ?_⟩
        have hsub : (⟨s(u, y), heq_e ▸ e.2⟩ : {p : Sym2 V // p ∈ U}) = e := Subtype.ext heq_e
        rw [hsub]
        exact heC
      · refine Or.inl (lemma_2_9 C hLL (mate hM u) x (s_mem_nonEdges.mpr ⟨hum_ne_x, h1⟩)
          (mate_mem_matchedVerts hM huM) ?_)
        rw [mate_mate hM huM]
        exact ⟨hux_U, hux_in_E', hux_C⟩
    -- Helper: Branch 2 (`x ∈ matchedVerts M`) yields either `(x*, u)` (2a) or `(x*, y)` (2b).
    have branch2 : x ∈ matchedVerts M →
        IsSwitchExit C (mate hM x) u ∨ IsSwitchExit C (mate hM x) y := by
      intro hxM
      have hxm_ne_u : mate hM x ≠ u := by
        intro h
        exact (Finset.mem_sdiff.mp hux_in_E').2 (by rw [Sym2.eq_swap, ← h]; exact s_mate_mem hM hxM)
      have hxm_ne_y : mate hM x ≠ y := by
        intro h
        exact hxy_nadj (h ▸ mate_adj hM hxM)
      by_cases hxu : G.Adj (mate hM x) u
      · -- Case 2b: `x*u` is an edge, so `x*y` is a noncritical non-edge switching to `f = s(x, y)`.
        have hxmy_nadj : ¬ G.Adj (mate hM x) y := by
          intro h
          have hmem : mate hM x ∈ commonNbrs G f.1 := by
            rw [hf_xy, mem_commonNbrs]
            exact ⟨mate_adj hM hxM, h.symm⟩
          rw [hcn_eq, Finset.mem_singleton] at hmem
          exact hxm_ne_u hmem
        have hxmy_NE : s(mate hM x, y) ∈ nonEdges G := s_mem_nonEdges.mpr ⟨hxm_ne_y, hxmy_nadj⟩
        have hxmy_Fnc : s(mate hM x, y) ∈ Fnc := by
          have hpos : 0 < (commonNbrs G s(mate hM x, y)).card :=
            Finset.card_pos.mpr (commonNbrs_nonempty_of_nonEdge hcrit.1 hxmy_NE)
          suffices hne1 : (commonNbrs G s(mate hM x, y)).card ≠ 1 by
            exact Finset.mem_filter.mpr ⟨hxmy_NE, by omega⟩
          intro hcard1
          have hfc' : s(mate hM x, y) ∈ Fc := Finset.mem_filter.mpr ⟨hxmy_NE, hcard1⟩
          have hfc'U : s(mate hM x, y) ∈ U := Finset.mem_union_right _ hfc'
          have hu_cn' : u ∈ commonNbrs G s(mate hM x, y) :=
            mem_commonNbrs.mpr ⟨hxu, huy_adj.symm⟩
          have hon' : OnCritPath G e.1 s(mate hM x, y) :=
            ⟨(Finset.mem_sdiff.mp heE').1, hfc', u, hu_cn', y, by simp, he_uy⟩
          have hadj' : I'.Adj e ⟨s(mate hM x, y), hfc'U⟩ := Or.inl ⟨heE', hfc', hon'⟩
          have hmem' : ⟨s(mate hM x, y), hfc'U⟩ ∈ I'.neighborFinset e :=
            (SimpleGraph.mem_neighborFinset I' e _).mpr hadj'
          rw [hf_eq, Finset.mem_singleton] at hmem'
          have hval : s(mate hM x, y) = s(x, y) := by
            have := congrArg Subtype.val hmem'
            simpa [hf_xy] using this
          rw [Sym2.eq_iff] at hval
          rcases hval with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact mate_ne hM hxM h1
          · exact hxy_ne h2.symm
        refine Or.inr ⟨hxmy_Fnc, mate_mem_matchedVerts hM hxM, ?_⟩
        rw [mate_mate hM hxM]
        refine ⟨hf_xy ▸ f.2, ?_⟩
        have hsub : (⟨s(x, y), hf_xy ▸ f.2⟩ : {p : Sym2 V // p ∈ U}) = f := Subtype.ext hf_xy.symm
        rw [hsub]
        exact hfC
      · -- Case 2a: `x*u` is a non-edge, switching to `xu ∈ L C`.
        refine Or.inl (lemma_2_9 C hLL (mate hM x) u (s_mem_nonEdges.mpr ⟨hxm_ne_u, hxu⟩)
          (mate_mem_matchedVerts hM hxM) ?_)
        rw [mate_mate hM hxM]
        refine ⟨by rw [Sym2.eq_swap]; exact hux_U, by rw [Sym2.eq_swap]; exact hux_in_E', ?_⟩
        have hsub : (⟨s(x, u), by rw [Sym2.eq_swap]; exact hux_U⟩ : {p : Sym2 V // p ∈ U}) =
            ⟨s(u, x), hux_U⟩ := Subtype.ext Sym2.eq_swap
        rw [hsub]
        exact hux_C
    -- By maximality of `M`, either `u ∈ matchedVerts M` or `x ∈ matchedVerts M`.
    have hor_ux : u ∈ matchedVerts M ∨ x ∈ matchedVerts M := by
      obtain ⟨z, hz, m, hmM, hzm⟩ := hMmax s(u, x) (Finset.mem_sdiff.mp hux_in_E').1
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, m, hmM, hzm⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, m, hmM, hzm⟩)
    by_cases huM : u ∈ matchedVerts M
    · rcases branch1 huM with h1a | h1b
      · -- Case 1a: `(u*, x)` is a switch exit.
        by_cases hxM : x ∈ matchedVerts M
        · rcases branch2 hxM with h2a | h2b
          · refine Or.inl (Or.inr ⟨(mate hM u, x), (mate hM x, u), ?_, h1a, h2a⟩)
            intro h
            exact hux_adj.ne (Prod.mk.inj h).2.symm
          · refine Or.inl (Or.inr ⟨(mate hM u, x), (mate hM x, y), ?_, h1a, h2b⟩)
            intro h
            exact hxy_ne (Prod.mk.inj h).2
        · exact Or.inl (Or.inl ⟨mate hM u, x, h1a, hxM⟩)
      · -- Case 1b: `(u*, y)` is a switch exit switching back to `e`.
        refine Or.inr ⟨mate hM u, y, h1b, Or.inl ?_⟩
        rw [mate_mate hM huM, he_uy, Sym2.eq_swap]
    · have hxM : x ∈ matchedVerts M := hor_ux.resolve_left huM
      rcases branch2 hxM with h2a | h2b
      · -- Case 2a with `u ∉ matchedVerts M`: safe switch exit!
        exact Or.inl (Or.inl ⟨mate hM x, u, h2a, huM⟩)
      · -- Case 2b: `(x*, y)` switches back to `f`.
        refine Or.inr ⟨mate hM x, y, h2b, Or.inr ⟨f, hfR, ?_, u, hu_cn, by rw [he_uy, Sym2.eq_swap]⟩⟩
        rw [mate_mate hM hxM, hf_xy]
  -- Lemma 2.11: left-lopsided component with `|L C| ≥ 2` has a safe switch exit or two switch exits.
  have lemma_2_11 : ∀ C, IsLL C → 2 ≤ (L C).card →
      (∃ p q, IsSafeSwitchExit C p q) ∨
      (∃ a b : V × V, a ≠ b ∧ IsSwitchExit C a.1 a.2 ∧ IsSwitchExit C b.1 b.2) := by
    intro C hLL hge2
    obtain ⟨e₁, he₁L, e₂, he₂L, hne12, hdeg1, hdeg2⟩ := hLL_two_leaves C hLL hge2
    rcases leaf_analysis C hLL e₁ he₁L hdeg1 with hdone | ⟨p₁, q₁, hex₁, htag₁⟩
    · exact hdone
    rcases leaf_analysis C hLL e₂ he₂L hdeg2 with hdone | ⟨p₂, q₂, hex₂, htag₂⟩
    · exact hdone
    refine Or.inr ⟨(p₁, q₁), (p₂, q₂), ?_, hex₁, hex₂⟩
    intro heq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    rcases htag₁ with h1b | ⟨f₁, hf₁R, hf₁_eq, u₁, hu₁_cn, he₁_eq⟩ <;>
      rcases htag₂ with h2b | ⟨f₂, hf₂R, hf₂_eq, u₂, hu₂_cn, he₂_eq⟩
    · exact hne12 (Subtype.ext (h1b.symm.trans h2b))
    · exact Finset.disjoint_left.mp hDisjEF
        (Finset.mem_filter.mp he₁L).2
        (h1b ▸ hf₂_eq ▸ (Finset.mem_filter.mp hf₂R).2)
    · exact Finset.disjoint_left.mp hDisjEF
        (Finset.mem_filter.mp he₂L).2
        (h2b ▸ hf₁_eq ▸ (Finset.mem_filter.mp hf₁R).2)
    · have hf12 : f₁.1 = f₂.1 := hf₁_eq.symm.trans hf₂_eq
      have hcard1 : (commonNbrs G f₁.1).card = 1 :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hf₁R).2).2
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
      have hu1w : u₁ = w := by rw [hw, Finset.mem_singleton] at hu₁_cn; exact hu₁_cn
      have hu2w : u₂ = w := by rw [← hf12, hw, Finset.mem_singleton] at hu₂_cn; exact hu₂_cn
      exact hne12 (Subtype.ext (by rw [he₁_eq, he₂_eq, hu1w, hu2w]))
  -- Corollary 2.12 + Double counting: `|C_l| ≤ |Fnc|`.
  let Cl : Finset I'.ConnectedComponent := Finset.univ.filter IsLL
  have hCl_le_Fnc : Cl.card ≤ Fnc.card := by
    let w : V × V → ℕ := fun pq =>
      if ∃ C ∈ Cl, IsSwitchExit C pq.1 pq.2 then
        if pq.2 ∉ matchedVerts M then 2 else 1
      else 0
    -- Lower bound: `2 * |Cl| ≤ ∑ pq : V × V, w pq`.
    have hlow : 2 * Cl.card ≤ ∑ pq : V × V, w pq := by
      let S : I'.ConnectedComponent → Finset (V × V) := fun C =>
        Finset.univ.filter (fun pq => IsSwitchExit C pq.1 pq.2)
      have hS_disj : (Cl : Set I'.ConnectedComponent).PairwiseDisjoint S := by
        intro C₁ _ C₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro pq h1 h2
        obtain ⟨_, _, hU₁, hC₁⟩ := (Finset.mem_filter.mp h1).2
        obtain ⟨_, _, hU₂, hC₂⟩ := (Finset.mem_filter.mp h2).2
        exact hne (hC₁.symm.trans hC₂)
      have hS_ge2 : ∀ C ∈ Cl, 2 ≤ ∑ pq ∈ S C, w pq := by
        intro C hC
        have hLL : IsLL C := (Finset.mem_filter.mp hC).2
        have hLpos : 1 ≤ (L C).card := by dsimp [IsLL] at hLL; omega
        have hcases : (∃ p q, IsSafeSwitchExit C p q) ∨
            (∃ a b : V × V, a ≠ b ∧ IsSwitchExit C a.1 a.2 ∧ IsSwitchExit C b.1 b.2) := by
          by_cases h1 : (L C).card = 1
          · exact lemma_2_10 C hLL h1
          · exact lemma_2_11 C hLL (by omega)
        rcases hcases with ⟨p, q, hex, hqnotM⟩ | ⟨a, b, hne, ha, hb⟩
        · have hmem : (p, q) ∈ S C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hex⟩
          have hex' : ∃ C' ∈ Cl, IsSwitchExit C' p q := ⟨C, hC, hex⟩
          have hw2 : w (p, q) = 2 := by
            simp only [w, if_pos hex', if_pos hqnotM]
          calc 2 = w (p, q) := hw2.symm
            _ ≤ ∑ pq ∈ S C, w pq := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
        · have ha_mem : a ∈ S C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
          have hb_mem : b ∈ S C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
          have ha' : ∃ C' ∈ Cl, IsSwitchExit C' a.1 a.2 := ⟨C, hC, ha⟩
          have hb' : ∃ C' ∈ Cl, IsSwitchExit C' b.1 b.2 := ⟨C, hC, hb⟩
          have hwa : 1 ≤ w a := by
            simp only [w, if_pos ha']
            split_ifs <;> omega
          have hwb : 1 ≤ w b := by
            simp only [w, if_pos hb']
            split_ifs <;> omega
          have hsub : ({a, b} : Finset (V × V)) ⊆ S C := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> assumption
          calc 2 ≤ w a + w b := by omega
            _ = ∑ pq ∈ ({a, b} : Finset (V × V)), w pq := (Finset.sum_pair hne).symm
            _ ≤ ∑ pq ∈ S C, w pq := Finset.sum_le_sum_of_subset hsub
      calc 2 * Cl.card
          = ∑ _C ∈ Cl, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ C ∈ Cl, ∑ pq ∈ S C, w pq := Finset.sum_le_sum hS_ge2
        _ = ∑ pq ∈ Cl.biUnion S, w pq := (Finset.sum_biUnion hS_disj).symm
        _ ≤ ∑ pq : V × V, w pq := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    -- Upper bound: `∑ pq : V × V, w pq ≤ 2 * |Fnc|`.
    have hupp : ∑ pq : V × V, w pq ≤ 2 * Fnc.card := by
      let T : Sym2 V → Finset (V × V) := fun f => Finset.univ.filter (fun pq => s(pq.1, pq.2) = f)
      have hT_disj : (Fnc : Set (Sym2 V)).PairwiseDisjoint T := by
        intro f₁ _ f₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro pq h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      have hsupp_sub : (Finset.univ : Finset (V × V)).filter (fun pq => w pq ≠ 0) ⊆
          Fnc.biUnion T := by
        intro pq hpq
        have hwne : w pq ≠ 0 := (Finset.mem_filter.mp hpq).2
        have hex : ∃ C ∈ Cl, IsSwitchExit C pq.1 pq.2 := by
          by_contra h
          exact hwne (by simp [w, h])
        obtain ⟨C, _, hfnc, _, _⟩ := hex
        exact Finset.mem_biUnion.mpr ⟨s(pq.1, pq.2), hfnc,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
      have hT_le2 : ∀ f ∈ Fnc, ∑ pq ∈ T f, w pq ≤ 2 := by
        intro f hf
        rcases sym2_exists_eq f with ⟨a, b, hab⟩
        have hab_ne : a ≠ b := (s_mem_nonEdges.mp (hab ▸ (Finset.mem_filter.mp hf).1)).1
        have hTeq : T f = {(a, b), (b, a)} := by
          ext ⟨p, q⟩
          simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, hab, Sym2.eq_iff,
            Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        rw [hTeq, Finset.sum_pair (fun h => hab_ne (Prod.mk.inj h).1)]
        have hw_zero_of_notM : ∀ p q : V, p ∉ matchedVerts M → w (p, q) = 0 := by
          intro p q hp
          have hno : ¬ ∃ C ∈ Cl, IsSwitchExit C p q := fun ⟨_, _, _, hpM, _⟩ => hp hpM
          simp [w, hno]
        by_cases haM : a ∈ matchedVerts M <;> by_cases hbM : b ∈ matchedVerts M
        · have h1 : w (a, b) ≤ 1 := by simp only [w]; split_ifs <;> omega
          have h2 : w (b, a) ≤ 1 := by simp only [w]; split_ifs <;> omega
          omega
        · have h1 : w (a, b) ≤ 2 := by simp only [w]; split_ifs <;> omega
          have h2 : w (b, a) = 0 := hw_zero_of_notM b a hbM
          omega
        · have h1 : w (a, b) = 0 := hw_zero_of_notM a b haM
          have h2 : w (b, a) ≤ 2 := by simp only [w]; split_ifs <;> omega
          omega
        · rw [hw_zero_of_notM a b haM, hw_zero_of_notM b a hbM]
          omega
      calc ∑ pq : V × V, w pq
          = ∑ pq ∈ (Finset.univ : Finset (V × V)).filter (fun pq => w pq ≠ 0), w pq := by
            rw [Finset.sum_filter_ne_zero]
        _ ≤ ∑ pq ∈ Fnc.biUnion T, w pq := Finset.sum_le_sum_of_subset hsupp_sub
        _ = ∑ f ∈ Fnc, ∑ pq ∈ T f, w pq := Finset.sum_biUnion hT_disj
        _ ≤ ∑ _f ∈ Fnc, 2 := Finset.sum_le_sum hT_le2
        _ = 2 * Fnc.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    omega
  -- Lemma 2.5: sum `|L C| ≤ |R C| + 1_{C ∈ Cl}` over all connected components `C`.
  have hsumL_eq : ∑ C : I'.ConnectedComponent, (L C).card = E'.card := by
    have hdisj : ((Finset.univ : Finset I'.ConnectedComponent) : Set I'.ConnectedComponent).PairwiseDisjoint L := by
      intro C₁ _ C₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro v h1 h2
      have hc1 := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
      have hc2 := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2
      exact hne (hc1.symm.trans hc2)
    rw [← Finset.card_biUnion hdisj]
    refine Finset.card_bij (fun v _ => v.1) ?_ ?_ ?_
    · intro v hv
      obtain ⟨C, _, hvL⟩ := Finset.mem_biUnion.mp hv
      exact (Finset.mem_filter.mp hvL).2
    · intro v₁ _ v₂ _ h
      exact Subtype.ext h
    · intro e he
      have heU : e ∈ U := Finset.mem_union_left _ he
      refine ⟨⟨e, heU⟩, Finset.mem_biUnion.mpr ⟨I'.connectedComponentMk ⟨e, heU⟩,
        Finset.mem_univ _, ?_⟩, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, he⟩
  have hsumR_eq : ∑ C : I'.ConnectedComponent, (R C).card = Fc.card := by
    have hdisj : ((Finset.univ : Finset I'.ConnectedComponent) : Set I'.ConnectedComponent).PairwiseDisjoint R := by
      intro C₁ _ C₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro v h1 h2
      have hc1 := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
      have hc2 := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2
      exact hne (hc1.symm.trans hc2)
    rw [← Finset.card_biUnion hdisj]
    refine Finset.card_bij (fun v _ => v.1) ?_ ?_ ?_
    · intro v hv
      obtain ⟨C, _, hvR⟩ := Finset.mem_biUnion.mp hv
      exact (Finset.mem_filter.mp hvR).2
    · intro v₁ _ v₂ _ h
      exact Subtype.ext h
    · intro f hf
      have hfU : f ∈ U := Finset.mem_union_right _ hf
      refine ⟨⟨f, hfU⟩, Finset.mem_biUnion.mpr ⟨I'.connectedComponentMk ⟨f, hfU⟩,
        Finset.mem_univ _, ?_⟩, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, hf⟩
  have hE'_le : E'.card ≤ Fc.card + Cl.card := by
    rw [← hsumL_eq, ← hsumR_eq]
    have hCl_sum : Cl.card = ∑ C : I'.ConnectedComponent, if IsLL C then 1 else 0 := by
      dsimp [Cl]
      rw [Finset.card_filter]
    rw [hCl_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun C _ => ?_)
    split_ifs with hLL
    · exact hL_le C
    · dsimp [IsLL] at hLL
      omega
  have hF_split : Fc.card + Fnc.card = (nonEdges G).card := card_crit_add_nonCrit hcrit.1
  change E'.card ≤ (nonEdges G).card
  omega

/-- Main theorem (Murty-Simon conjecture): every finite diameter-2-critical graph
has at most `⌊n^2 / 4⌋` edges. -/
theorem murty_simon (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Erdos742.IsDiameter2Critical G) :
    G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4 := by
  obtain ⟨M, hM, hMmax⟩ := exists_maximal_matching G
  have h1 : (G.edgeFinset \ M).card ≤ (nonEdges G).card :=
    card_sdiff_matching_le_nonEdges G hcrit M hM hMmax
  have hsdiff : (G.edgeFinset \ M).card + M.card = G.edgeFinset.card :=
    Finset.card_sdiff_add_card_eq_card hM.1
  have h2 : 2 * (G.edgeFinset.card + (nonEdges G).card) =
      Fintype.card V * (Fintype.card V - 1) :=
    two_mul_card_edges_add_nonEdges G
  have h3 : 2 * M.card ≤ Fintype.card V :=
    two_mul_card_matching_le hM
  have hsq : Fintype.card V * (Fintype.card V - 1) + Fintype.card V = (Fintype.card V) ^ 2 := by
    cases hn : Fintype.card V with
    | zero => simp
    | succ k =>
      simp only [Nat.add_sub_cancel, sq]
      ring
  have h4 : 4 * G.edgeFinset.card ≤ (Fintype.card V) ^ 2 := by omega
  omega

end MainProof

end Erdos742Proof

theorem OMA.solution : type_of% @Erdos742.erdos_742 :=
  fun _ _ _ G _ hG => Erdos742Proof.murty_simon G hG
