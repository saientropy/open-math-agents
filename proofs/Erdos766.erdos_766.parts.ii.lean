import FormalConjectures.ErdosProblems.«766»

/-!
Proof of `Erdos766.erdos_766.parts.ii`: for every `k : ℕ`, eventually for `n ≥ k`,
`Erdos766.forcingNumber n k` is strictly monotone on `Set.Ioc k (k ^ 2 / 4)`.

In fact, for all `k ≤ n` and `l + 1 ≤ k.choose 2`, `forcingNumber n k l < forcingNumber n k (l + 1)`:
if `m' = forcingNumber n k (l + 1)`, then `m' ≥ 1`, and for any `n`-vertex graph `G` with `m' - 1`
edges, either `G = ⊤` (containing an `l`-edge subgraph of `K_k`) or adding one missing edge `e₀`
produces a graph `G'` with `m'` edges containing some `(l + 1)`-edge `k`-vertex copy `H'`, from
which deleting the unique edge mapping to `e₀` (or any edge if `e₀` is unused) leaves an `l`-edge
`k`-vertex copy inside `G`.
-/

namespace Erdos766Proof

open Filter SimpleGraph
open scoped SimpleGraph

private lemma edgeSet_fromEdgeSet_of_not_diag {V : Type*} (s : Set (Sym2 V))
    (h : ∀ e ∈ s, ¬ e.IsDiag) :
    (SimpleGraph.fromEdgeSet s).edgeSet = s := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromEdgeSet_adj]
    constructor
    · exact fun huv => huv.1
    · intro huv
      refine ⟨huv, fun heq => h s(u, v) huv ?_⟩
      subst heq
      simp

private lemma edgeSet_ncard_le_choose_two {n : ℕ} (G : SimpleGraph (Fin n)) :
    G.edgeSet.ncard ≤ n.choose 2 := by
  classical
  have hsub : G.edgeFinset ⊆ (⊤ : SimpleGraph (Fin n)).edgeFinset := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    exact SimpleGraph.edgeSet_mono le_top he
  calc G.edgeSet.ncard = G.edgeFinset.card := by
        rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
    _ ≤ (⊤ : SimpleGraph (Fin n)).edgeFinset.card := Finset.card_le_card hsub
    _ = n.choose 2 := by
        rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]

private lemma forcingSet_nonempty (n k l : ℕ) :
    {m : ℕ | ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
      ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G}.Nonempty := by
  refine ⟨n.choose 2 + 1, fun G hG => ?_⟩
  have hle := edgeSet_ncard_le_choose_two G
  omega

private lemma forcingNumber_lt_succ {n k l : ℕ} (hkn : k ≤ n) (hl : l + 1 ≤ k.choose 2) :
    Erdos766.forcingNumber n k l < Erdos766.forcingNumber n k (l + 1) := by
  classical
  set m' := Erdos766.forcingNumber n k (l + 1)
  have hm'_mem : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m' →
      ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l + 1 ∧ H ⊑ G :=
    Nat.sInf_mem (forcingSet_nonempty n k (l + 1))
  have hm'_pos : 1 ≤ m' := by
    by_contra h0
    have hm0 : m' = 0 := by omega
    have hbot : (⊥ : SimpleGraph (Fin n)).edgeSet.ncard = m' := by
      simp [hm0]
    obtain ⟨H, hHcard, ⟨f⟩⟩ := hm'_mem ⊥ hbot
    have hne : H.edgeSet.Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _), hHcard]
      omega
    obtain ⟨e, he⟩ := hne
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      exact (f.toHom.map_rel he)
  have hle : Erdos766.forcingNumber n k l ≤ m' - 1 := by
    refine Erdos766.forcingNumber_le fun G hG => ?_
    by_cases htop : G = ⊤
    · subst htop
      have hcard_top : (⊤ : SimpleGraph (Fin k)).edgeFinset.card = k.choose 2 := by
        rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
      obtain ⟨E, hEsub, hEcard⟩ := Finset.exists_subset_card_eq (by omega : l ≤ (⊤ : SimpleGraph (Fin k)).edgeFinset.card)
      have hnd : ∀ e ∈ (E : Set (Sym2 (Fin k))), ¬ e.IsDiag := fun e he =>
        SimpleGraph.not_isDiag_of_mem_edgeSet _ (SimpleGraph.mem_edgeFinset.mp (hEsub he))
      refine ⟨SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin k))), ?_, ?_⟩
      · rw [edgeSet_fromEdgeSet_of_not_diag _ hnd, Set.ncard_coe_finset, hEcard]
      · refine ⟨⟨⟨Fin.castLE hkn, fun hab => ?_⟩, Fin.castLE_injective hkn⟩⟩
        exact (Fin.castLE_injective hkn).ne hab.ne
    · have hex : ∃ e₀ ∈ (⊤ : SimpleGraph (Fin n)).edgeSet, e₀ ∉ G.edgeSet := by
        by_contra hall
        push Not at hall
        apply htop
        ext u v
        simp only [SimpleGraph.top_adj]
        constructor
        · exact fun h => h.ne
        · intro hne
          have hmem : s(u, v) ∈ (⊤ : SimpleGraph (Fin n)).edgeSet := by
            rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
            exact hne
          exact G.mem_edgeSet.mp (hall s(u, v) hmem)
      obtain ⟨e₀, he₀_top, he₀_not⟩ := hex
      have hnd_G' : ∀ e ∈ insert e₀ G.edgeSet, ¬ e.IsDiag := by
        intro e he
        rcases Set.mem_insert_iff.mp he with rfl | hmem
        · exact SimpleGraph.not_isDiag_of_mem_edgeSet _ he₀_top
        · exact SimpleGraph.not_isDiag_of_mem_edgeSet _ hmem
      set G' : SimpleGraph (Fin n) := SimpleGraph.fromEdgeSet (insert e₀ G.edgeSet)
      have hG'_edges : G'.edgeSet = insert e₀ G.edgeSet :=
        edgeSet_fromEdgeSet_of_not_diag _ hnd_G'
      have hG'_card : G'.edgeSet.ncard = m' := by
        rw [hG'_edges, Set.ncard_insert_of_notMem he₀_not (Set.toFinite _), hG]
        omega
      obtain ⟨H', hH'_card, ⟨f⟩⟩ := hm'_mem G' hG'_card
      set E' : Finset (Sym2 (Fin k)) := H'.edgeFinset
      have hE'_card : E'.card = l + 1 := by
        rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, hH'_card]
      have hex_e1 : ∃ e₁ ∈ E', ∀ e ∈ E'.erase e₁, Sym2.map f e ≠ e₀ := by
        by_cases hit : ∃ e₁ ∈ E', Sym2.map f e₁ = e₀
        · obtain ⟨e₁, he₁, hmap⟩ := hit
          refine ⟨e₁, he₁, fun e he hmeq => ?_⟩
          have hneq : e ≠ e₁ := (Finset.mem_erase.mp he).1
          exact hneq (Sym2.map.injective f.injective (hmeq.trans hmap.symm))
        · push Not at hit
          have hE'_ne : E'.Nonempty := Finset.card_pos.mp (by omega)
          obtain ⟨e₁, he₁⟩ := hE'_ne
          exact ⟨e₁, he₁, fun e he => hit e (Finset.mem_of_mem_erase he)⟩
      obtain ⟨e₁, he₁_mem, he₁_avoid⟩ := hex_e1
      set E : Finset (Sym2 (Fin k)) := E'.erase e₁
      have hnd_E : ∀ e ∈ (E : Set (Sym2 (Fin k))), ¬ e.IsDiag := fun e he =>
        SimpleGraph.not_isDiag_of_mem_edgeSet _
          (SimpleGraph.mem_edgeFinset.mp (Finset.mem_of_mem_erase he))
      set H : SimpleGraph (Fin k) := SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin k)))
      have hH_edges : H.edgeSet = (E : Set (Sym2 (Fin k))) :=
        edgeSet_fromEdgeSet_of_not_diag _ hnd_E
      refine ⟨H, ?_, ?_⟩
      · rw [hH_edges, Set.ncard_coe_finset, Finset.card_erase_of_mem he₁_mem, hE'_card]
        omega
      · refine ⟨⟨⟨f, fun {a b} hab => ?_⟩, f.injective⟩⟩
        have hmemE : s(a, b) ∈ E := by
          have := H.mem_edgeSet.mpr hab
          rwa [hH_edges, Finset.mem_coe] at this
        have hH'adj : H'.Adj a b :=
          H'.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp (Finset.mem_of_mem_erase hmemE))
        have hG'adj : G'.Adj (f a) (f b) := f.toHom.map_rel hH'adj
        have hmemG' : s(f a, f b) ∈ insert e₀ G.edgeSet := by
          rwa [← hG'_edges, SimpleGraph.mem_edgeSet]
        have hne₀ : s(f a, f b) ≠ e₀ := by
          simpa only [Sym2.map_mk] using he₁_avoid s(a, b) hmemE
        exact G.mem_edgeSet.mp ((Set.mem_insert_iff.mp hmemG').resolve_left hne₀)
  omega

private lemma forcingNumber_strictMono_range {n k : ℕ} (hkn : k ≤ n) :
    StrictMonoOn (Erdos766.forcingNumber n k) (Set.Ioc k (k ^ 2 / 4)) := by
  intro l₁ hl₁ l₂ hl₂ hlt
  have hk2_le_choose : k ^ 2 / 4 ≤ k.choose 2 := by
    rw [Nat.choose_two_right]
    have hk_ge2 : 2 ≤ k := by
      have : k < k ^ 2 / 4 := lt_of_lt_of_le hl₁.1 hl₁.2
      by_contra hlt2
      interval_cases k <;> omega
    have hmul : k ^ 2 ≤ 2 * (k * (k - 1)) := by
      have hsub : k * (k - 1) + k = k * k := by
        cases k with
        | zero => omega
        | succ m => simp [Nat.mul_succ]
      nlinarith
    omega
  have hstep : ∀ d : ℕ, l₁ + 1 + d ≤ k.choose 2 →
      Erdos766.forcingNumber n k l₁ < Erdos766.forcingNumber n k (l₁ + 1 + d) := by
    intro d
    induction d with
    | zero =>
      intro hd
      simpa using forcingNumber_lt_succ hkn (by omega)
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have h2 := forcingNumber_lt_succ hkn (l := l₁ + 1 + d) (by omega)
      exact lt_trans h1 h2
  have hdecomp : l₂ = l₁ + 1 + (l₂ - l₁ - 1) := by omega
  rw [hdecomp]
  exact hstep (l₂ - l₁ - 1) (by have := hl₂.2; omega)

end Erdos766Proof

theorem OMA.solution : type_of% @Erdos766.erdos_766.parts.ii :=
  fun k => Filter.eventually_atTop.mpr ⟨k, fun _ hkn => Erdos766Proof.forcingNumber_strictMono_range hkn⟩
