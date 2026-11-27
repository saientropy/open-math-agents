import FormalConjectures.OEIS.«229232»

/-!
# Proof of Zhi-Wei Sun's Finite Field Primitive-Product Circular Permutation Conjecture (-1)

For every finite field `F` with `q = Fintype.card F > 7`, there exists a circular permutation
`a : Fin (q - 1) ≃ Fˣ` such that every adjacent product `a i * a ((i + 1) % (q - 1)) - 1`
is a primitive element of `F`.

Proof structure:
1. Vertex-Menger's theorem (Göring's edge-deletion induction) and the Chvátal–Erdős Hamiltonicity
   theorem (`Solver3.chvatal_erdos`).
2. Finite-field character theory, Jacobi-sum bounds, expander mixing on `Fˣ`, Cohen–Trudgian lower
   sieves, and `e`-free upper sieves (`Solver3.exists_circ_perm_of_analytic`).
3. Unconditional analytic coverage for all `q ≥ 8100` (`Solver3.analytic_ge_8100`) and verified
   double-squeeze integer range coverage for all `7 < q < 8100` outside 44 exceptional fields
   (`Solver3.below8100_ok`).
4. Explicit kernel-verified cycles (primes via `ZMod p`, squares via `QuadraticAlgebra`, algebraic
   constructions for `GF(16)` and `GF(27)`, plus `q ≡ 1 (mod 4)` and `char 2` sign transport).
-/

namespace Solver3

open Finset BigOperators

/- ### Part 1: Simple paths, vertex-Menger's theorem, and Chvátal–Erdős theorem -/

section GraphTheory

variable {V : Type*}

/-- A simple path in an undirected graph `adj`. -/
def IsPath (adj : V → V → Prop) (p : List V) : Prop :=
  p ≠ [] ∧ p.Nodup ∧ p.IsChain adj

/-- A simple cycle of length at least 3 in `adj`. -/
def IsCycle (adj : V → V → Prop) (cyc : List V) : Prop :=
  3 ≤ cyc.length ∧ cyc.Nodup ∧
    ∀ i : Fin cyc.length, adj cyc[i] (cyc[(i.val + 1) % cyc.length]'(Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => Fin.elim0 (h ▸ i))))

lemma isPath_singleton (adj : V → V → Prop) (v : V) : IsPath adj [v] :=
  ⟨List.cons_ne_nil _ _, List.nodup_singleton v, List.isChain_singleton v⟩

lemma isChain_imp_of_mem {R S : V → V → Prop} {l : List V} (h : l.IsChain R)
    (hf : ∀ x ∈ l, ∀ y ∈ l, R x y → S x y) : l.IsChain S := by
  induction l with
  | nil => exact List.IsChain.nil
  | cons a t ih =>
    cases t with
    | nil => exact List.isChain_singleton a
    | cons b t' =>
      obtain ⟨hab, hrest⟩ := List.isChain_cons_cons.mp h
      exact List.isChain_cons_cons.mpr ⟨hf a (by simp) b (by simp) hab,
        ih hrest fun x hx y hy => hf x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy)⟩

lemma isChain_map_iff {α β : Type*} (f : α → β) (R : β → β → Prop) :
    ∀ (l : List α), (l.map f).IsChain R ↔ l.IsChain (fun x y => R (f x) (f y))
  | [] => by simp
  | [_] => by simp
  | a :: b :: t => by
    simp only [List.map_cons, List.isChain_cons_cons]
    exact and_congr Iff.rfl (isChain_map_iff f R (b :: t))

lemma dropLast_map_eq {α β : Type*} (f : α → β) :
    ∀ (l : List α), (l.map f).dropLast = l.dropLast.map f
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
    simp only [List.map_cons, List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _)]
    exact congrArg (f a :: ·) (dropLast_map_eq f (b :: t))


lemma isPath_reverse {adj : V → V → Prop} (hsym : (∀ ⦃x y⦄, adj x y → adj y x)) {p : List V}
    (hp : IsPath adj p) : IsPath adj p.reverse := by
  refine ⟨by simp [hp.1], List.nodup_reverse.mpr hp.2.1, ?_⟩
  rw [List.isChain_reverse]
  exact hp.2.2.imp (fun _ _ h => hsym h)

lemma isPath_take {adj : V → V → Prop} {p : List V} (hp : IsPath adj p)
    {k : ℕ} (hk : 0 < k) : IsPath adj (p.take k) := by
  refine ⟨?_, hp.2.1.sublist (List.take_sublist k p), hp.2.2.take k⟩
  intro h
  have hlen : (p.take k).length = 0 := by simp [h]
  rw [List.length_take] at hlen
  have hp0 : 0 < p.length := List.length_pos_of_ne_nil hp.1
  omega

lemma isPath_drop {adj : V → V → Prop} {p : List V} (hp : IsPath adj p)
    {k : ℕ} (hk : k < p.length) : IsPath adj (p.drop k) := by
  refine ⟨?_, hp.2.1.sublist (List.drop_sublist k p), hp.2.2.drop k⟩
  intro h
  have hlen : (p.drop k).length = 0 := by simp [h]
  rw [List.length_drop] at hlen
  omega

lemma isPath_of_imp {adj₁ adj₂ : V → V → Prop} (himp : ∀ x y, adj₁ x y → adj₂ x y)
    {p : List V} (hp : IsPath adj₁ p) : IsPath adj₂ p :=
  ⟨hp.1, hp.2.1, hp.2.2.imp himp⟩

lemma isPath_append {adj : V → V → Prop} {p q : List V}
    (hp : IsPath adj p) (hq : IsPath adj q)
    (hdisj : List.Disjoint p q)
    (hadj : adj (p.getLast hp.1) (q.head hq.1)) :
    IsPath adj (p ++ q) := by
  refine ⟨List.append_ne_nil_of_left_ne_nil hp.1 _, List.nodup_append.mpr ⟨hp.2.1, hq.2.1, fun _ ha _ hb h => hdisj ha (h ▸ hb)⟩, ?_⟩
  rw [List.isChain_append]
  refine ⟨hp.2.2, hq.2.2, ?_⟩
  intro x hx y hy
  rw [List.getLast?_eq_some_getLast hp.1, Option.mem_some_iff] at hx
  rw [List.head?_eq_some_head hq.1, Option.mem_some_iff] at hy
  subst hx; subst hy
  exact hadj

lemma isPath_glue {adj : V → V → Prop} {p q : List V}
    (hp : IsPath adj p) (hq : IsPath adj q)
    (heq : p.getLast hp.1 = q.head hq.1)
    (hdisj : List.Disjoint p q.tail) :
    IsPath adj (p ++ q.tail) := by
  cases hq_eq : q with
  | nil => exact absurd hq_eq hq.1
  | cons a t =>
    simp only [hq_eq, List.tail_cons, List.head_cons] at heq hdisj ⊢
    cases ht_eq : t with
    | nil =>
      simpa using hp
    | cons b t' =>
      have hqt : IsPath adj (b :: t') := by
        have := isPath_drop hq (k := 1) (by simp [hq_eq, ht_eq])
        simpa [hq_eq, ht_eq] using this
      have hab : adj a b := by
        have hch := hq.2.2
        rw [hq_eq, ht_eq] at hch
        exact List.isChain_cons_cons.mp hch |>.1
      have hlast : adj (p.getLast hp.1) ((b :: t').head hqt.1) := by
        simpa [heq] using hab
      exact isPath_append hp hqt (ht_eq ▸ hdisj) hlast

lemma getLast_append_tail {p q : List V} (hp : p ≠ []) (hq : q ≠ [])
    (heq : p.getLast hp = q.head hq) :
    (p ++ q.tail).getLast (List.append_ne_nil_of_left_ne_nil hp _) = q.getLast hq := by
  cases q with
  | nil => exact absurd rfl hq
  | cons a t =>
    cases t with
    | nil => simpa using heq
    | cons b t' => simp

lemma getLast_tail_eq {q : List V} (hq : q ≠ []) (ht : q.tail ≠ []) :
    q.tail.getLast ht = q.getLast hq := by
  cases q with
  | nil => exact absurd rfl hq
  | cons a t =>
    cases t with
    | nil => exact absurd rfl ht
    | cons b t' => simp

/-- Truncate a path at its first vertex belonging to `T`. -/
lemma exists_prefix_first_mem {adj : V → V → Prop} {p : List V} (hp : IsPath adj p)
    {T : Finset V} (hT : ∃ x ∈ p, x ∈ T) :
    ∃ p', ∃ hp' : IsPath adj p', p'.head hp'.1 = p.head hp.1 ∧
      p'.getLast hp'.1 ∈ T ∧
      (∀ z ∈ p', z ∈ p) ∧
      (∀ z ∈ p'.dropLast, z ∉ T) := by
  -- Find minimal index i < p.length with p[i] ∈ T
  have hex : ∃ i : ℕ, ∃ hi : i < p.length, p[i] ∈ T := by
    obtain ⟨x, hxp, hxT⟩ := hT
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hxp
    exact ⟨i, hi, hxT⟩
  classical
  let i := Nat.find hex
  have hi_spec : ∃ hi : i < p.length, p[i] ∈ T := Nat.find_spec hex
  obtain ⟨hi, hpT⟩ := hi_spec
  let p' := p.take (i + 1)
  have hp' : IsPath adj p' := isPath_take hp (Nat.succ_pos i)
  have hlen : p'.length = i + 1 := by simp [p', Nat.min_eq_left (Nat.succ_le_of_lt hi)]
  refine ⟨p', hp', ?_, ?_, ?_, ?_⟩
  · have h0 : 0 < p'.length := by omega
    rw [List.head_eq_getElem_zero, List.head_eq_getElem_zero]
    simp [p']
  · rw [List.getLast_eq_getElem]
    have hget : p'[p'.length - 1] = p[i] := by simp [p', hlen]
    rw [hget]; exact hpT
  · intro z hz
    exact List.mem_of_mem_take hz
  · intro z hz
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hz
    rw [List.length_dropLast] at hj
    have hj_lt : j < i := by omega
    have hnot := Nat.find_min hex hj_lt
    push Not at hnot
    have hget : (p'.dropLast)[j] = p[j]'(lt_trans hj_lt hi) := by
      rw [List.getElem_dropLast]
      simp [p']
    rw [hget]
    exact hnot (lt_trans hj_lt hi)

/-- Truncate a path at its last vertex belonging to `T`. -/
lemma exists_suffix_last_mem {adj : V → V → Prop} (hsym : (∀ ⦃x y⦄, adj x y → adj y x))
    {p : List V} (hp : IsPath adj p) {T : Finset V} (hT : ∃ x ∈ p, x ∈ T) :
    ∃ p', ∃ hp' : IsPath adj p', p'.head hp'.1 ∈ T ∧
      p'.getLast hp'.1 = p.getLast hp.1 ∧
      (∀ z ∈ p', z ∈ p) ∧
      (∀ z ∈ p'.tail, z ∉ T) := by
  have hTrev : ∃ x ∈ p.reverse, x ∈ T := by
    obtain ⟨x, hx, hxT⟩ := hT
    exact ⟨x, List.mem_reverse.mpr hx, hxT⟩
  obtain ⟨q, hq, hq_head, hq_last, hq_sub, hq_avoid⟩ :=
    exists_prefix_first_mem (isPath_reverse hsym hp) hTrev
  refine ⟨q.reverse, isPath_reverse hsym hq, ?_, ?_, ?_, ?_⟩
  · rw [List.head_reverse]; exact hq_last
  · rw [List.getLast_reverse]; rw [List.head_reverse] at hq_head; exact hq_head
  · intro z hz
    exact List.mem_reverse.mp (hq_sub z (List.mem_reverse.mp hz))
  · intro z hz
    have : z ∈ q.dropLast.reverse := by rwa [List.tail_reverse] at hz
    exact hq_avoid z (List.mem_reverse.mp this)

/-- `S` separates `X` from `Y` in `adj`. -/
def IsSep (adj : V → V → Prop) (X Y S : Finset V) : Prop :=
  ∀ p : List V, (hp : IsPath adj p) → p.head hp.1 ∈ X → p.getLast hp.1 ∈ Y → ∃ z ∈ p, z ∈ S

/-- Reachability from `X` avoiding `S` in `adj`. -/
def ReachAvoiding (adj : V → V → Prop) (X S : Finset V) (z : V) : Prop :=
  ∃ p : List V, ∃ hp : IsPath adj p, p.head hp.1 ∈ X ∧ p.getLast hp.1 = z ∧ ∀ w ∈ p, w ∉ S

lemma reachAvoiding_adj [DecidableEq V] {adj : V → V → Prop} {X S : Finset V} {z w : V}
    (hz : ReachAvoiding adj X S z) (hzw : adj z w) (hwS : w ∉ S) :
    ReachAvoiding adj X S w := by
  obtain ⟨p, hp, hpX, hplast, hpS⟩ := hz
  by_cases hwp : w ∈ p
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hwp
    let p' := p.take (i + 1)
    have hp' : IsPath adj p' := isPath_take hp (Nat.succ_pos i)
    refine ⟨p', hp', ?_, ?_, ?_⟩
    · rw [List.head_eq_getElem_zero]; rw [List.head_eq_getElem_zero] at hpX; simpa [p'] using hpX
    · rw [List.getLast_eq_getElem]
      have hlen : p'.length = i + 1 := by simp [p', Nat.min_eq_left (Nat.succ_le_of_lt hi)]
      simp [p', hlen]
    · intro u hu; exact hpS u (List.mem_of_mem_take hu)
  · have hdisj : List.Disjoint p [w] := by
      intro u hu hw'
      simp only [List.mem_singleton] at hw'
      subst hw'; exact hwp hu
    have hpw : IsPath adj (p ++ [w]) :=
      isPath_append hp (isPath_singleton adj w) hdisj (by simpa [hplast] using hzw)
    refine ⟨p ++ [w], hpw, ?_, ?_, ?_⟩
    · rwa [List.head_append_of_ne_nil hp.1]
    · simp
    · intro u hu
      rcases List.mem_append.mp hu with hup | huw
      · exact hpS u hup
      · simp only [List.mem_singleton] at huw; subst huw; exact hwS

/-- A path starting in `A` and staying out of `S` stays inside `A` if `A` has no outgoing edges
outside `A ∪ S`. -/
lemma path_stays_in_of_no_cross {adj : V → V → Prop} {A S : Finset V}
    (hclosed : ∀ x ∈ A, ∀ y, adj x y → y ∉ S → y ∈ A)
    {p : List V} (hp : IsPath adj p) (hhead : p.head hp.1 ∈ A)
    (havoid : ∀ w ∈ p, w ∉ S) : ∀ w ∈ p, w ∈ A := by
  induction p with
  | nil => exact absurd rfl hp.1
  | cons a t ih =>
    intro w hw
    simp only [List.head_cons] at hhead
    rcases List.mem_cons.mp hw with rfl | hwt
    · exact hhead
    · cases t with
      | nil => cases hwt
      | cons b t' =>
        have hab : adj a b := (List.isChain_cons_cons.mp hp.2.2).1
        have hbS : b ∉ S := havoid b (by simp)
        have hbA : b ∈ A := hclosed a hhead b hab hbS
        have hbt : IsPath adj (b :: t') :=
          ⟨List.cons_ne_nil _ _, (List.nodup_cons.mp hp.2.1).2, (List.isChain_cons_cons.mp hp.2.2).2⟩
        exact ih hbt hbA (fun u hu => havoid u (List.mem_cons_of_mem a hu)) w hwt

/-- Edge cardinality of an undirected graph (counting ordered adjacent pairs). -/
noncomputable def edgeCard [Fintype V] (adj : V → V → Prop) : ℕ :=
  by classical exact (Finset.univ.filter fun e : V × V => adj e.1 e.2).card

/-- Vertex-Menger's Theorem via edge-deletion induction (Göring-style). -/
theorem menger [Fintype V] [DecidableEq V] :
    ∀ m : ℕ, ∀ (adj : V → V → Prop), (∀ ⦃x y⦄, adj x y → adj y x) → (∀ x, ¬ adj x x) →
      edgeCard adj = m →
      ∀ (X Y : Finset V) (k : ℕ),
        (∀ S : Finset V, IsSep adj X Y S → k ≤ S.card) →
        ∃ (P : Fin k → List V),
          (∀ i, ∃ hp : IsPath adj (P i), (P i).head hp.1 ∈ X ∧ (P i).getLast hp.1 ∈ Y) ∧
          Pairwise fun i j => List.Disjoint (P i) (P j) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    classical
    intro adj hsym hirr hm X Y k hsep
    by_cases hedge : ∃ u w : V, adj u w
    · obtain ⟨u, w, huw⟩ := hedge
      -- Delete edge {u, w}
      let adj' : V → V → Prop := fun x y => adj x y ∧ ¬ ((x = u ∧ y = w) ∨ (x = w ∧ y = u))
      have hsym' : (∀ ⦃x y⦄, adj' x y → adj' y x) := by
        intro x y ⟨hxy, hne⟩
        exact ⟨hsym hxy, fun h => hne (by tauto)⟩
      have hirr' : (∀ x, ¬ adj' x x) := fun x h => hirr x h.1
      have hlt : edgeCard adj' < m := by
        rw [← hm]
        unfold edgeCard
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨(u, w), ?_, ?_⟩
          · simp [huw]
          · simp [adj']
        · intro e he
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
          exact he.1
      by_cases hsep' : ∀ S : Finset V, IsSep adj' X Y S → k ≤ S.card
      · obtain ⟨P, hP, hdisj⟩ := ih (edgeCard adj') hlt adj' hsym' hirr' rfl X Y k hsep'
        refine ⟨P, fun i => ?_, hdisj⟩
        obtain ⟨hp, hX, hY⟩ := hP i
        exact ⟨isPath_of_imp (fun _ _ h => h.1) hp, hX, hY⟩
      · push Not at hsep'
        obtain ⟨S, hS_sep, hS_lt⟩ := hsep'
        -- Neither u nor w can be in S, else S separates X from Y in adj
        have huS : u ∉ S := by
          intro hu
          have hS_adj : IsSep adj X Y S := by
            intro p hp hpX hpY
            by_cases hup : u ∈ p
            · exact ⟨u, hup, hu⟩
            · have hp' : IsPath adj' p := by
                refine ⟨hp.1, hp.2.1, ?_⟩
                exact isChain_imp_of_mem hp.2.2 fun x hx y hy hxy => ⟨hxy, by
                  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
                  · exact hup hx
                  · exact hup hy⟩
              exact hS_sep p hp' hpX hpY
          exact absurd (hsep S hS_adj) (not_le.mpr hS_lt)
        have hwS : w ∉ S := by
          intro hw
          have hS_adj : IsSep adj X Y S := by
            intro p hp hpX hpY
            by_cases hwp : w ∈ p
            · exact ⟨w, hwp, hw⟩
            · have hp' : IsPath adj' p := by
                refine ⟨hp.1, hp.2.1, ?_⟩
                exact isChain_imp_of_mem hp.2.2 fun x hx y hy hxy => ⟨hxy, by
                  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
                  · exact hwp hy
                  · exact hwp hx⟩
              exact hS_sep p hp' hpX hpY
          exact absurd (hsep S hS_adj) (not_le.mpr hS_lt)
        -- Define A = reachable from X in adj' avoiding S, B = (univ \ S) \ A
        let A : Finset V := Finset.univ.filter fun z => ReachAvoiding adj' X S z
        let B : Finset V := (Finset.univ \ S) \ A
        have hAS_disj : Disjoint A S := by
          rw [Finset.disjoint_left]
          intro z hzA hzS
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hzA
          obtain ⟨p, hp, _, hlast, havoid⟩ := hzA
          exact havoid z (hlast ▸ List.getLast_mem hp.1) hzS
        have hA_closed : ∀ x ∈ A, ∀ y, adj' x y → y ∉ S → y ∈ A := by
          intro x hx y hxy hyS
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact reachAvoiding_adj hx hxy hyS
        have hB_closed : ∀ y ∈ B, ∀ x, adj' y x → x ∉ S → x ∈ B := by
          intro y hy x hyx hxS
          simp only [B, Finset.mem_sdiff, Finset.mem_univ, true_and] at hy ⊢
          refine ⟨hxS, fun hxA => hy.2 ?_⟩
          exact hA_closed x hxA y (hsym' hyx) hy.1
        have hX_sub : ∀ x ∈ X, x ∈ A ∨ x ∈ S := by
          intro x hx
          by_cases hxS : x ∈ S
          · exact Or.inr hxS
          · left
            simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨[x], isPath_singleton adj' x, hx, rfl, ?_⟩
            intro z hz; simp only [List.mem_singleton] at hz; subst hz; exact hxS
        have hY_disj_A : Disjoint Y A := by
          rw [Finset.disjoint_left]
          intro y hyY hyA
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hyA
          obtain ⟨p, hp, hpX, hplast, havoid⟩ := hyA
          obtain ⟨z, hzp, hzS⟩ := hS_sep p hp hpX (hplast ▸ hyY)
          exact havoid z hzp hzS
        have hY_sub : ∀ y ∈ Y, y ∈ B ∨ y ∈ S := by
          intro y hy
          by_cases hyS : y ∈ S
          · exact Or.inr hyS
          · left
            simp only [B, Finset.mem_sdiff, Finset.mem_univ, true_and]
            exact ⟨hyS, Finset.disjoint_left.mp hY_disj_A hy⟩
        -- One of u, w is in A and the other in B!
        have huw_split : (u ∈ A ∧ w ∈ B) ∨ (w ∈ A ∧ u ∈ B) := by
          have huAB : u ∈ A ∨ u ∈ B := by
            by_cases h : u ∈ A
            · exact Or.inl h
            · right; simp [B, huS, h]
          have hwAB : w ∈ A ∨ w ∈ B := by
            by_cases h : w ∈ A
            · exact Or.inl h
            · right; simp [B, hwS, h]
          rcases huAB with huA | huB <;> rcases hwAB with hwA | hwB
          · -- Both u, w in A => A is closed under adj too, so S separates X from Y in adj!
            exfalso
            have hS_adj : IsSep adj X Y S := by
              intro p hp hpX hpY
              by_contra hnoS
              push Not at hnoS
              have hheadA : p.head hp.1 ∈ A := by
                rcases hX_sub _ hpX with h | h
                · exact h
                · exact absurd h (hnoS _ (List.head_mem hp.1))
              have hA_cl_adj : ∀ x ∈ A, ∀ y, adj x y → y ∉ S → y ∈ A := by
                intro x hx y hxy hyS
                by_cases he : (x = u ∧ y = w) ∨ (x = w ∧ y = u)
                · rcases he with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption
                · exact hA_closed x hx y ⟨hxy, he⟩ hyS
              have hlastA : p.getLast hp.1 ∈ A :=
                path_stays_in_of_no_cross hA_cl_adj hp hheadA hnoS _ (List.getLast_mem hp.1)
              exact Finset.disjoint_left.mp hY_disj_A hpY hlastA
            exact absurd (hsep S hS_adj) (not_le.mpr hS_lt)
          · exact Or.inl ⟨huA, hwB⟩
          · exact Or.inr ⟨hwA, huB⟩
          · -- Both u, w in B => A is closed under adj too!
            exfalso
            have hS_adj : IsSep adj X Y S := by
              intro p hp hpX hpY
              by_contra hnoS
              push Not at hnoS
              have hheadA : p.head hp.1 ∈ A := by
                rcases hX_sub _ hpX with h | h
                · exact h
                · exact absurd h (hnoS _ (List.head_mem hp.1))
              have hA_cl_adj : ∀ x ∈ A, ∀ y, adj x y → y ∉ S → y ∈ A := by
                intro x hx y hxy hyS
                by_cases he : (x = u ∧ y = w) ∨ (x = w ∧ y = u)
                · exfalso
                  rcases he with ⟨rfl, _⟩ | ⟨rfl, _⟩
                  · exact (Finset.mem_sdiff.mp huB).2 hx
                  · exact (Finset.mem_sdiff.mp hwB).2 hx
                · exact hA_closed x hx y ⟨hxy, he⟩ hyS
              have hlastA : p.getLast hp.1 ∈ A :=
                path_stays_in_of_no_cross hA_cl_adj hp hheadA hnoS _ (List.getLast_mem hp.1)
              exact Finset.disjoint_left.mp hY_disj_A hpY hlastA
            exact absurd (hsep S hS_adj) (not_le.mpr hS_lt)
        -- WLOG rename so u₀ ∈ A, w₀ ∈ B, adj u₀ w₀, and adj' deletes {u₀, w₀}
        obtain ⟨u₀, w₀, hu₀A, hw₀B, hu₀w₀, hadj'_eq⟩ :
            ∃ u₀ w₀, u₀ ∈ A ∧ w₀ ∈ B ∧ adj u₀ w₀ ∧
              ∀ x y, adj' x y ↔ adj x y ∧ ¬ ((x = u₀ ∧ y = w₀) ∨ (x = w₀ ∧ y = u₀)) := by
          rcases huw_split with ⟨huA, hwB⟩ | ⟨hwA, huB⟩
          · exact ⟨u, w, huA, hwB, huw, fun _ _ => Iff.rfl⟩
          · exact ⟨w, u, hwA, huB, hsym huw, fun x y => by simp [adj', or_comm]⟩
        have hu₀S : u₀ ∉ S := Finset.disjoint_left.mp hAS_disj hu₀A
        have hw₀S : w₀ ∉ S := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hw₀B).1).2
        have hw₀A : w₀ ∉ A := (Finset.mem_sdiff.mp hw₀B).2
        -- Check S ∪ {u₀} separates X from Y in adj => |S| = k - 1
        have hSu_sep : IsSep adj X Y (insert u₀ S) := by
          intro p hp hpX hpY
          by_cases hu₀p : u₀ ∈ p
          · exact ⟨u₀, hu₀p, Finset.mem_insert_self _ _⟩
          · have hp' : IsPath adj' p := by
              refine ⟨hp.1, hp.2.1, isChain_imp_of_mem hp.2.2 fun x hx y hy hxy => (hadj'_eq x y).mpr ⟨hxy, ?_⟩⟩
              rintro (⟨rfl, _⟩ | ⟨_, rfl⟩)
              · exact hu₀p hx
              · exact hu₀p hy
            obtain ⟨z, hzp, hzS⟩ := hS_sep p hp' hpX hpY
            exact ⟨z, hzp, Finset.mem_insert_of_mem hzS⟩
        have hScard_ge : k ≤ S.card + 1 := by
          have := hsep (insert u₀ S) hSu_sep
          rwa [Finset.card_insert_of_notMem hu₀S] at this
        have hSu_card : (insert u₀ S).card = k := by
          rw [Finset.card_insert_of_notMem hu₀S]; omega
        have hSw_card : (insert w₀ S).card = k := by
          rw [Finset.card_insert_of_notMem hw₀S]; omega
        -- Claim 1: Every X-(S ∪ {u₀}) separator T in adj' has card >= k
        have hsep_left : ∀ T : Finset V, IsSep adj' X (insert u₀ S) T → k ≤ T.card := by
          intro T hT
          apply hsep T
          intro p hp hpX hpY
          by_cases hheadS : p.head hp.1 ∈ S
          · obtain ⟨z, hz, hzT⟩ := hT [p.head hp.1] (isPath_singleton adj' _) hpX
              (Finset.mem_insert_of_mem hheadS)
            simp only [List.mem_singleton] at hz; subst hz
            exact ⟨p.head hp.1, List.head_mem hp.1, hzT⟩
          · -- p starts in A and ends in B ∪ S (so not in A)
            have hheadA : p.head hp.1 ∈ A := (hX_sub _ hpX).resolve_right hheadS
            have hlastNA : p.getLast hp.1 ∉ A := Finset.disjoint_left.mp hY_disj_A hpY
            have hex : ∃ i : ℕ, ∃ hi : i < p.length, p[i] ∉ A := by
              exact ⟨p.length - 1, Nat.sub_lt (List.length_pos_of_ne_nil hp.1) Nat.one_pos,
                by rwa [← List.getLast_eq_getElem]⟩
            let idx := Nat.find hex
            obtain ⟨hidx_lt, hidx_nA⟩ := Nat.find_spec hex
            have hidx_pos : 0 < idx := by
              by_contra h0
              have h0' : idx = 0 := by omega
              apply hidx_nA
              have : p[idx] = p.head hp.1 := by rw [List.head_eq_getElem_zero]; congr 1
              rwa [this]
            have hprevA : ∀ j : ℕ, (hj : j < idx) → p[j]'(lt_trans hj hidx_lt) ∈ A := by
              intro j hj
              by_contra h
              exact Nat.find_min hex hj ⟨lt_trans hj hidx_lt, h⟩
            have hprev_ne_w₀ : ∀ j : ℕ, (hj : j < idx) → p[j]'(lt_trans hj hidx_lt) ≠ w₀ := by
              intro j hj heq
              exact hw₀A (heq ▸ hprevA j hj)
            -- Check whether p[idx] ∈ S or p[idx] ∈ B
            by_cases hidxS : p[idx] ∈ S
            · -- Prefix p.take (idx + 1) is an X-(S ∪ {u₀}) path in adj'!
              let q := p.take (idx + 1)
              have hq_adj : IsPath adj q := isPath_take hp (Nat.succ_pos idx)
              have hq_len : q.length = idx + 1 := by simp only [q, List.length_take]; omega
              have hq_ne_w₀ : w₀ ∉ q := by
                intro hwq
                obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem hwq
                rw [List.getElem_take] at hjw
                have hjle : j ≤ idx := by omega
                rcases eq_or_lt_of_le hjle with rfl | hjlt
                · exact hw₀S (hjw ▸ hidxS)
                · exact hprev_ne_w₀ j hjlt hjw
              have hq' : IsPath adj' q := by
                refine ⟨hq_adj.1, hq_adj.2.1, isChain_imp_of_mem hq_adj.2.2 fun x hx y hy hxy =>
                  (hadj'_eq x y).mpr ⟨hxy, ?_⟩⟩
                rintro (⟨_, rfl⟩ | ⟨rfl, _⟩)
                · exact hq_ne_w₀ hy
                · exact hq_ne_w₀ hx
              have hq_head : q.head hq'.1 ∈ X := by
                rw [List.head_eq_getElem_zero]; rw [List.head_eq_getElem_zero] at hpX; simpa [q] using hpX
              have hq_last : q.getLast hq'.1 ∈ insert u₀ S := by
                rw [List.getLast_eq_getElem]
                have : q[q.length - 1] = p[idx] := by simp [q, hq_len]
                rw [this]; exact Finset.mem_insert_of_mem hidxS
              obtain ⟨z, hzq, hzT⟩ := hT q hq' hq_head hq_last
              exact ⟨z, List.mem_of_mem_take hzq, hzT⟩
            · -- p[idx] ∉ A and p[idx] ∉ S, so edge (p[idx-1], p[idx]) MUST be (u₀, w₀)!
              have hadj_step : adj (p[idx - 1]'(by omega)) (p[idx]'hidx_lt) := by
                have := List.isChain_iff_getElem.mp hp.2.2 (idx - 1) (by omega)
                simpa [Nat.sub_add_cancel hidx_pos] using this
              have hprev_in_A : p[idx - 1]'(by omega) ∈ A := hprevA (idx - 1) (by omega)
              have hnot_adj' : ¬ adj' (p[idx - 1]'(by omega)) (p[idx]'hidx_lt) := by
                intro h'
                exact hidx_nA (hA_closed _ hprev_in_A _ h' hidxS)
              have hprev_eq_u₀ : p[idx - 1]'(by omega) = u₀ := by
                have hcross : (p[idx - 1]'(by omega) = u₀ ∧ p[idx] = w₀) ∨
                    (p[idx - 1]'(by omega) = w₀ ∧ p[idx] = u₀) := by
                  by_contra h
                  exact hnot_adj' ((hadj'_eq _ _).mpr ⟨hadj_step, h⟩)
                rcases hcross with ⟨h1, _⟩ | ⟨h1, _⟩
                · exact h1
                · exact absurd h1 (hprev_ne_w₀ (idx - 1) (by omega))
              let q := p.take idx
              have hq_adj : IsPath adj q := isPath_take hp hidx_pos
              have hq_len : q.length = idx := by simp only [q, List.length_take]; omega
              have hq_ne_w₀ : w₀ ∉ q := by
                intro hwq
                obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem hwq
                rw [List.getElem_take] at hjw
                exact hprev_ne_w₀ j (by omega) hjw
              have hq' : IsPath adj' q := by
                refine ⟨hq_adj.1, hq_adj.2.1, isChain_imp_of_mem hq_adj.2.2 fun x hx y hy hxy =>
                  (hadj'_eq x y).mpr ⟨hxy, ?_⟩⟩
                rintro (⟨_, rfl⟩ | ⟨rfl, _⟩)
                · exact hq_ne_w₀ hy
                · exact hq_ne_w₀ hx
              have hq_head : q.head hq'.1 ∈ X := by
                rw [List.head_eq_getElem_zero]; rw [List.head_eq_getElem_zero] at hpX; simpa [q] using hpX
              have hq_last : q.getLast hq'.1 ∈ insert u₀ S := by
                rw [List.getLast_eq_getElem]
                have : q[q.length - 1] = p[idx - 1]'(by omega) := by simp [q, hq_len]
                rw [this, hprev_eq_u₀]; exact Finset.mem_insert_self _ _
              obtain ⟨z, hzq, hzT⟩ := hT q hq' hq_head hq_last
              exact ⟨z, List.mem_of_mem_take hzq, hzT⟩
        -- Claim 2: Symmetrically, every (S ∪ {w₀})-Y separator T in adj' has card >= k
        have hsep_right : ∀ T : Finset V, IsSep adj' (insert w₀ S) Y T → k ≤ T.card := by
          intro T hT
          apply hsep T
          intro p hp hpX hpY
          -- Reverse p so it goes from Y to X!
          let pr := p.reverse
          have hpr : IsPath adj pr := isPath_reverse hsym hp
          have hpr_headY : pr.head hpr.1 ∈ Y := by rwa [List.head_reverse]
          have hpr_lastX : pr.getLast hpr.1 ∈ X := by rwa [List.getLast_reverse]
          have hX_disj_B : Disjoint X B := by
            rw [Finset.disjoint_left]
            intro x hxX hxB
            rcases hX_sub x hxX with hxA | hxS
            · exact (Finset.mem_sdiff.mp hxB).2 hxA
            · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxB).1).2 hxS
          by_cases hheadS : pr.head hpr.1 ∈ S
          · obtain ⟨z, hz, hzT⟩ := hT [pr.head hpr.1] (isPath_singleton adj' _)
              (Finset.mem_insert_of_mem hheadS) hpr_headY
            simp only [List.mem_singleton] at hz; subst hz
            exact ⟨pr.head hpr.1, List.mem_reverse.mp (List.head_mem hpr.1), hzT⟩
          · have hheadB : pr.head hpr.1 ∈ B := (hY_sub _ hpr_headY).resolve_right hheadS
            have hlastNB : pr.getLast hpr.1 ∉ B := Finset.disjoint_left.mp hX_disj_B hpr_lastX
            have hex : ∃ i : ℕ, ∃ hi : i < pr.length, pr[i] ∉ B :=
              ⟨pr.length - 1, Nat.sub_lt (List.length_pos_of_ne_nil hpr.1) Nat.one_pos,
                by rwa [← List.getLast_eq_getElem]⟩
            let idx := Nat.find hex
            obtain ⟨hidx_lt, hidx_nB⟩ := Nat.find_spec hex
            have hidx_pos : 0 < idx := by
              by_contra h0
              have h0' : idx = 0 := by omega
              apply hidx_nB
              have : pr[idx] = pr.head hpr.1 := by rw [List.head_eq_getElem_zero]; congr 1
              rwa [this]
            have hprevB : ∀ j : ℕ, (hj : j < idx) → pr[j]'(lt_trans hj hidx_lt) ∈ B := by
              intro j hj
              by_contra h
              exact Nat.find_min hex hj ⟨lt_trans hj hidx_lt, h⟩
            have hprev_ne_u₀ : ∀ j : ℕ, (hj : j < idx) → pr[j]'(lt_trans hj hidx_lt) ≠ u₀ := by
              intro j hj heq
              exact (Finset.mem_sdiff.mp (heq ▸ hprevB j hj)).2 hu₀A
            by_cases hidxS : pr[idx] ∈ S
            · let q := (pr.take (idx + 1)).reverse
              have hq0 : IsPath adj (pr.take (idx + 1)) := isPath_take hpr (Nat.succ_pos idx)
              have hq0_len : (pr.take (idx + 1)).length = idx + 1 := by simp only [List.length_take]; omega
              have hq0_ne_u₀ : u₀ ∉ pr.take (idx + 1) := by
                intro huq
                obtain ⟨j, hj, hju⟩ := List.getElem_of_mem huq
                rw [List.getElem_take] at hju
                have hjle : j ≤ idx := by omega
                rcases eq_or_lt_of_le hjle with rfl | hjlt
                · exact hu₀S (hju ▸ hidxS)
                · exact hprev_ne_u₀ j hjlt hju
              have hq_adj : IsPath adj q := isPath_reverse hsym hq0
              have hq_ne_u₀ : u₀ ∉ q := fun h => hq0_ne_u₀ (List.mem_reverse.mp h)
              have hq' : IsPath adj' q := by
                refine ⟨hq_adj.1, hq_adj.2.1, isChain_imp_of_mem hq_adj.2.2 fun x hx y hy hxy =>
                  (hadj'_eq x y).mpr ⟨hxy, ?_⟩⟩
                rintro (⟨rfl, _⟩ | ⟨_, rfl⟩)
                · exact hq_ne_u₀ hx
                · exact hq_ne_u₀ hy
              have hq_head : q.head hq'.1 ∈ insert w₀ S := by
                rw [List.head_reverse, List.getLast_eq_getElem]
                have : (pr.take (idx + 1))[(pr.take (idx + 1)).length - 1] = pr[idx] := by
                  simp [hq0_len]
                rw [this]; exact Finset.mem_insert_of_mem hidxS
              have hq_last : q.getLast hq'.1 ∈ Y := by
                rw [List.getLast_reverse, List.head_eq_getElem_zero]
                rw [List.head_eq_getElem_zero] at hpr_headY
                simpa using hpr_headY
              obtain ⟨z, hzq, hzT⟩ := hT q hq' hq_head hq_last
              exact ⟨z, List.mem_reverse.mp (List.mem_of_mem_take (List.mem_reverse.mp hzq)), hzT⟩
            · have hadj_step : adj (pr[idx - 1]'(by omega)) (pr[idx]'hidx_lt) := by
                have := List.isChain_iff_getElem.mp hpr.2.2 (idx - 1) (by omega)
                simpa [Nat.sub_add_cancel hidx_pos] using this
              have hprev_in_B : pr[idx - 1]'(by omega) ∈ B := hprevB (idx - 1) (by omega)
              have hnot_adj' : ¬ adj' (pr[idx - 1]'(by omega)) (pr[idx]'hidx_lt) := by
                intro h'
                exact hidx_nB (hB_closed _ hprev_in_B _ h' hidxS)
              have hprev_eq_w₀ : pr[idx - 1]'(by omega) = w₀ := by
                have hcross : (pr[idx - 1]'(by omega) = u₀ ∧ pr[idx] = w₀) ∨
                    (pr[idx - 1]'(by omega) = w₀ ∧ pr[idx] = u₀) := by
                  by_contra h
                  exact hnot_adj' ((hadj'_eq _ _).mpr ⟨hadj_step, h⟩)
                rcases hcross with ⟨h1, _⟩ | ⟨h1, _⟩
                · exact absurd h1 (hprev_ne_u₀ (idx - 1) (by omega))
                · exact h1
              let q := (pr.take idx).reverse
              have hq0 : IsPath adj (pr.take idx) := isPath_take hpr hidx_pos
              have hq0_len : (pr.take idx).length = idx := by simp only [List.length_take]; omega
              have hq0_ne_u₀ : u₀ ∉ pr.take idx := by
                intro huq
                obtain ⟨j, hj, hju⟩ := List.getElem_of_mem huq
                rw [List.getElem_take] at hju
                exact hprev_ne_u₀ j (by omega) hju
              have hq_adj : IsPath adj q := isPath_reverse hsym hq0
              have hq_ne_u₀ : u₀ ∉ q := fun h => hq0_ne_u₀ (List.mem_reverse.mp h)
              have hq' : IsPath adj' q := by
                refine ⟨hq_adj.1, hq_adj.2.1, isChain_imp_of_mem hq_adj.2.2 fun x hx y hy hxy =>
                  (hadj'_eq x y).mpr ⟨hxy, ?_⟩⟩
                rintro (⟨rfl, _⟩ | ⟨_, rfl⟩)
                · exact hq_ne_u₀ hx
                · exact hq_ne_u₀ hy
              have hq_head : q.head hq'.1 ∈ insert w₀ S := by
                rw [List.head_reverse, List.getLast_eq_getElem]
                have : (pr.take idx)[(pr.take idx).length - 1] = pr[idx - 1]'(by omega) := by
                  simp [hq0_len]
                rw [this, hprev_eq_w₀]; exact Finset.mem_insert_self _ _
              have hq_last : q.getLast hq'.1 ∈ Y := by
                rw [List.getLast_reverse, List.head_eq_getElem_zero]
                rw [List.head_eq_getElem_zero] at hpr_headY
                simpa using hpr_headY
              obtain ⟨z, hzq, hzT⟩ := hT q hq' hq_head hq_last
              exact ⟨z, List.mem_reverse.mp (List.mem_of_mem_take (List.mem_reverse.mp hzq)), hzT⟩
        -- Apply IH to both sides in adj'!
        obtain ⟨P₀, hP₀, hP₀_disj⟩ :=
          ih (edgeCard adj') hlt adj' hsym' hirr' rfl X (insert u₀ S) k hsep_left
        obtain ⟨Q₀, hQ₀, hQ₀_disj⟩ :=
          ih (edgeCard adj') hlt adj' hsym' hirr' rfl (insert w₀ S) Y k hsep_right
        -- Truncate each P₀ i at first hit of insert u₀ S, and each Q₀ j at last hit of insert w₀ S
        have hP_tr : ∀ i : Fin k, ∃ p', ∃ hp' : IsPath adj' p', p'.head hp'.1 ∈ X ∧
            p'.getLast hp'.1 ∈ insert u₀ S ∧ (∀ z ∈ p', z ∈ P₀ i) ∧
            (∀ z ∈ p'.dropLast, z ∉ insert u₀ S) := by
          intro i
          obtain ⟨hp, hX, hSu⟩ := hP₀ i
          obtain ⟨p', hp', hhd, hlt', hsub, havoid⟩ :=
            exists_prefix_first_mem hp ⟨(P₀ i).getLast hp.1, List.getLast_mem hp.1, hSu⟩
          exact ⟨p', hp', hhd.symm ▸ hX, hlt', hsub, havoid⟩
        have hQ_tr : ∀ j : Fin k, ∃ q', ∃ hq' : IsPath adj' q', q'.head hq'.1 ∈ insert w₀ S ∧
            q'.getLast hq'.1 ∈ Y ∧ (∀ z ∈ q', z ∈ Q₀ j) ∧
            (∀ z ∈ q'.tail, z ∉ insert w₀ S) := by
          intro j
          obtain ⟨hq, hSw, hY⟩ := hQ₀ j
          obtain ⟨q', hq', hhd, hlt', hsub, havoid⟩ :=
            exists_suffix_last_mem hsym' hq ⟨(Q₀ j).head hq.1, List.head_mem hq.1, hSw⟩
          exact ⟨q', hq', hhd, hlt'.symm ▸ hY, hsub, havoid⟩
        choose P hP_path hP_X hP_end hP_sub hP_avoid using hP_tr
        choose Q hQ_path hQ_start hQ_Y hQ_sub hQ_avoid using hQ_tr
        -- Truncated P i has every vertex in A ∪ {endpoint}, and every dropLast vertex in A!
        have hP_in_A : ∀ i : Fin k, ∀ z ∈ (P i).dropLast, z ∈ A := by
          intro i z hz
          have hne : (P i).dropLast ≠ [] := List.ne_nil_of_mem hz
          have hdl_path : IsPath adj' (P i).dropLast := by
            have hpos : 0 < (P i).length - 1 := by
              have := List.length_pos_of_ne_nil hne; rwa [List.length_dropLast] at this
            rw [List.dropLast_eq_take]; exact isPath_take (hP_path i) hpos
          have hdl_head : (P i).dropLast.head hdl_path.1 ∈ A := by
            have hhead_eq : (P i).dropLast.head hdl_path.1 = (P i).head (hP_path i).1 := by
              rw [List.head_eq_getElem_zero, List.head_eq_getElem_zero, List.getElem_dropLast]
            rw [hhead_eq]
            rcases hX_sub _ (hP_X i) with hA | hS
            · exact hA
            · exfalso
              exact hP_avoid i _ (hhead_eq ▸ List.head_mem hdl_path.1) (Finset.mem_insert_of_mem hS)
          exact path_stays_in_of_no_cross hA_closed hdl_path hdl_head
            (fun w hw hwS => hP_avoid i w hw (Finset.mem_insert_of_mem hwS)) z hz
        -- Truncated Q j has every tail vertex in B!
        have hQ_in_B : ∀ j : Fin k, ∀ z ∈ (Q j).tail, z ∈ B := by
          intro j z hz
          have hne : (Q j).tail ≠ [] := List.ne_nil_of_mem hz
          have htl_path : IsPath adj' (Q j).tail := by
            have hlt1 : 1 < (Q j).length := by
              cases hq : Q j with
              | nil => simp [hq] at hne
              | cons _ t =>
                cases t with
                | nil => simp [hq] at hne
                | cons _ _ => simp
            have := isPath_drop (hQ_path j) hlt1
            rwa [List.drop_one] at this
          have hrev_path : IsPath adj' (Q j).tail.reverse := isPath_reverse hsym' htl_path
          have hrev_head : (Q j).tail.reverse.head hrev_path.1 ∈ B := by
            rw [List.head_reverse]
            have hlast_eq : (Q j).tail.getLast htl_path.1 = (Q j).getLast (hQ_path j).1 := getLast_tail_eq (hQ_path j).1 htl_path.1
            rw [hlast_eq]
            rcases hY_sub _ (hQ_Y j) with hB | hS
            · exact hB
            · exfalso
              exact hQ_avoid j _ (hlast_eq ▸ List.getLast_mem htl_path.1) (Finset.mem_insert_of_mem hS)
          exact path_stays_in_of_no_cross hB_closed hrev_path hrev_head
            (fun w hw hwS => hQ_avoid j w (List.mem_reverse.mp hw) (Finset.mem_insert_of_mem hwS))
            z (List.mem_reverse.mpr hz)
        -- Endpoints of P give a bijection Fin k ≃ insert u₀ S; startpoints of Q give Fin k ≃ insert w₀ S
        have hP_disj : Pairwise fun i j => List.Disjoint (P i) (P j) := by
          intro i j hij z hzi hzj
          exact hP₀_disj hij (hP_sub i z hzi) (hP_sub j z hzj)
        have hQ_disj : Pairwise fun i j => List.Disjoint (Q i) (Q j) := by
          intro i j hij z hzi hzj
          exact hQ₀_disj hij (hQ_sub i z hzi) (hQ_sub j z hzj)
        let fP : Fin k → ↥(insert u₀ S) := fun i => ⟨(P i).getLast (hP_path i).1, hP_end i⟩
        let fQ : Fin k → ↥(insert w₀ S) := fun j => ⟨(Q j).head (hQ_path j).1, hQ_start j⟩
        have hfP_inj : Function.Injective fP := by
          intro i j hij
          by_contra hne
          have hval : (P i).getLast (hP_path i).1 = (P j).getLast (hP_path j).1 := congrArg Subtype.val hij
          exact hP_disj hne (List.getLast_mem (hP_path i).1) (hval ▸ List.getLast_mem (hP_path j).1)
        have hfQ_inj : Function.Injective fQ := by
          intro i j hij
          by_contra hne
          have hval : (Q i).head (hQ_path i).1 = (Q j).head (hQ_path j).1 := congrArg Subtype.val hij
          exact hQ_disj hne (List.head_mem (hQ_path i).1) (hval ▸ List.head_mem (hQ_path j).1)
        have hfP_bij : Function.Bijective fP :=
          (Fintype.bijective_iff_injective_and_card fP).mpr ⟨hfP_inj, by simp only [Fintype.card_fin, Fintype.card_coe, hSu_card]⟩
        have hfQ_bij : Function.Bijective fQ :=
          (Fintype.bijective_iff_injective_and_card fQ).mpr ⟨hfQ_inj, by simp only [Fintype.card_fin, Fintype.card_coe, hSw_card]⟩
        -- Map each i : Fin k to the matching j = matchQ i : Fin k
        let eQ := Equiv.ofBijective fQ hfQ_bij
        let matchElem : ↥(insert u₀ S) → ↥(insert w₀ S) := fun x =>
          if h : x.1 = u₀ then ⟨w₀, Finset.mem_insert_self _ _⟩
          else ⟨x.1, Finset.mem_insert_of_mem ((Finset.mem_insert.mp x.2).resolve_left h)⟩
        have hmatch_inj : Function.Injective matchElem := by
          intro x y hxy
          ext
          dsimp [matchElem] at hxy
          split_ifs at hxy with hx hy hy
          · exact hx.trans hy.symm
          · exfalso
            have hyS : y.1 ∈ S := (Finset.mem_insert.mp y.2).resolve_left hy
            have : w₀ = y.1 := congrArg Subtype.val hxy
            exact hw₀S (this ▸ hyS)
          · exfalso
            have hxS : x.1 ∈ S := (Finset.mem_insert.mp x.2).resolve_left hx
            have : x.1 = w₀ := congrArg Subtype.val hxy
            exact hw₀S (this ▸ hxS)
          · simpa using congrArg Subtype.val hxy
        let matchQ : Fin k → Fin k := fun i => eQ.symm (matchElem (fP i))
        have hmatchQ_inj : Function.Injective matchQ :=
          eQ.symm.injective.comp (hmatch_inj.comp hfP_inj)
        -- Helper: P i ⊆ A ∪ S (actually every vertex of P i is in A or = last ∈ S ∪ {u₀})
        have hP_mem_AS : ∀ i z, z ∈ P i → z ∈ A ∨ z = (P i).getLast (hP_path i).1 := by
          intro i z hz
          have hsplit := List.dropLast_append_getLast (hP_path i).1
          rw [← hsplit, List.mem_append, List.mem_singleton] at hz
          rcases hz with hdl | rfl
          · exact Or.inl (hP_in_A i z hdl)
          · exact Or.inr rfl
        have hP_all_notB : ∀ i z, z ∈ P i → z ∉ B := by
          intro i z hz hzB
          rcases hP_mem_AS i z hz with hzA | rfl
          · exact (Finset.mem_sdiff.mp hzB).2 hzA
          · rcases Finset.mem_insert.mp (hP_end i) with heq | hzS
            · exact (Finset.mem_sdiff.mp hzB).2 (heq ▸ hu₀A)
            · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hzB).1).2 hzS
        -- Build glued path R i
        let R : Fin k → List V := fun i =>
          if (P i).getLast (hP_path i).1 = u₀ then P i ++ Q (matchQ i)
          else P i ++ (Q (matchQ i)).tail
        refine ⟨R, ?_, ?_⟩
        · intro i
          have hPi : IsPath adj (P i) := isPath_of_imp (fun _ _ h => h.1) (hP_path i)
          have hQi : IsPath adj (Q (matchQ i)) := isPath_of_imp (fun _ _ h => h.1) (hQ_path (matchQ i))
          have hQhead_val : (Q (matchQ i)).head (hQ_path (matchQ i)).1 = (matchElem (fP i)).1 := by
            have := eQ.apply_symm_apply (matchElem (fP i))
            exact congrArg Subtype.val this
          dsimp only [R]
          split_ifs with hiu
          · -- Glue across edge (u₀, w₀)
            have hQw : (Q (matchQ i)).head hQi.1 = w₀ := by
              rw [hQhead_val]; simp [matchElem, fP, hiu]
            have hdisjPQ : List.Disjoint (P i) (Q (matchQ i)) := by
              intro z hzP hzQ
              cases hq : Q (matchQ i) with
              | nil => exact absurd hq hQi.1
              | cons a t =>
                have ha : a = w₀ := by simpa [hq] using hQw
                rw [hq, List.mem_cons] at hzQ
                rcases hzQ with rfl | hzt
                · exact hP_all_notB i z hzP (ha ▸ hw₀B)
                · exact hP_all_notB i z hzP (hQ_in_B (matchQ i) z (by simpa [hq] using hzt))
            have hR : IsPath adj (P i ++ Q (matchQ i)) :=
              isPath_append hPi hQi hdisjPQ (by rw [hiu, hQw]; exact hu₀w₀)
            refine ⟨hR, ?_, ?_⟩
            · rw [List.head_append_of_ne_nil hPi.1]; exact hP_X i
            · rw [List.getLast_append_of_ne_nil _ hQi.1]; exact hQ_Y (matchQ i)
          · -- Glue at shared vertex s ∈ S
            have hQs : (Q (matchQ i)).head hQi.1 = (P i).getLast hPi.1 := by
              rw [hQhead_val]; simp [matchElem, fP, hiu]
            have hdisjPQ : List.Disjoint (P i) (Q (matchQ i)).tail := by
              intro z hzP hzQt
              exact hP_all_notB i z hzP (hQ_in_B (matchQ i) z hzQt)
            have hR : IsPath adj (P i ++ (Q (matchQ i)).tail) :=
              isPath_glue hPi hQi hQs.symm hdisjPQ
            refine ⟨hR, ?_, ?_⟩
            · rw [List.head_append_of_ne_nil hPi.1]; exact hP_X i
            · rw [getLast_append_tail hPi.1 hQi.1 hQs.symm]; exact hQ_Y (matchQ i)
        · -- Pairwise disjointness of R i and R j
          intro i j hij z hzi hzj
          have hR_sub : ∀ l, ∀ w ∈ R l, w ∈ P l ∨ w ∈ Q (matchQ l) := by
            intro l w hw
            dsimp only [R] at hw
            split_ifs at hw
            · exact List.mem_append.mp hw
            · rcases List.mem_append.mp hw with h | h
              · exact Or.inl h
              · exact Or.inr (List.mem_of_mem_tail h)
          -- Also note any w ∈ Q (matchQ l) \ {head} is in B, and head is w₀ ∈ B or = P l.last!
          have hQ_not_P : ∀ l₁ l₂, l₁ ≠ l₂ → ∀ w, w ∈ P l₁ → w ∈ Q (matchQ l₂) → False := by
            intro l₁ l₂ hne w hwP hwQ
            cases hq : Q (matchQ l₂) with
            | nil => exact absurd hq (hQ_path (matchQ l₂)).1
            | cons a t =>
              rw [hq, List.mem_cons] at hwQ
              rcases hwQ with rfl | hwt
              · have hQhead_val : w = (matchElem (fP l₂)).1 := by
                  have := eQ.apply_symm_apply (matchElem (fP l₂))
                  have h1 : (Q (matchQ l₂)).head (hQ_path (matchQ l₂)).1 = (matchElem (fP l₂)).1 :=
                    congrArg Subtype.val this
                  simpa [hq] using h1
                dsimp [matchElem, fP] at hQhead_val
                split_ifs at hQhead_val with hl₂u
                · exact hP_all_notB l₁ w hwP (hQhead_val ▸ hw₀B)
                · exact hP_disj hne hwP (hQhead_val ▸ List.getLast_mem (hP_path l₂).1)
              · exact hP_all_notB l₁ w hwP (hQ_in_B (matchQ l₂) w (by simpa [hq] using hwt))
          rcases hR_sub i z hzi with hziP | hziQ <;> rcases hR_sub j z hzj with hzjP | hzjQ
          · exact hP_disj hij hziP hzjP
          · exact hQ_not_P i j hij z hziP hzjQ
          · exact hQ_not_P j i hij.symm z hzjP hziQ
          · exact hQ_disj (fun h => hij (hmatchQ_inj h)) hziQ hzjQ
    · -- Base case: no edges at all! X ∩ Y is a separator, so k ≤ |X ∩ Y|.
      push Not at hedge
      have hXY_sep : IsSep adj X Y (X ∩ Y) := by
        intro p hp hpX hpY
        cases p with
        | nil => exact absurd rfl hp.1
        | cons a t =>
          cases t with
          | nil =>
            simp only [List.head_cons, List.getLast_singleton] at hpX hpY
            exact ⟨a, List.mem_cons_self, Finset.mem_inter.mpr ⟨hpX, hpY⟩⟩
          | cons b t' =>
            exact absurd (List.isChain_cons_cons.mp hp.2.2).1 (hedge a b)
      have hk_le : k ≤ (X ∩ Y).card := hsep (X ∩ Y) hXY_sep
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hk_le
      let eT : Fin k ≃ ↥T := (Fintype.equivFinOfCardEq (by simp [hTcard])).symm
      refine ⟨fun i => [(eT i).1], fun i => ?_, ?_⟩
      · have hmem : (eT i).1 ∈ X ∩ Y := hTsub (eT i).2
        exact ⟨isPath_singleton adj _, (Finset.mem_inter.mp hmem).1, (Finset.mem_inter.mp hmem).2⟩
      · intro i j hij z hzi hzj
        simp only [List.mem_singleton] at hzi hzj
        have : eT i = eT j := Subtype.ext (hzi.symm.trans hzj)
        exact hij (eT.injective this)

/-- Helper: cyclic indexing on a list. -/
def cycNext {α : Type*} (cyc : List α) (i : Fin cyc.length) : α :=
  cyc[(i.val + 1) % cyc.length]'(Nat.mod_lt _ (Nat.pos_of_ne_zero (by intro h; exact Fin.elim0 (h ▸ i))))

lemma isCycle_rotate {adj : V → V → Prop} {cyc : List V} (hc : IsCycle adj cyc) (r : ℕ) :
    IsCycle adj (cyc.rotate r) := by
  have hlen : (cyc.rotate r).length = cyc.length := List.length_rotate cyc r
  have hc3 : 3 ≤ cyc.length := hc.1
  refine ⟨by omega, List.nodup_rotate.mpr hc.2.1, fun i => ?_⟩
  have hpos : 0 < cyc.length := by omega
  have hi1 : (cyc.rotate r)[i] = cyc[(i.val + r) % cyc.length]'(Nat.mod_lt _ hpos) := by
    simp [List.getElem_rotate]
  have hi2 : (cyc.rotate r)[(i.val + 1) % (cyc.rotate r).length]'(Nat.mod_lt _ (by omega)) =
      cyc[(((i.val + r) % cyc.length) + 1) % cyc.length]'(Nat.mod_lt _ hpos) := by
    rw [List.getElem_rotate]
    congr 1
    simp only [hlen]
    rw [Nat.add_mod ((i.val + 1) % cyc.length), Nat.mod_mod, ← Nat.add_mod]
    rw [Nat.add_mod ((i.val + r) % cyc.length), Nat.mod_mod, ← Nat.add_mod]
    congr 1; omega
  rw [hi1, hi2]
  exact hc.2.2 ⟨(i.val + r) % cyc.length, Nat.mod_lt _ hpos⟩

lemma isCycle_of_isPath_and_adj {adj : V → V → Prop} {cyc : List V}
    (hlen : 3 ≤ cyc.length) (hp : IsPath adj cyc)
    (hclose : adj (cyc.getLast hp.1) (cyc.head hp.1)) : IsCycle adj cyc := by
  refine ⟨hlen, hp.2.1, fun i => ?_⟩
  by_cases hi : i.val + 1 < cyc.length
  · have hmod : (i.val + 1) % cyc.length = i.val + 1 := Nat.mod_eq_of_lt hi
    simp only [hmod]
    exact List.isChain_iff_getElem.mp hp.2.2 i.val hi
  · have hieq : i.val = cyc.length - 1 := by omega
    have hmod : (i.val + 1) % cyc.length = 0 := by
      rw [hieq, Nat.sub_add_cancel (by omega), Nat.mod_self]
    simp only [hmod]
    have h1 : cyc[i] = cyc.getLast hp.1 := by rw [List.getLast_eq_getElem]; simp [hieq]
    have h2 : cyc[0]'(by omega) = cyc.head hp.1 := (List.head_eq_getElem_zero hp.1).symm
    rw [h1, h2]
    exact hclose

/-- Chvátal–Erdős Theorem (1972): if `|V| ≥ 3` and `G` has no vertex cut `(S, A, B)`
with `|S| < |I|` for some independent set `I`, then `G` has a Hamiltonian cycle. -/
theorem chvatal_erdos [Fintype V] [DecidableEq V] (adj : V → V → Prop) (hsym : (∀ ⦃x y⦄, adj x y → adj y x)) (hirr : (∀ x, ¬ adj x x))
    (hn : 3 ≤ Fintype.card V)
    (hno : ∀ (S A B I : Finset V),
      Disjoint S A → Disjoint S B → Disjoint A B →
      S ∪ A ∪ B = Finset.univ → A.Nonempty → B.Nonempty →
      (∀ x ∈ A, ∀ y ∈ B, ¬ adj x y) →
      (∀ x ∈ I, ∀ y ∈ I, ¬ adj x y) →
      I.card ≤ S.card) :
    ∃ a : Fin (Fintype.card V) ≃ V,
      ∀ i : Fin (Fintype.card V),
        adj (a i) (a ⟨(i.val + 1) % Fintype.card V, Nat.mod_lt _ (by omega)⟩) := by
  classical
  -- First handle complete graph directly!
  by_cases hcomp : ∀ x y : V, x ≠ y → adj x y
  · let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
    refine ⟨e, fun i => hcomp _ _ fun h => ?_⟩
    have := e.injective h
    have hv : i.val = (i.val + 1) % Fintype.card V := congrArg Fin.val this
    by_cases hlt : i.val + 1 < Fintype.card V
    · rw [Nat.mod_eq_of_lt hlt] at hv; omega
    · have : i.val + 1 = Fintype.card V := by omega
      rw [this, Nat.mod_self] at hv; omega
  -- Not complete => there exists an independent set of size 2 => minimum degree >= 2!
  push Not at hcomp
  obtain ⟨u₀, v₀, huv_ne, huv_nadj⟩ := hcomp
  have hind2 : ∀ x ∈ ({u₀, v₀} : Finset V), ∀ y ∈ ({u₀, v₀} : Finset V), ¬ adj x y := by
    intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact hirr _
    · exact huv_nadj
    · exact fun h => huv_nadj (hsym h)
    · exact hirr _
  have hcard2 : ({u₀, v₀} : Finset V).card = 2 := Finset.card_pair huv_ne
  have hdeg2 : ∀ x : V, 2 ≤ (Finset.univ.filter fun y => adj x y).card := by
    intro x
    by_contra hlt
    push Not at hlt
    let S := Finset.univ.filter fun y => adj x y
    let A : Finset V := {x}
    let B : Finset V := (Finset.univ \ S) \ A
    have hxS : x ∉ S := by simp [S, hirr x]
    have hBcard : 0 < B.card := by
      have hSA : (S ∪ A).card ≤ S.card + 1 := by
        simpa [A, Finset.card_singleton] using Finset.card_union_le S A
      have h2 : B = Finset.univ \ (S ∪ A) := by ext z; simp [B, A]; tauto
      rw [h2, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
      have hSc : S.card < 2 := hlt
      omega
    have hle := hno S A B {u₀, v₀}
      (Finset.disjoint_singleton_right.mpr hxS)
      (by rw [Finset.disjoint_left]; intro z hzS hzB; exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hzB).1).2 hzS)
      (by rw [Finset.disjoint_left]; intro z hzA hzB; exact (Finset.mem_sdiff.mp hzB).2 hzA)
      (by ext z; simp [B, A]; tauto)
      ⟨x, Finset.mem_singleton_self x⟩
      (Finset.card_pos.mp hBcard)
      (by intro a ha b hb hadj; simp only [A, Finset.mem_singleton] at ha; subst ha
          exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hb).1).2 (by simp [S, hadj]))
      hind2
    have hSc : S.card < 2 := hlt; rw [hcard2] at hle; omega
  -- Existence of at least one simple cycle of length >= 3 (from a longest simple path)
  have hex_cycle : ∃ c : List V, IsCycle adj c := by
    -- Pick a path of maximum length
    have hex_len : ∃ l : ℕ, ∃ p : List V, IsPath adj p ∧ p.length = l :=
      ⟨1, [u₀], isPath_singleton adj u₀, rfl⟩
    have hbound : ∀ l, (∃ p : List V, IsPath adj p ∧ p.length = l) → l ≤ Fintype.card V := by
      rintro l ⟨p, hp, rfl⟩
      exact hp.2.1.length_le_card
    -- Use Finset.max' on lengths of paths? Even simpler: Nat.findGreatest!
    let P_pred : ℕ → Prop := fun l => ∃ p : List V, IsPath adj p ∧ p.length = l
    let L := Nat.findGreatest P_pred (Fintype.card V)
    have hL_spec : P_pred L := Nat.findGreatest_spec (m := 1) (by omega) ⟨[u₀], isPath_singleton adj u₀, rfl⟩
    obtain ⟨p, hp, hpL⟩ := hL_spec
    -- Every neighbor of p.head lies in p!
    let x := p.head hp.1
    have hN_sub : ∀ y, adj x y → y ∈ p := by
      intro y hxy
      by_contra hyp
      have hy_path : IsPath adj (y :: p) := by
        refine ⟨List.cons_ne_nil _ _, List.nodup_cons.mpr ⟨hyp, hp.2.1⟩, ?_⟩
        cases hp_eq : p with
        | nil => exact absurd hp_eq hp.1
        | cons a t =>
          have hax : a = x := by simp [x, hp_eq]
          exact List.isChain_cons_cons.mpr ⟨hsym (hax ▸ hxy), hp_eq ▸ hp.2.2⟩
      have hle : (y :: p).length ≤ L :=
        Nat.le_findGreatest (hy_path.2.1.length_le_card) ⟨y :: p, hy_path, rfl⟩
      simp [hpL] at hle
    -- Since deg(x) >= 2 and x = p[0] is not adjacent to itself, x has a neighbor p[j] with j >= 2!
    have hN_card := hdeg2 x
    let N := Finset.univ.filter fun y => adj x y
    have hlen_ge : 3 ≤ p.length := by
      have hsub : insert x N ⊆ p.toFinset := by
        intro y hy
        rw [List.mem_toFinset]
        rcases Finset.mem_insert.mp hy with rfl | hyN
        · exact List.head_mem hp.1
        · exact hN_sub y (Finset.mem_filter.mp hyN).2
      have hxN : x ∉ N := by simp [N, hirr x]
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hxN, List.toFinset_card_of_nodup hp.2.1] at h1
      have hNc : 2 ≤ N.card := hN_card
      omega
    have hex_j : ∃ y ∈ N, y ≠ p[1]'(by omega) := by
      by_contra hall
      push Not at hall
      have hsub : N ⊆ {p[1]'(by omega)} := fun y hy => Finset.mem_singleton.mpr (hall y hy)
      have := Finset.card_le_card hsub
      have hNc : 2 ≤ N.card := hN_card
      simp at this; omega
    obtain ⟨y, hyN, hy_ne1⟩ := hex_j
    have hy_adj : adj x y := (Finset.mem_filter.mp hyN).2
    have hyp : y ∈ p := hN_sub y hy_adj
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hyp
    have hj_ne0 : j ≠ 0 := by
      rintro rfl
      have : p[0]'(by omega) = x := (List.head_eq_getElem_zero hp.1).symm
      exact hirr x (this ▸ hy_adj)
    have hj_ne1 : j ≠ 1 := by
      intro h; subst h; exact hy_ne1 rfl
    have hj_ge2 : 2 ≤ j := by omega
    let c := p.take (j + 1)
    have hc_path : IsPath adj c := isPath_take hp (Nat.succ_pos j)
    have hc_len : c.length = j + 1 := by simp [c, Nat.min_eq_left (Nat.succ_le_of_lt hj)]
    refine ⟨c, isCycle_of_isPath_and_adj (by omega) hc_path ?_⟩
    have hlast : c.getLast hc_path.1 = p[j] := by
      rw [List.getLast_eq_getElem]; simp [c, hc_len]
    have hhead : c.head hc_path.1 = x := by
      rw [List.head_eq_getElem_zero]; simp [c, x, List.head_eq_getElem_zero hp.1]
    rw [hlast, hhead]
    exact hsym hy_adj
  -- Pick a LONGEST simple cycle C!
  let C_pred : ℕ → Prop := fun l => ∃ c : List V, IsCycle adj c ∧ c.length = l
  obtain ⟨c₀, hc₀⟩ := hex_cycle
  let M := Nat.findGreatest C_pred (Fintype.card V)
  have hM_spec : C_pred M :=
    Nat.findGreatest_spec (m := c₀.length) (hc₀.2.1.length_le_card) ⟨c₀, hc₀, rfl⟩
  obtain ⟨C, hC, hCM⟩ := hM_spec
  have hC_max : ∀ c' : List V, IsCycle adj c' → c'.length ≤ C.length := by
    intro c' hc'
    rw [hCM]
    exact Nat.le_findGreatest hc'.2.1.length_le_card ⟨c', hc', rfl⟩
  -- Show C.length = Fintype.card V!
  have hC3 : 3 ≤ C.length := hC.1
  have hC_full : C.length = Fintype.card V := by
    by_contra hne
    have hlt : C.length < Fintype.card V := lt_of_le_of_ne hC.2.1.length_le_card hne
    have hex_v : ∃ v : V, v ∉ C := by
      by_contra hall
      push Not at hall
      have hsub : Finset.univ ⊆ C.toFinset := fun x _ => List.mem_toFinset.mpr (hall x)
      have := Finset.card_le_card hsub
      rw [Finset.card_univ, List.toFinset_card_of_nodup hC.2.1] at this
      omega
    obtain ⟨v, hvC⟩ := hex_v
    -- Work in H = G \ {v} with X = N(v) and Y = C!
    let V' := {z : V // z ≠ v}
    let adjH : V' → V' → Prop := fun x y => adj x.1 y.1
    have hsymH : (∀ ⦃x y⦄, adjH x y → adjH y x) := fun _ _ h => hsym h
    have hirrH : (∀ x, ¬ adjH x x) := fun x h => hirr x.1 h
    let XH : Finset V' := Finset.univ.filter fun x => adj v x.1
    let YH : Finset V' := Finset.univ.filter fun x => x.1 ∈ C
    have hYH_card : YH.card = C.length := by
      have hbij : YH.card = C.toFinset.card := by
        refine Finset.card_bij (fun x _ => x.1) (fun x hx => List.mem_toFinset.mpr (Finset.mem_filter.mp hx).2)
          (fun _ _ _ _ h => Subtype.ext h) (fun y hy => ?_)
        have hyC : y ∈ C := List.mem_toFinset.mp hy
        exact ⟨⟨y, fun heq => hvC (heq ▸ hyC)⟩, by simp [YH, hyC], rfl⟩
      rw [hbij, List.toFinset_card_of_nodup hC.2.1]
    -- Minimum XH-YH separator in H
    have hYH_sep : IsSep adjH XH YH YH := fun p hp _ hlast => ⟨p.getLast hp.1, List.getLast_mem hp.1, hlast⟩
    have hex_sep : ∃ r : ℕ, ∃ S' : Finset V', IsSep adjH XH YH S' ∧ S'.card = r :=
      ⟨YH.card, YH, hYH_sep, rfl⟩
    let r := Nat.find hex_sep
    obtain ⟨S', hS'_sep, hS'_card⟩ := Nat.find_spec hex_sep
    have hr_min : ∀ T : Finset V', IsSep adjH XH YH T → r ≤ T.card :=
      fun T hT => Nat.find_min' hex_sep ⟨T, hT, rfl⟩
    have hr_le_C : r ≤ C.length := hYH_card ▸ hr_min YH hYH_sep
    -- Apply Menger on H to get r pairwise disjoint XH-YH paths, truncated at first hit of YH!
    obtain ⟨P₀, hP₀, hP₀_disj⟩ := menger (edgeCard adjH) adjH hsymH hirrH rfl XH YH r hr_min
    have hP_tr : ∀ i : Fin r, ∃ p', ∃ hp' : IsPath adjH p', p'.head hp'.1 ∈ XH ∧
        p'.getLast hp'.1 ∈ YH ∧ (∀ z ∈ p', z ∈ P₀ i) ∧
        (∀ z ∈ p'.dropLast, z ∉ YH) := by
      intro i
      obtain ⟨hp, hX, hY⟩ := hP₀ i
      obtain ⟨p', hp', hhd, hlt', hsub, havoid⟩ :=
        exists_prefix_first_mem hp ⟨(P₀ i).getLast hp.1, List.getLast_mem hp.1, hY⟩
      exact ⟨p', hp', hhd.symm ▸ hX, hlt', hsub, havoid⟩
    choose PH hPH_path hPH_X hPH_end hPH_sub hPH_avoid using hP_tr
    -- Map each path PH i back to V
    let PV : Fin r → List V := fun i => (PH i).map Subtype.val
    have hPV_path : ∀ i, IsPath adj (PV i) := by
      intro i
      refine ⟨fun h => (hPH_path i).1 (List.map_eq_nil_iff.mp h), (hPH_path i).2.1.map Subtype.val_injective, ?_⟩
      exact (isChain_map_iff Subtype.val adj (PH i)).mpr (hPH_path i).2.2
    have hPV_nv : ∀ i, v ∉ PV i := by
      intro i hv
      obtain ⟨x, _, hx⟩ := List.mem_map.mp hv
      exact x.2 hx
    have hPV_disj : Pairwise fun i j => List.Disjoint (PV i) (PV j) := by
      intro i j hij z hzi hzj
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hzi
      obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hzj
      have hxy : x = y := Subtype.ext hyx.symm
      subst hxy
      exact hP₀_disj hij (hPH_sub i x hx) (hPH_sub j x hy)
    have hPV_head_adj : ∀ i, adj v ((PV i).head (hPV_path i).1) := by
      intro i
      have : (PV i).head (hPV_path i).1 = ((PH i).head (hPH_path i).1).1 := List.head_map (hPV_path i).1
      rw [this]
      exact (Finset.mem_filter.mp (hPH_X i)).2
    -- Endpoint index idxC i of PV i on C
    have hPV_end_C : ∀ i, (PV i).getLast (hPV_path i).1 ∈ C := by
      intro i
      have : (PV i).getLast (hPV_path i).1 = ((PH i).getLast (hPH_path i).1).1 := List.getLast_map (hPV_path i).1
      rw [this]
      exact (Finset.mem_filter.mp (hPH_end i)).2
    have hPV_int_nC : ∀ i, ∀ z ∈ (PV i).dropLast, z ∉ C := by
      intro i z hz hzC
      have hdl : (PV i).dropLast = (PH i).dropLast.map Subtype.val := by
        exact dropLast_map_eq Subtype.val (PH i)
      rw [hdl] at hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      exact hPH_avoid i x hx (by simp [YH, hzC])
    -- Choose index of endpoint on C
    have hex_idx : ∀ i : Fin r, ∃ t : Fin C.length, C[t] = (PV i).getLast (hPV_path i).1 := by
      intro i
      obtain ⟨t, ht, hCt⟩ := List.getElem_of_mem (hPV_end_C i)
      exact ⟨⟨t, ht⟩, hCt⟩
    choose idxC hidxC using hex_idx
    have hidxC_inj : Function.Injective idxC := by
      intro i j hij
      by_contra hne
      have : (PV i).getLast (hPV_path i).1 = (PV j).getLast (hPV_path j).1 := by
        rw [← hidxC i, ← hidxC j, hij]
      exact hPV_disj hne (List.getLast_mem (hPV_path i).1) (this ▸ List.getLast_mem (hPV_path j).1)
    -- Helper: for any i, v is NOT adjacent to successor of C[idxC i] on C!
    have hno_v_succ : ∀ i : Fin r, ¬ adj v (cycNext C (idxC i)) := by
      intro i hv_next
      -- Rotate C so idxC i is at index 0, cycNext is at index 1; reverse so we go from idxC i backwards to cycNext!
      -- Easier: rotate C by (idxC i + 1) so cycNext is at 0 and idxC i is at length - 1!
      let C' := C.rotate ((idxC i).val + 1)
      have hC' : IsCycle adj C' := isCycle_rotate hC _
      have hC'_len : C'.length = C.length := by simp [C']
      have hC'_path : IsPath adj C' := by
        refine ⟨by intro h; have := congrArg List.length h; rw [List.length_nil] at this; omega, hC'.2.1, ?_⟩
        rw [List.isChain_iff_getElem]
        intro j hj
        have := hC'.2.2 ⟨j, by omega⟩
        simpa [Nat.mod_eq_of_lt hj] using this
      have hC'_head : C'.head hC'_path.1 = cycNext C (idxC i) := by
        rw [List.head_eq_getElem_zero]; simp [C', cycNext, List.getElem_rotate]
      have hC'_last : C'.getLast hC'_path.1 = (PV i).getLast (hPV_path i).1 := by
        rw [List.getLast_eq_getElem, ← hidxC i]
        simp only [C', hC'_len, List.getElem_rotate]
        congr 1
        have hpos : 0 < C.length := by omega
        have : C.length - 1 + ((idxC i).val + 1) = (idxC i).val + C.length := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (idxC i).2]
      -- Build longer cycle: C' ++ (PV i).reverse.tail ++ [v]
      let P' := (PV i).reverse
      have hP' : IsPath adj P' := isPath_reverse hsym (hPV_path i)
      have hP'_head : P'.head hP'.1 = C'.getLast hC'_path.1 := by
        rw [hC'_last]; exact List.head_reverse _
      have hP'_tail_disj : List.Disjoint C' P'.tail := by
        intro z hzC' hzPt
        have hzC : z ∈ C := (List.mem_rotate).mp hzC'
        have hzdl : z ∈ (PV i).dropLast := by
          have : z ∈ (PV i).dropLast.reverse := by rwa [List.tail_reverse] at hzPt
          exact List.mem_reverse.mp this
        exact hPV_int_nC i z hzdl hzC
      have hCP : IsPath adj (C' ++ P'.tail) := isPath_glue hC'_path hP' hP'_head.symm hP'_tail_disj
      have hCP_last : (C' ++ P'.tail).getLast hCP.1 = (PV i).head (hPV_path i).1 := by
        rw [getLast_append_tail hC'_path.1 hP'.1 hP'_head.symm]; exact List.getLast_reverse _
      have hv_disj : List.Disjoint (C' ++ P'.tail) [v] := by
        intro z hz hvz
        simp only [List.mem_singleton] at hvz; subst hvz
        rcases List.mem_append.mp hz with h1 | h2
        · exact hvC (List.mem_rotate.mp h1)
        · exact hPV_nv i (List.mem_reverse.mp (List.mem_of_mem_tail h2))
      have hbig : IsPath adj ((C' ++ P'.tail) ++ [v]) :=
        isPath_append hCP (isPath_singleton adj v) hv_disj (by rw [hCP_last]; exact hsym (hPV_head_adj i))
      have hbig_cyc : IsCycle adj ((C' ++ P'.tail) ++ [v]) :=
        isCycle_of_isPath_and_adj (by simp [hC'_len]; omega) hbig (by
          simp only [List.getLast_append_singleton]
          rw [List.head_append_of_ne_nil hCP.1, List.head_append_of_ne_nil hC'_path.1, hC'_head]
          exact hv_next)
      have hle := hC_max _ hbig_cyc
      simp [hC'_len] at hle
    -- Helper: for any i ≠ j, idxC i and idxC j CANNOT be adjacent on C!
    have hno_adj_ends : ∀ i j : Fin r, i ≠ j →
        ((idxC i).val + 1) % C.length ≠ (idxC j).val := by
      intro i j hij hnext
      -- Rotate C by (idxC j).val so idxC j is at 0 and idxC i is at C.length - 1!
      let C' := C.rotate (idxC j).val
      have hC' : IsCycle adj C' := isCycle_rotate hC _
      have hC'_len : C'.length = C.length := by simp [C']
      have hC'_path : IsPath adj C' := by
        refine ⟨by intro h; have := congrArg List.length h; rw [List.length_nil] at this; omega, hC'.2.1, ?_⟩
        rw [List.isChain_iff_getElem]
        intro t ht
        have := hC'.2.2 ⟨t, by omega⟩
        simpa [Nat.mod_eq_of_lt ht] using this
      have hC'_head : C'.head hC'_path.1 = (PV j).getLast (hPV_path j).1 := by
        rw [List.head_eq_getElem_zero, ← hidxC j]; simp [C', List.getElem_rotate, Nat.mod_eq_of_lt (idxC j).2]
      have hC'_last : C'.getLast hC'_path.1 = (PV i).getLast (hPV_path i).1 := by
        rw [List.getLast_eq_getElem, ← hidxC i]
        simp only [C', hC'_len, List.getElem_rotate]
        congr 1
        have hpos : 0 < C.length := by omega
        have : (C.length - 1 + (idxC j).val) % C.length = (idxC i).val := by
          rw [← hnext]
          have h1 : (C.length - 1 + ((idxC i).val + 1) % C.length) % C.length =
              (C.length - 1 + ((idxC i).val + 1)) % C.length := by
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          rw [h1]
          have h2 : C.length - 1 + ((idxC i).val + 1) = (idxC i).val + C.length := by omega
          rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (idxC i).2]
        exact this
      -- Glue C' (ending at PV i.last) ++ (PV i).reverse.tail ++ [v] ++ (PV j).dropLast!
      let PiR := (PV i).reverse
      have hPiR : IsPath adj PiR := isPath_reverse hsym (hPV_path i)
      have hPiR_head : PiR.head hPiR.1 = C'.getLast hC'_path.1 := by
        rw [hC'_last]; exact List.head_reverse _
      have h1_disj : List.Disjoint C' PiR.tail := by
        intro z hzC' hzPt
        exact hPV_int_nC i z (List.mem_reverse.mp (by rwa [List.tail_reverse] at hzPt)) (List.mem_rotate.mp hzC')
      have hCPi : IsPath adj (C' ++ PiR.tail) := isPath_glue hC'_path hPiR hPiR_head.symm h1_disj
      have hCPi_last : (C' ++ PiR.tail).getLast hCPi.1 = (PV i).head (hPV_path i).1 := by
        rw [getLast_append_tail hC'_path.1 hPiR.1 hPiR_head.symm]; exact List.getLast_reverse _
      have hv_disj : List.Disjoint (C' ++ PiR.tail) [v] := by
        intro z hz hvz
        simp only [List.mem_singleton] at hvz; subst hvz
        rcases List.mem_append.mp hz with h1 | h2
        · exact hvC (List.mem_rotate.mp h1)
        · exact hPV_nv i (List.mem_reverse.mp (List.mem_of_mem_tail h2))
      have hCPiv : IsPath adj ((C' ++ PiR.tail) ++ [v]) :=
        isPath_append hCPi (isPath_singleton adj v) hv_disj (by rw [hCPi_last]; exact hsym (hPV_head_adj i))
      -- Now append (PV j).dropLast (which may be empty if PV j is a singleton!)
      cases hdl : (PV j).dropLast with
      | nil =>
        -- PV j is a singleton [c_j], so v is directly adjacent to c_j = C'.head!
        have hlen1 : (PV j).length = 1 := by
          have h0 := congrArg List.length hdl
          rw [List.length_dropLast, List.length_nil] at h0
          have hpos := List.length_pos_of_ne_nil (hPV_path j).1
          omega
        have hhead_last : (PV j).head (hPV_path j).1 = (PV j).getLast (hPV_path j).1 := by
          rw [List.head_eq_getElem_zero, List.getLast_eq_getElem]; congr 1; omega
        have hbig_cyc : IsCycle adj ((C' ++ PiR.tail) ++ [v]) :=
          isCycle_of_isPath_and_adj (by simp [hC'_len]; omega) hCPiv (by
            simp only [List.getLast_append_singleton]
            rw [List.head_append_of_ne_nil hCPi.1, List.head_append_of_ne_nil hC'_path.1,
              hC'_head, ← hhead_last]
            exact hPV_head_adj j)
        have hle := hC_max _ hbig_cyc
        simp [hC'_len] at hle
      | cons b t =>
        have hdl_path : IsPath adj (b :: t) := by
          have h1 : 0 < (PV j).length - 1 := by
            have := congrArg List.length hdl; rw [List.length_dropLast] at this; simp at this; omega
          have := isPath_take (hPV_path j) h1
          rwa [← List.dropLast_eq_take, hdl] at this
        have hdl_head : (b :: t).head hdl_path.1 = (PV j).head (hPV_path j).1 := by
          have : ((PV j).dropLast)[0]'(by simp [hdl]) = (PV j)[0]'(List.length_pos_of_ne_nil (hPV_path j).1) :=
            List.getElem_dropLast _
          rw [List.head_eq_getElem_zero, List.head_eq_getElem_zero]; simpa [hdl] using this
        have hdl_last_adj : adj ((b :: t).getLast hdl_path.1) ((PV j).getLast (hPV_path j).1) := by
          have hsplit := List.dropLast_append_getLast (hPV_path j).1
          have hch := (hPV_path j).2.2
          rw [← hsplit, hdl, List.isChain_append] at hch
          exact hch.2.2 _ (List.getLast?_eq_some_getLast hdl_path.1) _ (by simp)
        have hdl_disj : List.Disjoint ((C' ++ PiR.tail) ++ [v]) (b :: t) := by
          intro z hz1 hz2
          have hzdl : z ∈ (PV j).dropLast := hdl ▸ hz2
          have hzPj : z ∈ PV j := List.mem_of_mem_dropLast hzdl
          rcases List.mem_append.mp hz1 with h12 | hvz
          · rcases List.mem_append.mp h12 with hzC' | hzPi
            · exact hPV_int_nC j z hzdl (List.mem_rotate.mp hzC')
            · exact hPV_disj hij (List.mem_reverse.mp (List.mem_of_mem_tail hzPi)) hzPj
          · simp only [List.mem_singleton] at hvz; subst hvz; exact hPV_nv j hzPj
        have hbig : IsPath adj (((C' ++ PiR.tail) ++ [v]) ++ (b :: t)) :=
          isPath_append hCPiv hdl_path hdl_disj (by
            rw [List.getLast_append_singleton, hdl_head]; exact hPV_head_adj j)
        have hbig_cyc : IsCycle adj (((C' ++ PiR.tail) ++ [v]) ++ (b :: t)) :=
          isCycle_of_isPath_and_adj (by simp [hC'_len]; omega) hbig (by
            rw [List.getLast_append_of_ne_nil _ hdl_path.1,
              List.head_append_of_ne_nil hCPiv.1, List.head_append_of_ne_nil hCPi.1,
              List.head_append_of_ne_nil hC'_path.1, hC'_head]
            exact hdl_last_adj)
        have hle := hC_max _ hbig_cyc
        simp [hC'_len] at hle
    -- Therefore r < C.length! (If r = C.length, idxC is surjective, so C[0] and C[1] are hit!)
    have hr_lt_C : r < C.length := by
      by_contra hge
      have hreq : r = C.length := by omega
      have hbij : Function.Bijective idxC :=
        (Fintype.bijective_iff_injective_and_card idxC).mpr ⟨hidxC_inj, by simp [hreq]⟩
      obtain ⟨i, hi⟩ := hbij.2 ⟨0, by omega⟩
      obtain ⟨j, hj⟩ := hbij.2 ⟨1, by omega⟩
      have hij : i ≠ j := fun h => by subst h; rw [hi] at hj; exact absurd (congrArg Fin.val hj) (by simp)
      apply hno_adj_ends i j hij
      rw [hi, hj]; simp [Nat.mod_eq_of_lt (show 1 < C.length by omega)]
    -- Helper: for any i ≠ j, cycNext C (idxC i) and cycNext C (idxC j) are NOT adjacent!
    have hno_succ_adj : ∀ i j : Fin r, i ≠ j →
        ¬ adj (cycNext C (idxC i)) (cycNext C (idxC j)) := by
      intro i j hij hadj_ss
      -- Rotate C by (idxC i).val so c_i is at 0, c_i^+ is at 1, c_j is at t with 2 ≤ t ≤ m - 2!
      let C' := C.rotate (idxC i).val
      have hC' : IsCycle adj C' := isCycle_rotate hC _
      have hC'_len : C'.length = C.length := by simp [C']
      have hpos : 0 < C.length := by omega
      let t : ℕ := ((idxC j).val + C.length - (idxC i).val) % C.length
      have ht_lt : t < C.length := Nat.mod_lt _ hpos
      have ht_val : C'[t]'(by omega) = C[idxC j] := by
        simp only [C', List.getElem_rotate, t]
        congr 1
        have h1 : (((idxC j).val + C.length - (idxC i).val) % C.length + (idxC i).val) % C.length =
            ((idxC j).val + C.length - (idxC i).val + (idxC i).val) % C.length := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        rw [h1, Nat.sub_add_cancel (by omega), Nat.add_mod_right, Nat.mod_eq_of_lt (idxC j).2]
      have ht_ne0 : t ≠ 0 := by
        intro h0
        have : C'[0]'(by omega) = C[idxC j] := by simpa [h0] using ht_val
        have h0' : C'[0]'(by omega) = C[idxC i] := by simp [C', List.getElem_rotate, Nat.mod_eq_of_lt (idxC i).2]
        have hceq : C[idxC i] = C[idxC j] := h0'.symm.trans this
        have hidx_eq : idxC i = idxC j := Fin.ext ((List.Nodup.getElem_inj_iff hC.2.1).mp hceq)
        exact hij (hidxC_inj hidx_eq)
      have ht_ne1 : t ≠ 1 := by
        intro h1
        apply hno_adj_ends i j hij
        have : ((idxC i).val + 1) % C.length = (idxC j).val := by
          have heq : C'[1]'(by omega) = C[idxC j] := by simpa [h1] using ht_val
          have h1' : C'[1]'(by omega) = C[((idxC i).val + 1) % C.length]'(Nat.mod_lt _ hpos) := by
            simp [C', List.getElem_rotate, Nat.add_comm]
          exact (List.Nodup.getElem_inj_iff hC.2.1).mp (h1'.symm.trans heq)
        exact this
      have ht_lt_last : t + 1 < C.length := by
        by_contra hge
        have htlast : t = C.length - 1 := by omega
        apply hno_adj_ends j i hij.symm
        have h1 : (t + (idxC i).val) % C.length = (idxC j).val := by
          have : C'[(t)]'(by omega) = C[(t + (idxC i).val) % C.length]'(Nat.mod_lt _ hpos) := by
            simp [C', List.getElem_rotate]
          exact (List.Nodup.getElem_inj_iff hC.2.1).mp (this.symm.trans ht_val)
        rw [← h1, htlast]
        have h2 : ((C.length - 1 + (idxC i).val) % C.length + 1) % C.length =
            (C.length - 1 + (idxC i).val + 1) % C.length := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        rw [h2]
        have h3 : C.length - 1 + (idxC i).val + 1 = (idxC i).val + C.length := by omega
        rw [h3, Nat.add_mod_right, Nat.mod_eq_of_lt (idxC i).2]
      -- Split C' into two arcs:
      --   Arc1 = (C'.drop 1).take t  : goes from C'[1] (= c_i^+) to C'[t] (= c_j), length t >= 2
      --   Arc2 = (C'[0] :: (C'.drop (t + 1)).reverse) : goes from C'[0] (= c_i) backwards to C'[t+1] (= c_j^+), length C.length - t >= 2!
      -- Wait: even cleaner! Just take Arc2 = (C'.rotate (t + 1)).take (C.length - t) reversed!
      -- Let's check: C'.rotate (t + 1) has:
      --   index 0 -> C'[t+1] = c_j^+
      --   index C.length - t - 1 -> C'[0] = c_i
      --   so ((C'.rotate (t + 1)).take (C.length - t)).reverse goes from c_i to c_j^+!
      have hC'_path : IsPath adj C' := by
        refine ⟨by intro h; have := congrArg List.length h; rw [List.length_nil] at this; omega, hC'.2.1, ?_⟩
        rw [List.isChain_iff_getElem]
        intro s hs
        have := hC'.2.2 ⟨s, by omega⟩
        simpa [Nat.mod_eq_of_lt hs] using this
      let arc1 := (C'.drop 1).take t
      have harc1_path : IsPath adj arc1 := isPath_take (isPath_drop hC'_path (by omega)) (by omega)
      have harc1_len : arc1.length = t := by
        simp [arc1, hC'_len, Nat.min_eq_left (show t ≤ C.length - 1 by omega)]
      have harc1_head : arc1.head harc1_path.1 = cycNext C (idxC i) := by
        rw [List.head_eq_getElem_zero]
        simp [arc1, C', cycNext, List.getElem_rotate, Nat.add_comm]
      have harc1_last : arc1.getLast harc1_path.1 = (PV j).getLast (hPV_path j).1 := by
        rw [List.getLast_eq_getElem, ← hidxC j, ← ht_val]
        simp only [arc1, List.getElem_take, List.getElem_drop, harc1_len]
        congr 1; omega
      let C'' := C'.rotate (t + 1)
      have hC'' : IsCycle adj C'' := isCycle_rotate hC' (t + 1)
      have hC''_len : C''.length = C.length := by simp [C'', hC'_len]
      have hC''_path : IsPath adj C'' := by
        refine ⟨by intro h; have := congrArg List.length h; rw [List.length_nil] at this; omega, hC''.2.1, ?_⟩
        rw [List.isChain_iff_getElem]
        intro s hs
        have := hC''.2.2 ⟨s, by omega⟩
        simpa [Nat.mod_eq_of_lt hs] using this
      let arc2₀ := C''.take (C.length - t)
      have harc2₀_path : IsPath adj arc2₀ := isPath_take hC''_path (by omega)
      have harc2₀_len : arc2₀.length = C.length - t := by
        simp [arc2₀, hC''_len]
      let arc2 := arc2₀.reverse
      have harc2_path : IsPath adj arc2 := isPath_reverse hsym harc2₀_path
      have harc2_len : arc2.length = C.length - t := by simp [arc2, harc2₀_len]
      have harc2_head : arc2.head harc2_path.1 = (PV i).getLast (hPV_path i).1 := by
        rw [List.head_reverse, List.getLast_eq_getElem, ← hidxC i]
        simp only [arc2₀, harc2₀_len, List.getElem_take, C'', C', hC'_len, List.getElem_rotate]
        congr 1
        have h1 : (C.length - t - 1 + (t + 1)) % C.length = 0 := by
          have : C.length - t - 1 + (t + 1) = C.length := by omega
          rw [this, Nat.mod_self]
        rw [h1, zero_add, Nat.mod_eq_of_lt (idxC i).2]
      have harc2_last : arc2.getLast harc2_path.1 = cycNext C (idxC j) := by
        rw [List.getLast_reverse, List.head_eq_getElem_zero]
        simp only [arc2₀, List.getElem_take, C'', C', hC'_len, List.getElem_rotate, cycNext]
        congr 1
        have h1 : ((0 + (t + 1)) % C.length + (idxC i).val) % C.length =
            (t + (idxC i).val + 1) % C.length := by
          rw [zero_add, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; ring_nf
        rw [h1]
        have h2 : (t + (idxC i).val) % C.length = (idxC j).val := by
          have : C'[t]'(by omega) = C[(t + (idxC i).val) % C.length]'(Nat.mod_lt _ hpos) := by
            simp [C', List.getElem_rotate]
          exact (List.Nodup.getElem_inj_iff hC.2.1).mp (this.symm.trans ht_val)
        rw [← h2]; simp [Nat.add_mod]
      -- Verify arc1 and arc2 are DISJOINT!
      have harc_disj : List.Disjoint arc1 arc2 := by
        intro z hz1 hz2
        obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hz1
        obtain ⟨b, hb, hba⟩ := List.getElem_of_mem (List.mem_reverse.mp hz2)
        have ha' : a < t := by omega
        have hb' : b < C.length - t := by omega
        have h1_lt : 1 + a < C'.length := by omega
        have h2_lt : (b + (t + 1)) % C.length < C'.length := by rw [hC'_len]; exact Nat.mod_lt _ (by omega)
        have h1 : arc1[a] = C'[1 + a]'h1_lt := by simp [arc1]; congr 1; omega
        have h2 : arc2₀[b] = C'[(b + (t + 1)) % C.length]'h2_lt := by
          simp [arc2₀, C'', hC'_len, List.getElem_rotate]
        have hEq : C'[(b + (t + 1)) % C.length]'h2_lt = C'[1 + a]'h1_lt :=
          h2.symm.trans (hba.trans h1)
        have hidxEq := (List.Nodup.getElem_inj_iff hC'.2.1).mp hEq
        by_cases hltb : b + (t + 1) < C.length
        · rw [Nat.mod_eq_of_lt hltb] at hidxEq; omega
        · have hb_eq : b + (t + 1) = C.length := by omega
          rw [hb_eq, Nat.mod_self] at hidxEq; omega
      -- Now stitch: arc1 ++ (PV j).reverse.tail ++ [v] ++ (PV i).dropLast ++ arc2!
      -- Wait: check that (PV i) ends at arc2.head! So (PV i) ++ arc2.tail is glue!
      -- Let's glue step by step:
      --   L1 := arc1 ++ (PV j).reverse.tail  (ends at (PV j).head)
      --   L2 := L1 ++ [v]                    (ends at v)
      --   L3 := (PV i) ++ arc2.tail          (starts at (PV i).head, ends at arc2.last = c_j^+)
      --   Big := L2 ++ L3!
      let PjR := (PV j).reverse
      have hPjR : IsPath adj PjR := isPath_reverse hsym (hPV_path j)
      have hL1_disj : List.Disjoint arc1 PjR.tail := by
        intro z hz1 hz2
        have hzC : z ∈ C := List.mem_rotate.mp (List.mem_of_mem_drop (List.mem_of_mem_take hz1))
        exact hPV_int_nC j z (List.mem_reverse.mp (by rwa [List.tail_reverse] at hz2)) hzC
      have hL1 : IsPath adj (arc1 ++ PjR.tail) :=
        isPath_glue harc1_path hPjR (by rw [harc1_last, List.head_reverse]) hL1_disj
      have hL1_last : (arc1 ++ PjR.tail).getLast hL1.1 = (PV j).head (hPV_path j).1 := by
        rw [getLast_append_tail harc1_path.1 hPjR.1 (by rw [harc1_last, List.head_reverse])]; exact List.getLast_reverse _
      have hv_disj1 : List.Disjoint (arc1 ++ PjR.tail) [v] := by
        intro z hz hvz
        simp only [List.mem_singleton] at hvz; subst hvz
        rcases List.mem_append.mp hz with h1 | h2
        · exact hvC (List.mem_rotate.mp (List.mem_of_mem_drop (List.mem_of_mem_take h1)))
        · exact hPV_nv j (List.mem_reverse.mp (List.mem_of_mem_tail h2))
      have hL2 : IsPath adj ((arc1 ++ PjR.tail) ++ [v]) :=
        isPath_append hL1 (isPath_singleton adj v) hv_disj1 (by rw [hL1_last]; exact hsym (hPV_head_adj j))
      have hL3_disj : List.Disjoint (PV i) arc2.tail := by
        intro z hzPi hz2t
        have hz2 : z ∈ arc2 := List.mem_of_mem_tail hz2t
        have hzC : z ∈ C :=
          List.mem_rotate.mp (List.mem_rotate.mp (List.mem_of_mem_take (List.mem_reverse.mp hz2)))
        have hsplit := List.dropLast_append_getLast (hPV_path i).1
        rw [← hsplit, List.mem_append, List.mem_singleton] at hzPi
        rcases hzPi with hdl | rfl
        · exact hPV_int_nC i z hdl hzC
        · rw [← harc2_head] at hz2t
          cases ha2 : arc2 with
          | nil => exact absurd ha2 harc2_path.1
          | cons a l =>
            have hnd := harc2_path.2.1
            rw [ha2, List.nodup_cons] at hnd
            simp only [ha2, List.head_cons, List.tail_cons] at hz2t
            exact hnd.1 hz2t
      have hL3 : IsPath adj (PV i ++ arc2.tail) :=
        isPath_glue (hPV_path i) harc2_path harc2_head.symm hL3_disj
      have hL3_last : (PV i ++ arc2.tail).getLast hL3.1 = cycNext C (idxC j) := by
        rw [getLast_append_tail (hPV_path i).1 harc2_path.1 harc2_head.symm]; exact harc2_last
      have hL23_disj : List.Disjoint ((arc1 ++ PjR.tail) ++ [v]) (PV i ++ arc2.tail) := by
        intro z hzL2 hzL3
        have hzL3' : z ∈ PV i ∨ z ∈ arc2 := by
          rcases List.mem_append.mp hzL3 with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_of_mem_tail h)
        rcases List.mem_append.mp hzL2 with h12 | hvz
        · rcases List.mem_append.mp h12 with hz1 | hzPj
          · rcases hzL3' with hzPi | hz2
            · -- z ∈ arc1 ⊆ C and z ∈ PV i => z = PV i.last = arc2.head ∈ arc2, contradicting arc1 ∩ arc2 = ∅!
              have hzC : z ∈ C := List.mem_rotate.mp (List.mem_of_mem_drop (List.mem_of_mem_take hz1))
              have hsplit := List.dropLast_append_getLast (hPV_path i).1
              rw [← hsplit, List.mem_append, List.mem_singleton] at hzPi
              rcases hzPi with hdl | rfl
              · exact hPV_int_nC i z hdl hzC
              · exact harc_disj hz1 (harc2_head ▸ List.head_mem harc2_path.1)
            · exact harc_disj hz1 hz2
          · have hzPj_dl : z ∈ (PV j).dropLast :=
              List.mem_reverse.mp (by rwa [List.tail_reverse] at hzPj)
            rcases hzL3' with hzPi | hz2
            · exact hPV_disj hij hzPi (List.mem_of_mem_dropLast hzPj_dl)
            · exact hPV_int_nC j z hzPj_dl
                (List.mem_rotate.mp (List.mem_rotate.mp (List.mem_of_mem_take (List.mem_reverse.mp hz2))))
        · simp only [List.mem_singleton] at hvz; subst hvz
          rcases hzL3' with hzPi | hz2
          · exact hPV_nv i hzPi
          · exact hvC (List.mem_rotate.mp (List.mem_rotate.mp (List.mem_of_mem_take (List.mem_reverse.mp hz2))))
      have hBig : IsPath adj (((arc1 ++ PjR.tail) ++ [v]) ++ (PV i ++ arc2.tail)) :=
        isPath_append hL2 hL3 hL23_disj (by
          rw [List.getLast_append_singleton, List.head_append_of_ne_nil (hPV_path i).1]
          exact hPV_head_adj i)
      have hBig_cyc : IsCycle adj (((arc1 ++ PjR.tail) ++ [v]) ++ (PV i ++ arc2.tail)) :=
        isCycle_of_isPath_and_adj (by simp [harc1_len, harc2_len]; omega) hBig (by
          rw [List.getLast_append_of_ne_nil _ hL3.1, hL3_last,
            List.head_append_of_ne_nil hL2.1, List.head_append_of_ne_nil hL1.1,
            List.head_append_of_ne_nil harc1_path.1, harc1_head]
          exact hsym hadj_ss)
      have hle := hC_max _ hBig_cyc
      have hPVi_pos : 1 ≤ (PV i).length := List.length_pos_of_ne_nil (hPV_path i).1
      simp only [List.length_append, List.length_singleton, List.length_tail, harc1_len, harc2_len] at hle
      omega
    -- NOW build the vertex cut (S, A, B) of size r and independent set I of size r + 1!
    let S : Finset V := S'.image Subtype.val
    have hS_card : S.card = r := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective, hS'_card]
    have hvS : v ∉ S := by
      intro hv; obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hv; exact x.2 hx
    -- Because r < C.length, there exists c* ∈ C with c* ∉ S!
    have hex_c_out : ∃ c ∈ C, c ∉ S := by
      by_contra hall
      push Not at hall
      have hsub : C.toFinset ⊆ S := fun x hx => hall x (List.mem_toFinset.mp hx)
      have := Finset.card_le_card hsub
      rw [List.toFinset_card_of_nodup hC.2.1, hS_card] at this
      omega
    obtain ⟨c_out, hc_out_C, hc_out_nS⟩ := hex_c_out
    let A : Finset V := Finset.univ.filter fun z => ReachAvoiding adj {v} S z
    let B : Finset V := (Finset.univ \ S) \ A
    have hvA : v ∈ A := by
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨[v], isPath_singleton adj v, Finset.mem_singleton_self v, rfl, ?_⟩
      intro w hw; simp only [List.mem_singleton] at hw; subst hw; exact hvS
    have hc_out_nA : c_out ∉ A := by
      intro hA
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hA
      obtain ⟨p, hp, hpv, hplast, havoid⟩ := hA
      simp only [Finset.mem_singleton] at hpv
      -- p starts at v and ends at c_out ∈ C (≠ v), so p.tail is a path in H from XH to YH avoiding S'!
      cases hp_eq : p with
      | nil => exact absurd hp_eq hp.1
      | cons a t =>
        simp only [hp_eq, List.head_cons] at hpv
        cases ht_eq : t with
        | nil =>
          simp only [hp_eq, ht_eq, List.getLast_singleton] at hplast
          exact hvC (hpv ▸ hplast ▸ hc_out_C)
        | cons b t' =>
          have hnd := List.nodup_cons.mp (hp_eq ▸ hp.2.1)
          have hch := List.isChain_cons_cons.mp (by rw [← ht_eq, ← hp_eq]; exact hp.2.2)
          have ht_nv : ∀ w ∈ b :: t', w ≠ v := fun w hw h => hnd.1 (hpv.symm ▸ ht_eq ▸ h ▸ hw)
          let pH : List V' := (b :: t').pmap Subtype.mk ht_nv
          have hpH_map : pH.map Subtype.val = b :: t' := by simp [pH, List.map_pmap]
          have hpH : IsPath adjH pH := by
            refine ⟨by simp [pH], ?_, ?_⟩
            · exact List.Nodup.of_map Subtype.val (hpH_map ▸ (ht_eq ▸ hnd.2))
            · exact (isChain_map_iff Subtype.val adj pH).mp (hpH_map ▸ hch.2)
          have hpH_head : pH.head hpH.1 ∈ XH := by
            simp [XH, pH, ← hpv, hch.1]
          have hpH_last : pH.getLast hpH.1 ∈ YH := by
            have h1 : (pH.getLast hpH.1).1 = c_out := by
              have hne_m : pH.map Subtype.val ≠ [] := fun h => hpH.1 (List.map_eq_nil_iff.mp h)
              have hm1 : (pH.map Subtype.val).getLast hne_m = (pH.getLast hpH.1).1 := List.getLast_map hne_m
              have hgl : ∀ {l₁ l₂ : List V} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []), l₁ = l₂ → l₁.getLast h₁ = l₂.getLast h₂ := by
                intro l₁ l₂ _ _ heq; subst heq; rfl
              have hm2 := hgl hne_m (List.cons_ne_nil b t') hpH_map
              have h2 : (b :: t').getLast (List.cons_ne_nil _ _) = c_out := by
                simpa [hp_eq, ht_eq] using hplast
              exact hm1.symm.trans (hm2.trans h2)
            simp [YH, h1, hc_out_C]
          obtain ⟨z, hzpH, hzS'⟩ := hS'_sep pH hpH hpH_head hpH_last
          have hz_in_p : z.1 ∈ p := by
            rw [hp_eq, ht_eq]
            apply List.mem_cons_of_mem
            rw [← hpH_map]
            exact List.mem_map_of_mem hzpH
          exact havoid z.1 hz_in_p (Finset.mem_image_of_mem Subtype.val hzS')
    have hc_out_B : c_out ∈ B := by
      simp [B, hc_out_nS, hc_out_nA]
    -- Independent set I = insert v (Finset.univ.image fun i => cycNext C (idxC i))
    let I_succ : Finset V := Finset.univ.image fun i : Fin r => cycNext C (idxC i)
    let I : Finset V := insert v I_succ
    have hsucc_inj : Function.Injective (fun i : Fin r => cycNext C (idxC i)) := by
      intro i j hij
      have hmod := (List.Nodup.getElem_inj_iff hC.2.1).mp hij
      have hidx : (idxC i).val = (idxC j).val := by
        by_cases hi : (idxC i).val + 1 < C.length <;> by_cases hj : (idxC j).val + 1 < C.length
        · rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hmod; omega
        · have : (idxC j).val + 1 = C.length := by omega
          rw [Nat.mod_eq_of_lt hi, this, Nat.mod_self] at hmod; omega
        · have : (idxC i).val + 1 = C.length := by omega
          rw [this, Nat.mod_self, Nat.mod_eq_of_lt hj] at hmod; omega
        · omega
      exact hidxC_inj (Fin.ext hidx)
    have hv_nI : v ∉ I_succ := by
      intro hv
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
      exact hvC (by rw [← hi]; exact List.getElem_mem _)
    have hI_card : I.card = r + 1 := by
      rw [Finset.card_insert_of_notMem hv_nI, Finset.card_image_of_injective _ hsucc_inj,
        Finset.card_univ, Fintype.card_fin]
    have hI_indep : ∀ x ∈ I, ∀ y ∈ I, ¬ adj x y := by
      intro x hx y hy
      rcases Finset.mem_insert.mp hx with rfl | hx' <;> rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact hirr _
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy'
        exact hno_v_succ j
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx'
        exact fun h => hno_v_succ i (hsym h)
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx'
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy'
        by_cases hij : i = j
        · subst hij; exact hirr _
        · exact hno_succ_adj i j hij
    have hle := hno S A B I
      (by rw [Finset.disjoint_left]; intro z hzS hzA
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hzA
          obtain ⟨p, hp, _, hlast, havoid⟩ := hzA
          exact havoid z (hlast ▸ List.getLast_mem hp.1) hzS)
      (by rw [Finset.disjoint_left]; intro z hzS hzB
          exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hzB).1).2 hzS)
      (by rw [Finset.disjoint_left]; intro z hzA hzB
          exact (Finset.mem_sdiff.mp hzB).2 hzA)
      (by ext z; simp [B]; tauto)
      ⟨v, hvA⟩
      ⟨c_out, hc_out_B⟩
      (by intro x hxA y hyB hxy
          have hyS : y ∉ S := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hyB).1).2
          have hxR : ReachAvoiding adj {v} S x := (Finset.mem_filter.mp hxA).2
          exact (Finset.mem_sdiff.mp hyB).2 (by simp [A, reachAvoiding_adj hxR hxy hyS]))
      hI_indep
    omega
  -- Convert full-length cycle C into Equiv Fin (Fintype.card V) ≃ V!
  let f : Fin (Fintype.card V) → V := fun i => C[i.val]'(by omega)
  have hf_inj : Function.Injective f := fun i j h =>
    Fin.ext ((List.Nodup.getElem_inj_iff hC.2.1).mp h)
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, by simp⟩
  refine ⟨Equiv.ofBijective f hf_bij, fun i => ?_⟩
  have := hC.2.2 ⟨i.val, by omega⟩
  simpa [f, hC_full] using this

end GraphTheory

section CharacterEngine

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Norm bound for twisted Jacobi sum `∑ u : Fˣ, ψ (a₀ + u) * χ u`. -/
lemma norm_twisted_sum_eq_jacobi (a₀ : F) (ha₀ : a₀ ≠ 0) (ψ χ : MulChar F ℂ) :
    ‖∑ u : Fˣ, ψ (a₀ + u) * χ u‖ = ‖jacobiSum ψ χ‖ := by
  have hrew : ∑ u : Fˣ, ψ (a₀ + u) * χ u = ψ a₀ * χ (-a₀) * jacobiSum ψ χ := by
    rw [jacobiSum, Finset.mul_sum]
    have hsumF : ∑ u : Fˣ, ψ (a₀ + u) * χ u = ∑ u : F, ψ (a₀ + u) * χ u := by
      have h0 : ψ (a₀ + 0) * χ 0 = 0 := by rw [χ.map_zero, mul_zero]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : F)), h0, add_zero]
      refine Finset.sum_bij (fun (u : Fˣ) _ => (u : F))
        (fun u _ => Finset.mem_erase.mpr ⟨u.ne_zero, Finset.mem_univ _⟩)
        (fun _ _ _ _ h => Units.ext h)
        (fun x hx => ⟨Units.mk0 x (Finset.mem_erase.mp hx).1, Finset.mem_univ _, rfl⟩)
        (fun _ _ => rfl)
    rw [hsumF]
    -- Reindex t = 1 + a₀⁻¹ * u (bijection on F since a₀ ≠ 0), so a₀ + u = a₀ * t and u = (-a₀) * (1 - t)!
    refine Finset.sum_bij (fun u _ => 1 + a₀⁻¹ * u) (fun _ _ => Finset.mem_univ _)
      (fun u₁ _ u₂ _ h => by
        have h1 : a₀⁻¹ * u₁ = a₀⁻¹ * u₂ := add_left_cancel h
        exact mul_left_cancel₀ (inv_ne_zero ha₀) h1)
      (fun t _ => ⟨a₀ * (t - 1), Finset.mem_univ _, by field_simp [ha₀]; ring⟩)
      (fun u _ => ?_)
    have h1 : a₀ + u = a₀ * (1 + a₀⁻¹ * u) := by field_simp [ha₀]
    have h2 : u = (-a₀) * (1 - (1 + a₀⁻¹ * u)) := by field_simp [ha₀]; ring
    calc ψ (a₀ + u) * χ u
        = ψ (a₀ * (1 + a₀⁻¹ * u)) * χ ((-a₀) * (1 - (1 + a₀⁻¹ * u))) := by rw [← h1, ← h2]
      _ = ψ a₀ * ψ (1 + a₀⁻¹ * u) * (χ (-a₀) * χ (1 - (1 + a₀⁻¹ * u))) := by rw [map_mul, map_mul]
      _ = ψ a₀ * χ (-a₀) * (ψ (1 + a₀⁻¹ * u) * χ (1 - (1 + a₀⁻¹ * u))) := by ring
  rw [hrew, norm_mul, norm_mul]
  have h1 : ‖ψ a₀‖ = 1 := by
    have hu : IsUnit a₀ := isUnit_iff_ne_zero.mpr ha₀
    rw [← hu.unit_spec]
    exact Complex.norm_eq_one_of_mem_rootsOfUnity (ψ.apply_mem_rootsOfUnity hu.unit)
  have h2 : ‖χ (-a₀)‖ = 1 := by
    have hu : IsUnit (-a₀) := isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr ha₀)
    rw [← hu.unit_spec]
    exact Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity hu.unit)
  rw [h1, h2, one_mul, one_mul]

omit [DecidableEq F] in
lemma norm_jacobiSum_one_nontrivial {χ : MulChar F ℂ} (hχ : χ ≠ 1) :
    ‖jacobiSum (1 : MulChar F ℂ) χ‖ = 1 := by
  rw [jacobiSum_one_nontrivial hχ, norm_neg, norm_one]

lemma norm_jacobiSum_le_sqrt {ψ χ : MulChar F ℂ} (hψ : ψ ≠ 1) (hχ : χ ≠ 1) :
    ‖jacobiSum ψ χ‖ ≤ Real.sqrt (Fintype.card F) := by
  by_cases hmul : ψ * χ = 1
  · have hχ_eq : χ = ψ⁻¹ := eq_inv_of_mul_eq_one_right hmul
    rw [hχ_eq, jacobiSum_nontrivial_inv hψ, norm_neg]
    have h1 : ‖ψ (-1)‖ = 1 := by
      have hu : IsUnit (-1 : F) := isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero)
      rw [← hu.unit_spec]
      exact Complex.norm_eq_one_of_mem_rootsOfUnity (ψ.apply_mem_rootsOfUnity hu.unit)
    rw [h1]
    exact Real.one_le_sqrt.mpr (by exact_mod_cast Nat.one_le_of_lt Fintype.one_lt_card)
  · have hchar : ringChar ℂ ≠ ringChar F := by
      rw [ringChar.eq_zero]
      obtain ⟨p, _, _, hp, _⟩ := FiniteField.card' F
      rw [ringChar.eq F p]
      exact hp.ne_zero.symm
    have hprod := jacobiSum_mul_jacobiSum_inv hchar hψ hχ hmul
    have hstar : jacobiSum ψ⁻¹ χ⁻¹ = starRingEnd ℂ (jacobiSum ψ χ) := by
      simp only [jacobiSum, map_sum, map_mul, ← RCLike.star_def, MulChar.star_apply']
    rw [hstar, Complex.mul_conj'] at hprod
    have hsq : ‖jacobiSum ψ χ‖ ^ 2 = (Fintype.card F : ℝ) := by
      exact_mod_cast congrArg Complex.re hprod
    rw [← Real.sqrt_sq (norm_nonneg _), hsq]

/-- Pick a generating multiplicative character `χ₀ : MulChar F ℂ` of exact order `n = card F - 1`. -/
lemma exists_gen_mulChar :
    ∃ χ₀ : MulChar F ℂ,
      (∀ k : ℕ, χ₀ ^ k = 1 ↔ Fintype.card Fˣ ∣ k) ∧
      (∀ u : Fˣ, ∑ k : Fin (Fintype.card Fˣ), (χ₀ ^ k.val) u =
        if u = 1 then (Fintype.card Fˣ : ℂ) else 0) := by
  let n := Fintype.card Fˣ
  have hn : 0 < n := Fintype.card_pos
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  let ζu : ℂˣ := (hζ.isUnit hn.ne').unit
  have hζmem : ζu ∈ rootsOfUnity n ℂ := by
    rw [mem_rootsOfUnity]
    exact Units.ext (by push_cast; exact hζ.pow_eq_one)
  let χ₀ : MulChar F ℂ := MulChar.ofRootOfUnity hζmem hg
  have hχ₀g : χ₀ g = ζ := by
    simpa [χ₀, ζu] using MulChar.ofRootOfUnity_spec hζmem hg
  have hord : ∀ k : ℕ, χ₀ ^ k = 1 ↔ n ∣ k := by
    intro k
    rw [MulChar.eq_iff hg, MulChar.one_apply_coe, MulChar.pow_apply_coe, hχ₀g]
    exact hζ.pow_eq_one_iff_dvd k
  refine ⟨χ₀, hord, fun u => ?_⟩
  have hpow : ∀ k : ℕ, (χ₀ ^ k) u = (χ₀ u) ^ k := fun k => MulChar.pow_apply_coe χ₀ k u
  simp_rw [hpow, Fin.sum_univ_eq_sum_range]
  by_cases hu : u = 1
  · subst hu; simp
  · rw [if_neg hu]
    have hne1 : χ₀ u ≠ 1 := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
      have hm_ndvd : ¬ (n : ℤ) ∣ m := by
        intro hdvd
        obtain ⟨q, rfl⟩ := hdvd
        apply hu
        rw [← hm, zpow_mul, zpow_natCast, pow_card_eq_one, one_zpow]
      have hχu : χ₀ u = ζ ^ m := by
        have h1 : χ₀ u = ((χ₀.toUnitHom u : ℂˣ) : ℂ) := rfl
        have h2 : χ₀.toUnitHom u = (χ₀.toUnitHom g) ^ m := by rw [← hm, map_zpow]
        have h3 : ((χ₀.toUnitHom g : ℂˣ) : ℂ) = ζ := hχ₀g
        rw [h1, h2, Units.val_zpow_eq_zpow_val, h3]
      rw [hχu]
      intro h1
      exact hm_ndvd ((hζ.zpow_eq_one_iff_dvd m).mp h1)
    rw [geom_sum_eq hne1]
    have hzn : (χ₀ u) ^ n = 1 := by
      rw [← hpow, (hord n).mpr dvd_rfl, MulChar.one_apply_coe]
    rw [hzn, sub_self, zero_div]

/-- Finite-field Expander Mixing Lemma on `Fˣ` with exact `(1 - |X|/n)(1 - |Y|/n)` variance factor! -/
theorem expander_mixing (f : Fˣ → ℝ) (X Y : Finset Fˣ)
    {χ₀ : MulChar F ℂ}
    (_hord : ∀ k : ℕ, χ₀ ^ k = 1 ↔ Fintype.card Fˣ ∣ k)
    (horth : ∀ u : Fˣ, ∑ k : Fin (Fintype.card Fˣ), (χ₀ ^ k.val) u =
      if u = 1 then (Fintype.card Fˣ : ℂ) else 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hhat : ∀ k : Fin (Fintype.card Fˣ), k.val ≠ 0 →
      ‖∑ u : Fˣ, (f u : ℂ) * (χ₀ ^ k.val) u‖ ≤ M) :
    let n : ℝ := Fintype.card Fˣ
    let μ : ℝ := (∑ u : Fˣ, f u) / n
    |∑ x ∈ X, ∑ y ∈ Y, f (x * y) - μ * X.card * Y.card| ≤
      M * Real.sqrt (X.card * (1 - X.card / n) * (Y.card * (1 - Y.card / n))) := by
  intro n μ
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr Fintype.card_pos
  have hn_ne : (Fintype.card Fˣ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- Fourier identity: n * ∑_{x ∈ X, y ∈ Y} f(xy) = ∑_k hat(f)(k) * (∑_{x ∈ X} χ_k⁻¹ x) * (∑_{y ∈ Y} χ_k⁻¹ y)
  let hatF : Fin (Fintype.card Fˣ) → ℂ := fun k => ∑ u : Fˣ, (f u : ℂ) * (χ₀ ^ k.val) u
  let sX : Fin (Fintype.card Fˣ) → ℂ := fun k => ∑ x ∈ X, (χ₀ ^ k.val)⁻¹ x
  let sY : Fin (Fintype.card Fˣ) → ℂ := fun k => ∑ y ∈ Y, (χ₀ ^ k.val)⁻¹ y
  have hfour : (Fintype.card Fˣ : ℂ) * ∑ x ∈ X, ∑ y ∈ Y, (f (x * y) : ℂ) =
      ∑ k : Fin (Fintype.card Fˣ), hatF k * sX k * sY k := by
    have hrhs : ∑ k : Fin (Fintype.card Fˣ), hatF k * sX k * sY k =
        ∑ x ∈ X, ∑ y ∈ Y, ∑ u : Fˣ, (f u : ℂ) *
          ∑ k : Fin (Fintype.card Fˣ), (χ₀ ^ k.val) ((u * (x * y)⁻¹ : Fˣ) : F) := by
      have hterm : ∀ k : Fin (Fintype.card Fˣ),
          hatF k * sX k * sY k =
          ∑ x ∈ X, ∑ y ∈ Y, ∑ u : Fˣ, (f u : ℂ) * (χ₀ ^ k.val) ((u * (x * y)⁻¹ : Fˣ) : F) := by
        intro k
        calc hatF k * sX k * sY k
            = ∑ y ∈ Y, ∑ x ∈ X, ∑ u : Fˣ, ((f u : ℂ) * (χ₀ ^ k.val) u) * (χ₀ ^ k.val)⁻¹ x * (χ₀ ^ k.val)⁻¹ y := by
                simp only [hatF, sX, sY, Finset.mul_sum, Finset.sum_mul]
          _ = ∑ x ∈ X, ∑ y ∈ Y, ∑ u : Fˣ, ((f u : ℂ) * (χ₀ ^ k.val) u) * (χ₀ ^ k.val)⁻¹ x * (χ₀ ^ k.val)⁻¹ y :=
                Finset.sum_comm
          _ = ∑ x ∈ X, ∑ y ∈ Y, ∑ u : Fˣ, (f u : ℂ) * (χ₀ ^ k.val) ((u * (x * y)⁻¹ : Fˣ) : F) := by
                refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
                  Finset.sum_congr rfl fun u _ => ?_
                rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mul, mul_inv,
                  map_mul, map_mul, MulChar.inv_apply', MulChar.inv_apply']
                ring
      simp_rw [hterm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => (Finset.mul_sum ..).symm
    rw [hrhs]
    simp_rw [horth]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_eq_single (x * y)]
    · rw [mul_inv_cancel, if_pos rfl, mul_comm]
    · intro u _ hne
      have h1 : u * (x * y)⁻¹ ≠ 1 := fun h => hne (eq_of_mul_inv_eq_one h)
      rw [if_neg h1, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- Parseval on sX and sY: ∑_{k ≠ 0} ‖sX k‖^2 = n * |X| - |X|^2
  have hpars : ∀ Z : Finset Fˣ,
      ∑ k ∈ Finset.univ.filter (fun k : Fin (Fintype.card Fˣ) => k.val ≠ 0),
        ‖∑ x ∈ Z, (χ₀ ^ k.val)⁻¹ x‖ ^ 2 = n * Z.card - (Z.card : ℝ) ^ 2 := by
    intro Z
    have htot : ∑ k : Fin (Fintype.card Fˣ),
        (∑ x ∈ Z, (χ₀ ^ k.val)⁻¹ x) * star (∑ y ∈ Z, (χ₀ ^ k.val)⁻¹ y) =
        (Fintype.card Fˣ : ℂ) * Z.card := by
      have h1 : ∀ k : Fin (Fintype.card Fˣ),
          (∑ x ∈ Z, (χ₀ ^ k.val)⁻¹ x) * star (∑ y ∈ Z, (χ₀ ^ k.val)⁻¹ y) =
          ∑ x ∈ Z, ∑ y ∈ Z, (χ₀ ^ k.val) ((y * x⁻¹ : Fˣ) : F) := by
        intro k
        rw [star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [MulChar.star_apply', inv_inv, MulChar.inv_apply', Units.val_mul, Units.val_inv_eq_inv_val,
          map_mul, mul_comm]
      simp_rw [h1]
      rw [Finset.sum_comm]
      conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
      simp_rw [horth]
      have hinner : ∀ x ∈ Z, ∑ y ∈ Z, (if y * x⁻¹ = 1 then (Fintype.card Fˣ : ℂ) else 0) =
          (Fintype.card Fˣ : ℂ) := by
        intro x hx
        rw [Finset.sum_eq_single x]
        · simp [mul_inv_cancel]
        · intro y _ hyx; simp [show y * x⁻¹ ≠ 1 from fun h => hyx (eq_of_mul_inv_eq_one h)]
        · intro h; exact absurd hx h
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul, mul_comm]
    -- Split off k = 0
    let k0 : Fin (Fintype.card Fˣ) := ⟨0, Fintype.card_pos⟩
    have hsplit := Finset.sum_erase_add (s := Finset.univ)
      (f := fun k : Fin (Fintype.card Fˣ) =>
        (∑ x ∈ Z, (χ₀ ^ k.val)⁻¹ x) * star (∑ y ∈ Z, (χ₀ ^ k.val)⁻¹ y)) (Finset.mem_univ k0)
    have hk0_val : (∑ x ∈ Z, (χ₀ ^ k0.val)⁻¹ x) * star (∑ y ∈ Z, (χ₀ ^ k0.val)⁻¹ y) =
        ((Z.card : ℂ) ^ 2) := by
      simp only [k0, pow_zero, inv_one, MulChar.one_apply_coe, Finset.sum_const, nsmul_eq_mul, mul_one,
        star_natCast, sq]
    rw [hk0_val] at hsplit
    have herase : Finset.univ.erase k0 =
        Finset.univ.filter (fun k : Fin (Fintype.card Fˣ) => k.val ≠ 0) := by
      ext k; simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_filter, true_and, ne_eq, Fin.ext_iff]; rfl
    rw [herase] at hsplit
    have hre := congrArg Complex.re (hsplit.trans htot)
    simp only [Complex.add_re, Complex.re_sum, RCLike.star_def, Complex.mul_conj', ← Complex.ofReal_pow,
      Complex.ofReal_re] at hre
    have hre_rhs : ((Fintype.card Fˣ : ℂ) * Z.card).re = n * Z.card := by simp [n]
    have hre_sq : ((Z.card : ℂ) ^ 2).re = (Z.card : ℝ) ^ 2 := by simp [sq]
    rw [hre_rhs, hre_sq] at hre
    linarith
  -- Split off k = 0 in hfour and apply triangle inequality + Cauchy-Schwarz!
  let k0 : Fin (Fintype.card Fˣ) := ⟨0, Fintype.card_pos⟩
  have hsplit := Finset.sum_erase_add (s := Finset.univ)
    (f := fun k => hatF k * sX k * sY k) (Finset.mem_univ k0)
  have hk0 : hatF k0 * sX k0 * sY k0 = ((∑ u : Fˣ, f u : ℝ) : ℂ) * (X.card : ℂ) * (Y.card : ℂ) := by
    simp [hatF, sX, sY, k0]
  rw [hk0] at hsplit
  have herase : Finset.univ.erase k0 =
      Finset.univ.filter (fun k : Fin (Fintype.card Fˣ) => k.val ≠ 0) := by
    ext k; simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_filter, true_and, ne_eq, Fin.ext_iff]; rfl
  rw [herase] at hsplit
  have hdiff : ((n * (∑ x ∈ X, ∑ y ∈ Y, f (x * y) - μ * X.card * Y.card) : ℝ) : ℂ) =
      ∑ k ∈ Finset.univ.filter (fun k : Fin (Fintype.card Fˣ) => k.val ≠ 0),
        hatF k * sX k * sY k := by
    have h1 : (Fintype.card Fˣ : ℂ) * ∑ x ∈ X, ∑ y ∈ Y, (f (x * y) : ℂ) -
        ((∑ u : Fˣ, f u : ℝ) : ℂ) * (X.card : ℂ) * (Y.card : ℂ) =
        ∑ k ∈ Finset.univ.filter (fun k : Fin (Fintype.card Fˣ) => k.val ≠ 0),
          hatF k * sX k * sY k := by
      rw [hfour, ← hsplit]; ring
    rw [← h1]
    have hμn : n * μ = ∑ u : Fˣ, f u := mul_div_cancel₀ _ hn_pos.ne'
    have hcast : (n * (∑ x ∈ X, ∑ y ∈ Y, f (x * y) - μ * X.card * Y.card) : ℝ) =
        n * (∑ x ∈ X, ∑ y ∈ Y, f (x * y)) - (∑ u : Fˣ, f u) * X.card * Y.card := by
      calc n * (∑ x ∈ X, ∑ y ∈ Y, f (x * y) - μ * X.card * Y.card)
          = n * (∑ x ∈ X, ∑ y ∈ Y, f (x * y)) - (n * μ) * X.card * Y.card := by ring
        _ = _ := by rw [hμn]
    rw [hcast]
    push_cast
    rfl
  have hnorm_eq : n * |∑ x ∈ X, ∑ y ∈ Y, f (x * y) - μ * X.card * Y.card| =
      ‖∑ k ∈ Finset.univ.filter (fun k : Fin (Fintype.card Fˣ) => k.val ≠ 0),
        hatF k * sX k * sY k‖ := by
    rw [← hdiff, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hn_pos]
  let S := Finset.univ.filter (fun k : Fin (Fintype.card Fˣ) => k.val ≠ 0)
  have htri : ‖∑ k ∈ S, hatF k * sX k * sY k‖ ≤ M * ∑ k ∈ S, ‖sX k‖ * ‖sY k‖ := by
    calc ‖∑ k ∈ S, hatF k * sX k * sY k‖
        ≤ ∑ k ∈ S, ‖hatF k * sX k * sY k‖ := norm_sum_le _ _
      _ = ∑ k ∈ S, ‖hatF k‖ * (‖sX k‖ * ‖sY k‖) := by simp [mul_assoc]
      _ ≤ ∑ k ∈ S, M * (‖sX k‖ * ‖sY k‖) := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_right (hhat k (Finset.mem_filter.mp hk).2) (by positivity)
      _ = M * ∑ k ∈ S, ‖sX k‖ * ‖sY k‖ := (Finset.mul_sum ..).symm
  have hcs : ∑ k ∈ S, ‖sX k‖ * ‖sY k‖ ≤
      Real.sqrt (∑ k ∈ S, ‖sX k‖ ^ 2) * Real.sqrt (∑ k ∈ S, ‖sY k‖ ^ 2) := by
    have hsq := Finset.sum_mul_sq_le_sq_mul_sq S (fun k => ‖sX k‖) (fun k => ‖sY k‖)
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Real.le_sqrt_of_sq_le hsq
  have hpX := hpars X
  have hpY := hpars Y
  have hSX_nn : 0 ≤ n * X.card - (X.card : ℝ) ^ 2 := by
    rw [← hpX]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSY_nn : 0 ≤ n * Y.card - (Y.card : ℝ) ^ 2 := by
    rw [← hpY]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbound : n * |∑ x ∈ X, ∑ y ∈ Y, f (x * y) - μ * X.card * Y.card| ≤
      M * Real.sqrt ((n * X.card - (X.card : ℝ) ^ 2) * (n * Y.card - (Y.card : ℝ) ^ 2)) := by
    rw [hnorm_eq]
    calc ‖∑ k ∈ S, hatF k * sX k * sY k‖
        ≤ M * ∑ k ∈ S, ‖sX k‖ * ‖sY k‖ := htri
      _ ≤ M * (Real.sqrt (∑ k ∈ S, ‖sX k‖ ^ 2) * Real.sqrt (∑ k ∈ S, ‖sY k‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hcs hM
      _ = M * Real.sqrt ((n * X.card - (X.card : ℝ) ^ 2) * (n * Y.card - (Y.card : ℝ) ^ 2)) := by
          rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _), hpX, hpY]
  -- Divide by n > 0!
  have hrew_sq : (n * X.card - (X.card : ℝ) ^ 2) * (n * Y.card - (Y.card : ℝ) ^ 2) =
      n ^ 2 * (X.card * (1 - X.card / n) * (Y.card * (1 - Y.card / n))) := by
    field_simp [hn_pos.ne']
  rw [hrew_sq, Real.sqrt_mul (sq_nonneg n), Real.sqrt_sq hn_pos.le] at hbound
  nlinarith

end CharacterEngine

section PrimeSieves

open Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `x` is nonzero and not a `p`-th power in `Fˣ`. -/
def isPFree (p : ℕ) (x : F) : Prop :=
  x ≠ 0 ∧ ∀ y : Fˣ, (y : F) ^ p ≠ x

noncomputable def indP (p : ℕ) (x : F) : ℝ :=
  if isPFree p x then 1 else 0

noncomputable def indE (E : Finset ℕ) (x : F) : ℝ :=
  if x = 0 then 0 else ∏ p ∈ E, indP p x

noncomputable def theta (E : Finset ℕ) : ℝ :=
  ∏ p ∈ E, (1 - 1 / (p : ℝ))

lemma theta_pos {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) : 0 < theta E := by
  apply Finset.prod_pos
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hE p hp).two_le
  have hp_pos : (0 : ℝ) < p := by linarith
  rw [sub_pos, div_lt_one hp_pos]
  linarith

omit [Fintype F] in
lemma indE_empty (x : F) : indE ∅ x = if x = 0 then 0 else 1 := by
  simp [indE]

omit [Fintype F] in
lemma indE_insert {E : Finset ℕ} {p : ℕ} (hp : p ∉ E) (x : F) :
    indE (insert p E) x = indP p x * indE E x := by
  by_cases hx : x = 0
  · simp [indE, hx]
  · simp [indE, hx, Finset.prod_insert hp]

omit [Fintype F] [DecidableEq F] in
lemma indP_nonneg (p : ℕ) (x : F) : 0 ≤ indP p x := by
  classical unfold indP; split_ifs <;> norm_num

omit [Fintype F] [DecidableEq F] in
lemma indP_le_one (p : ℕ) (x : F) : indP p x ≤ 1 := by
  classical unfold indP; split_ifs <;> norm_num

omit [Fintype F] in
lemma indE_zero_or_one (E : Finset ℕ) (x : F) : indE E x = 0 ∨ indE E x = 1 := by
  classical
  by_cases hx : x = 0
  · left; simp [indE, hx]
  · simp only [indE, hx, ↓reduceIte]
    induction E using Finset.induction_on with
    | empty => right; simp
    | @insert p s hp ih =>
      rw [Finset.prod_insert hp]
      rcases ih with h | h <;> rw [h] <;> unfold indP <;> split_ifs <;> norm_num

omit [Fintype F] in
lemma indE_mono {E₁ E₂ : Finset ℕ} (hsub : E₁ ⊆ E₂) (x : F) : indE E₂ x ≤ indE E₁ x := by
  by_cases hx : x = 0
  · simp [indE, hx]
  · simp only [indE, hx, ↓reduceIte]
    have hsplit : ∏ p ∈ E₂, indP p x = (∏ p ∈ E₁, indP p x) * (∏ p ∈ E₂ \ E₁, indP p x) := by
      rw [← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hsub]
    rw [hsplit]
    have h1 : 0 ≤ ∏ p ∈ E₁, indP p x := Finset.prod_nonneg fun p _ => indP_nonneg p x
    have h2 : ∏ p ∈ E₂ \ E₁, indP p x ≤ 1 :=
      Finset.prod_le_one (fun p _ => indP_nonneg p x) (fun p _ => indP_le_one p x)
    nlinarith

lemma indE_primeFactors_eq_prim (x : F) :
    indE (Fintype.card Fˣ).primeFactors x =
      if IsPrimitiveRoot x (Fintype.card Fˣ) then 1 else 0 := by
  let n := Fintype.card Fˣ
  have hn_pos : 0 < n := Fintype.card_pos
  have hiff : (x ≠ 0 ∧ ∀ p ∈ n.primeFactors, isPFree p x) ↔ IsPrimitiveRoot x n := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    have hord_g : orderOf g = n := (orderOf_eq_card_of_forall_mem_zpowers hg).trans Nat.card_eq_fintype_card
    have hg_prim : IsPrimitiveRoot (g : F) n := by
      rw [IsPrimitiveRoot.iff_def]
      refine ⟨by rw [← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one], fun l hl => ?_⟩
      have hl' : g ^ l = 1 := Units.ext (by simpa using hl)
      rw [← hord_g]
      exact orderOf_dvd_of_pow_eq_one hl'
    constructor
    · rintro ⟨hx0, hfree⟩
      let xu : Fˣ := Units.mk0 x hx0
      obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff.mp (hg xu))
      -- Reduce k mod n to a Nat m < n with g^m = xu!
      let m : ℕ := (k % (n : ℤ)).toNat
      have hm_eq : g ^ m = xu := by
        have hmod : (m : ℤ) = k % (n : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg k (by positivity))
        have hdiv : k = (n : ℤ) * (k / n) + k % n := (Int.mul_ediv_add_emod k n).symm
        rw [← hk]
        have : g ^ (m : ℤ) = g ^ k := by
          rw [hmod]
          conv_rhs => rw [hdiv, zpow_add, zpow_mul, zpow_natCast, pow_card_eq_one, one_zpow, one_mul]
        simpa [zpow_natCast] using this
      have hcop : Nat.Coprime m n := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hne
        have hpm : p ∣ m := hp_dvd.trans (Nat.gcd_dvd_left m n)
        have hpn : p ∣ n := hp_dvd.trans (Nat.gcd_dvd_right m n)
        have hp_mem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp_prime, hpn, hn_pos.ne'⟩
        obtain ⟨q, hq⟩ := hpm
        apply (hfree p hp_mem).2 (g ^ q)
        have : ((g ^ q : Fˣ) : F) ^ p = (g ^ m : Fˣ) := by
          rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm q p, ← hq]
        rw [this, hm_eq]; rfl
      have : (g : F) ^ m = x := by
        have := congrArg Units.val hm_eq
        simpa [xu] using this
      rw [← this]
      exact hg_prim.pow_of_coprime m hcop
    · intro hprim
      have hx0 : x ≠ 0 := hprim.ne_zero hn_pos.ne'
      refine ⟨hx0, fun p hp => ⟨hx0, fun y hy => ?_⟩⟩
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hp_dvd := Nat.dvd_of_mem_primeFactors hp
      have hpow : x ^ (n / p) = 1 := by
        rw [← hy, ← pow_mul, Nat.mul_div_cancel' hp_dvd]
        rw [← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one]
      have hdvd := hprim.dvd_of_pow_eq_one (n / p) hpow
      have hlt : n / p < n := Nat.div_lt_self hn_pos hp_prime.one_lt
      have hpos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn_pos hp_dvd) hp_prime.pos
      exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)
  by_cases h : IsPrimitiveRoot x n
  · rw [if_pos h]
    obtain ⟨hx0, hfree⟩ := hiff.mpr h
    simp only [indE, hx0, ↓reduceIte]
    exact Finset.prod_eq_one fun p hp => by simp [indP, hfree p hp]
  · rw [if_neg h]
    by_cases hx0 : x = 0
    · simp [indE, hx0]
    · simp only [indE, hx0, ↓reduceIte]
      have hnot : ¬ ∀ p ∈ n.primeFactors, isPFree p x := fun hall => h (hiff.mp ⟨hx0, hall⟩)
      push Not at hnot
      obtain ⟨p, hp, hnp⟩ := hnot
      exact Finset.prod_eq_zero hp (by simp [indP, hnp])

/-- Character expansion of `indP p x` for any prime `p ∣ Fintype.card Fˣ`. -/
lemma indP_eq_char_sum {χ₀ : MulChar F ℂ}
    (hord : ∀ k : ℕ, χ₀ ^ k = 1 ↔ Fintype.card Fˣ ∣ k)
    {p : ℕ} (hp : p.Prime) (hpdvd : p ∣ Fintype.card Fˣ) (x : F) :
    (indP p x : ℂ) =
      (1 - 1 / (p : ℂ)) * (1 : MulChar F ℂ) x -
      (1 / (p : ℂ)) * ∑ j ∈ Finset.Ico 1 p, (χ₀ ^ (j * (Fintype.card Fˣ / p))) x := by
  let n := Fintype.card Fˣ
  have hp_pos : 0 < p := hp.pos
  have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  by_cases hx : x = 0
  · subst hx
    have hnot : ¬ isPFree p (0 : F) := fun h => h.1 rfl
    simp [indP, hnot, MulChar.map_zero]
  · let xu : Fˣ := Units.mk0 x hx
    have h1x : (1 : MulChar F ℂ) x = 1 := MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
    -- Compute ∑ j ∈ range p, (χ₀ ^ (j * (n/p))) x
    let ψ : MulChar F ℂ := χ₀ ^ (n / p)
    have hψ_pow : ∀ j : ℕ, (χ₀ ^ (j * (n / p))) x = (ψ x) ^ j := by
      intro j
      change (χ₀ ^ (j * (n / p))) (xu : F) = (ψ (xu : F)) ^ j
      have h1 : (χ₀ ^ (j * (n / p))) (xu : F) = ((χ₀ ^ (n / p)) ^ j) (xu : F) := by
        rw [← pow_mul, mul_comm]
      rw [h1, MulChar.pow_apply_coe]
    have hψ_ord_p : (ψ x) ^ p = 1 := by
      have h1 : (ψ ^ p) xu = (1 : MulChar F ℂ) xu := by
        have hpow : ψ ^ p = χ₀ ^ n := by
          dsimp [ψ]; rw [← pow_mul, Nat.div_mul_cancel hpdvd]
        rw [hpow, (hord n).mpr dvd_rfl]
      rw [MulChar.pow_apply_coe, MulChar.one_apply_coe] at h1
      simpa [xu] using h1
    -- Equivalence: ψ x = 1 ↔ ∃ y : Fˣ, y ^ p = xu!
    have hψ_eq_one_iff : ψ x = 1 ↔ ∃ y : Fˣ, (y : F) ^ p = x := by
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
      have hg_n : ∀ m : ℕ, χ₀ (g ^ m : Fˣ) = 1 ↔ n ∣ m := by
        intro m
        have h1 : χ₀ (g ^ m : Fˣ) = (χ₀ ^ m) g := by
          rw [MulChar.pow_apply_coe, Units.val_pow_eq_pow_val, map_pow]
        rw [h1, ← MulChar.one_apply_coe (R := F) (R' := ℂ) g, ← MulChar.eq_iff hg, hord]
      constructor
      · intro hψ1
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg xu)
        let m : ℕ := (k % (n : ℤ)).toNat
        have hm_eq : g ^ m = xu := by
          have hmod : (m : ℤ) = k % (n : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg k (by positivity))
          have hdiv : k = (n : ℤ) * (k / n) + k % n := (Int.mul_ediv_add_emod k n).symm
          rw [← hk]
          have : g ^ (m : ℤ) = g ^ k := by
            rw [hmod]
            conv_rhs => rw [hdiv, zpow_add, zpow_mul, zpow_natCast, pow_card_eq_one, one_zpow, one_mul]
          simpa [zpow_natCast] using this
        have hχm : χ₀ (g ^ (m * (n / p)) : Fˣ) = 1 := by
          have h1 : (g ^ (m * (n / p)) : Fˣ) = xu ^ (n / p) := by rw [pow_mul, hm_eq]
          rw [h1, Units.val_pow_eq_pow_val, map_pow]
          have h2 : (χ₀ (xu : F)) ^ (n / p) = ψ x := by
            simpa [ψ, xu] using (MulChar.pow_apply_coe χ₀ (n / p) xu).symm
          rw [h2, hψ1]
        have hdvd : n ∣ m * (n / p) := (hg_n _).mp hχm
        have hpm : p ∣ m := by
          obtain ⟨t, ht⟩ := hdvd
          have hmul : (n / p) * (p * t) = (n / p) * m := by
            calc (n / p) * (p * t) = ((n / p) * p) * t := by ring
              _ = n * t := by rw [Nat.div_mul_cancel hpdvd]
              _ = m * (n / p) := ht.symm
              _ = (n / p) * m := mul_comm _ _
          have hpos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd Fintype.card_pos hpdvd) hp_pos
          exact ⟨t, (Nat.mul_left_cancel hpos hmul).symm⟩
        obtain ⟨q, hqm⟩ := hpm
        refine ⟨g ^ q, ?_⟩
        have : ((g ^ q : Fˣ) : F) ^ p = (g ^ m : Fˣ) := by
          rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm q p, ← hqm]
        rw [this, hm_eq]; rfl
      · rintro ⟨y, hy⟩
        have hyu : y ^ p = xu := Units.ext (by simpa [xu] using hy)
        have h1 : ψ x = (χ₀ y) ^ (p * (n / p)) := by
          have h2 : ψ x = (χ₀ x) ^ (n / p) := by
            simpa [ψ, xu] using MulChar.pow_apply_coe χ₀ (n / p) xu
          rw [h2, ← hy, map_pow, ← pow_mul]
        rw [h1, Nat.mul_div_cancel' hpdvd]
        have h3 : (χ₀ y) ^ n = (χ₀ ^ n) y := (MulChar.pow_apply_coe χ₀ n y).symm
        rw [h3, (hord n).mpr dvd_rfl, MulChar.one_apply_coe]
    -- Compute the sum over j ∈ Ico 1 p using geom_sum_eq!
    have hsplit : ∑ j ∈ Finset.range p, (ψ x) ^ j = 1 + ∑ j ∈ Finset.Ico 1 p, (ψ x) ^ j := by
      have hset : Finset.range p = insert 0 (Finset.Ico 1 p) := by
        ext j; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
      rw [hset, Finset.sum_insert (by simp), pow_zero]
    have hIco_eq : ∑ j ∈ Finset.Ico 1 p, (χ₀ ^ (j * (n / p))) x =
        ∑ j ∈ Finset.Ico 1 p, (ψ x) ^ j := Finset.sum_congr rfl fun j _ => hψ_pow j
    rw [hIco_eq, h1x, mul_one]
    by_cases hpow_ex : ∃ y : Fˣ, (y : F) ^ p = x
    · have hnf : ¬ isPFree p x := fun h => by obtain ⟨y, hy⟩ := hpow_ex; exact h.2 y hy
      have hψ1 : ψ x = 1 := hψ_eq_one_iff.mpr hpow_ex
      have hsum : ∑ j ∈ Finset.Ico 1 p, (ψ x) ^ j = (p : ℂ) - 1 := by
        simp [hψ1, Nat.cast_sub hp.one_le]
      simp only [indP, hnf, ↓reduceIte, Complex.ofReal_zero, hsum]
      field_simp [hp_ne]
      ring
    · have hf : isPFree p x := ⟨hx, fun y hy => hpow_ex ⟨y, hy⟩⟩
      have hψne : ψ x ≠ 1 := fun h => hpow_ex (hψ_eq_one_iff.mp h)
      have hgeom : ∑ j ∈ Finset.range p, (ψ x) ^ j = 0 := by
        rw [geom_sum_eq hψne, hψ_ord_p, sub_self, zero_div]
      have hsum : ∑ j ∈ Finset.Ico 1 p, (ψ x) ^ j = -1 := by
        linear_combination hgeom - hsplit
      simp only [indP, hf, ↓reduceIte, Complex.ofReal_one, hsum]
      field_simp [hp_ne]
      ring

/-- Helper: order of `χ₀ ^ (j * (n / p))` is `p` when `p` is prime, `p ∣ n`, and `1 ≤ j < p`. -/
lemma orderOf_char_prime {χ₀ : MulChar F ℂ}
    (hord : ∀ k : ℕ, χ₀ ^ k = 1 ↔ Fintype.card Fˣ ∣ k)
    {p j : ℕ} (hp : p.Prime) (hpdvd : p ∣ Fintype.card Fˣ) (hj1 : 1 ≤ j) (hjp : j < p) :
    orderOf (χ₀ ^ (j * (Fintype.card Fˣ / p))) = p := by
  let n := Fintype.card Fˣ
  have hpow_p : (χ₀ ^ (j * (n / p))) ^ p = 1 := by
    rw [← pow_mul, hord, mul_assoc, Nat.div_mul_cancel hpdvd]
    exact dvd_mul_left n j
  have hne1 : χ₀ ^ (j * (n / p)) ≠ 1 := by
    intro h1
    have hdvd := (hord _).mp h1
    obtain ⟨t, ht⟩ := hdvd
    have hpos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd Fintype.card_pos hpdvd) hp.pos
    have hmul : (n / p) * (p * t) = (n / p) * j := by
      calc (n / p) * (p * t) = ((n / p) * p) * t := by ring
        _ = n * t := by rw [Nat.div_mul_cancel hpdvd]
        _ = j * (n / p) := ht.symm
        _ = (n / p) * j := mul_comm _ _
    have hpj : p ∣ j := ⟨t, (Nat.mul_left_cancel hpos hmul).symm⟩
    exact absurd (Nat.le_of_dvd (by omega) hpj) (not_le.mpr hjp)
  have hdvd_p : orderOf (χ₀ ^ (j * (n / p))) ∣ p := orderOf_dvd_of_pow_eq_one hpow_p
  rcases hp.eq_one_or_self_of_dvd _ hdvd_p with h1 | hself
  · exact absurd (orderOf_eq_one_iff.mp h1) hne1
  · exact hself

/-- Exact principal sum `∑ x : F, ψ x * indE E x` by Finset induction on `E` (5-line proof!). -/
lemma sum_mul_indE {χ₀ : MulChar F ℂ}
    (hord : ∀ k : ℕ, χ₀ ^ k = 1 ↔ Fintype.card Fˣ ∣ k)
    (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime ∧ p ∣ Fintype.card Fˣ) :
    ∀ ψ : MulChar F ℂ, (orderOf ψ).Coprime (∏ p ∈ E, p) →
      ∑ x : F, ψ x * (indE E x : ℂ) =
        if ψ = 1 then (theta E : ℂ) * (Fintype.card Fˣ : ℂ) else 0 := by
  induction E using Finset.induction_on with
  | empty =>
    intro ψ _
    have hrew : ∀ x : F, ψ x * (indE ∅ x : ℂ) = ψ x := by
      intro x; by_cases hx : x = 0 <;> simp [indE_empty, hx, MulChar.map_zero]
    simp_rw [hrew]
    split_ifs with hψ
    · subst hψ; simp [theta, MulChar.sum_one_eq_card_units]
    · exact MulChar.sum_eq_zero_of_ne_one hψ
  | @insert p s hp ih =>
    intro ψ hcop
    have hp_spec := hE p (Finset.mem_insert_self p s)
    have hs_spec : ∀ r ∈ s, r.Prime ∧ r ∣ Fintype.card Fˣ :=
      fun r hr => hE r (Finset.mem_insert_of_mem hr)
    rw [Finset.prod_insert hp] at hcop
    have hcop_p : (orderOf ψ).Coprime p := (Nat.coprime_mul_iff_right.mp hcop).1
    have hcop_s : (orderOf ψ).Coprime (∏ r ∈ s, r) := (Nat.coprime_mul_iff_right.mp hcop).2
    have hrew : ∀ x : F, ψ x * (indE (insert p s) x : ℂ) =
        (1 - 1 / (p : ℂ)) * (ψ x * (indE s x : ℂ)) -
        (1 / (p : ℂ)) * ∑ j ∈ Finset.Ico 1 p,
          ((ψ * χ₀ ^ (j * (Fintype.card Fˣ / p))) x * (indE s x : ℂ)) := by
      intro x
      rw [indE_insert hp, Complex.ofReal_mul, indP_eq_char_sum hord hp_spec.1 hp_spec.2]
      by_cases hx : x = 0
      · simp [hx, indE]
      · have h1x : (1 : MulChar F ℂ) x = 1 := MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
        simp only [h1x, mul_one, MulChar.mul_apply]
        have hdist : ψ x * (-(1 / (p : ℂ)) * (∑ j ∈ Finset.Ico 1 p, (χ₀ ^ (j * (Fintype.card Fˣ / p))) x) * (indE s x : ℂ)) =
            -(1 / (p : ℂ)) * ∑ j ∈ Finset.Ico 1 p, ψ x * (χ₀ ^ (j * (Fintype.card Fˣ / p))) x * (indE s x : ℂ) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => by ring
        linear_combination hdist
    simp_rw [hrew]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
    -- Every term in the second sum has ψ * χ_j ≠ 1 and order coprime to ∏ r ∈ s, r!
    have hsecond : ∀ j ∈ Finset.Ico 1 p,
        ∑ x : F, (ψ * χ₀ ^ (j * (Fintype.card Fˣ / p))) x * (indE s x : ℂ) = 0 := by
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
      have hjp : j < p := (Finset.mem_Ico.mp hj).2
      let η : MulChar F ℂ := χ₀ ^ (j * (Fintype.card Fˣ / p))
      have hη_ord : orderOf η = p := orderOf_char_prime hord hp_spec.1 hp_spec.2 hj1 hjp
      have hcop_ηs : (orderOf η).Coprime (∏ r ∈ s, r) := by
        rw [hη_ord]
        exact Nat.Coprime.prod_right fun r hr =>
          (hp_spec.1.coprime_iff_not_dvd).mpr fun hdvd =>
            hp ((Nat.prime_dvd_prime_iff_eq hp_spec.1 (hs_spec r hr).1).mp hdvd ▸ hr)
      have hcop_mul : (orderOf (ψ * η)).Coprime (∏ r ∈ s, r) := by
        have hdvd : orderOf (ψ * η) ∣ orderOf ψ * orderOf η :=
          Commute.orderOf_mul_dvd_mul_orderOf (Commute.all ψ η)
        exact (hcop_s.mul_left hcop_ηs).coprime_dvd_left hdvd
      have hne1 : ψ * η ≠ 1 := by
        intro h1
        have hinv : η = ψ⁻¹ := eq_inv_of_mul_eq_one_right h1
        have hord_eq : orderOf η = orderOf ψ := by rw [hinv, orderOf_inv]
        rw [hη_ord] at hord_eq
        rw [← hord_eq] at hcop_p
        have h1 := hcop_p.gcd_eq_one; rw [Nat.gcd_self] at h1; exact absurd h1 hp_spec.1.ne_one
      rw [ih hs_spec (ψ * η) hcop_mul, if_neg hne1]
    rw [Finset.sum_eq_zero hsecond, mul_zero, sub_zero, ih hs_spec ψ hcop_s]
    split_ifs with hψ
    · simp only [theta, Finset.prod_insert hp, Complex.ofReal_mul, Complex.ofReal_sub,
        Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_natCast]
      ring
    · simp

/-- Exact twisted Jacobi-sum bound on `indE` by Finset induction on `E`! -/
lemma norm_sum_mul_indE_le (a₀ : F) (ha₀ : a₀ ≠ 0) {χ₀ : MulChar F ℂ}
    (hord : ∀ k : ℕ, χ₀ ^ k = 1 ↔ Fintype.card Fˣ ∣ k)
    {χ : MulChar F ℂ} (hχ : χ ≠ 1)
    (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime ∧ p ∣ Fintype.card Fˣ) :
    ∀ ψ : MulChar F ℂ, (orderOf ψ).Coprime (∏ p ∈ E, p) →
      ‖∑ u : Fˣ, ψ (a₀ + u) * (indE E (a₀ + u) : ℂ) * χ u‖ ≤
        theta E * (if ψ = 1 then ((2 : ℝ) ^ E.card - 1) * Real.sqrt (Fintype.card F) + 1
          else (2 : ℝ) ^ E.card * Real.sqrt (Fintype.card F)) := by
  induction E using Finset.induction_on with
  | empty =>
    intro ψ _
    have hrew : ∀ u : Fˣ, ψ (a₀ + u) * (indE ∅ (a₀ + u) : ℂ) * χ u = ψ (a₀ + u) * χ u := by
      intro u
      by_cases h0 : a₀ + (u : F) = 0
      · simp [indE_empty, h0, MulChar.map_zero]
      · simp [indE_empty, h0]
    simp_rw [hrew, norm_twisted_sum_eq_jacobi a₀ ha₀ ψ χ]
    simp only [theta, Finset.prod_empty, Finset.card_empty, pow_zero, one_mul]
    split_ifs with hψ
    · subst hψ; rw [norm_jacobiSum_one_nontrivial hχ]; ring_nf; linarith
    · exact norm_jacobiSum_le_sqrt hψ hχ
  | @insert p s hp ih =>
    intro ψ hcop
    have hp_spec := hE p (Finset.mem_insert_self p s)
    have hs_spec : ∀ r ∈ s, r.Prime ∧ r ∣ Fintype.card Fˣ :=
      fun r hr => hE r (Finset.mem_insert_of_mem hr)
    rw [Finset.prod_insert hp] at hcop
    have hcop_p : (orderOf ψ).Coprime p := (Nat.coprime_mul_iff_right.mp hcop).1
    have hcop_s : (orderOf ψ).Coprime (∏ r ∈ s, r) := (Nat.coprime_mul_iff_right.mp hcop).2
    have hrew : ∀ u : Fˣ, ψ (a₀ + u) * (indE (insert p s) (a₀ + u) : ℂ) * χ u =
        (1 - 1 / (p : ℂ)) * (ψ (a₀ + u) * (indE s (a₀ + u) : ℂ) * χ u) -
        (1 / (p : ℂ)) * ∑ j ∈ Finset.Ico 1 p,
          ((ψ * χ₀ ^ (j * (Fintype.card Fˣ / p))) (a₀ + u) * (indE s (a₀ + u) : ℂ) * χ u) := by
      intro u
      rw [indE_insert hp, Complex.ofReal_mul, indP_eq_char_sum hord hp_spec.1 hp_spec.2]
      by_cases hx : a₀ + (u : F) = 0
      · simp [hx, indE]
      · have h1x : (1 : MulChar F ℂ) (a₀ + u) = 1 := MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
        simp only [h1x, mul_one, MulChar.mul_apply]
        have hdist : ψ (a₀ + u) * (-(1 / (p : ℂ)) * (∑ j ∈ Finset.Ico 1 p, (χ₀ ^ (j * (Fintype.card Fˣ / p))) (a₀ + u)) * (indE s (a₀ + u) : ℂ)) * χ u =
            -(1 / (p : ℂ)) * ∑ j ∈ Finset.Ico 1 p, ψ (a₀ + u) * (χ₀ ^ (j * (Fintype.card Fˣ / p))) (a₀ + u) * (indE s (a₀ + u) : ℂ) * χ u := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => by ring
        linear_combination hdist
    simp_rw [hrew]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp_spec.1.pos
    have hp_ge2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_spec.1.two_le
    have h1sub_nn : 0 ≤ 1 - 1 / (p : ℝ) := by rw [sub_nonneg, div_le_one hp_pos]; linarith
    have hnorm1 : ‖(1 : ℂ) - 1 / (p : ℂ)‖ = 1 - 1 / (p : ℝ) := by
      have : ((1 - 1 / (p : ℝ) : ℝ) : ℂ) = 1 - 1 / (p : ℂ) := by push_cast; rfl
      rw [← this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1sub_nn]
    have hnorm_inv : ‖(1 : ℂ) / (p : ℂ)‖ = 1 / (p : ℝ) := by
      have : ((1 / (p : ℝ) : ℝ) : ℂ) = 1 / (p : ℂ) := by push_cast; rfl
      rw [← this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hsec : ‖∑ j ∈ Finset.Ico 1 p,
        ∑ u : Fˣ, (ψ * χ₀ ^ (j * (Fintype.card Fˣ / p))) (a₀ + u) * (indE s (a₀ + u) : ℂ) * χ u‖ ≤
        ((p : ℝ) - 1) * (theta s * ((2 : ℝ) ^ s.card * Real.sqrt (Fintype.card F))) := by
      calc ‖∑ j ∈ Finset.Ico 1 p, _‖
          ≤ ∑ j ∈ Finset.Ico 1 p,
              ‖∑ u : Fˣ, (ψ * χ₀ ^ (j * (Fintype.card Fˣ / p))) (a₀ + u) * (indE s (a₀ + u) : ℂ) * χ u‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _j ∈ Finset.Ico 1 p, (theta s * ((2 : ℝ) ^ s.card * Real.sqrt (Fintype.card F))) := by
            apply Finset.sum_le_sum
            intro j hj
            have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
            have hjp : j < p := (Finset.mem_Ico.mp hj).2
            let η : MulChar F ℂ := χ₀ ^ (j * (Fintype.card Fˣ / p))
            have hη_ord : orderOf η = p := orderOf_char_prime hord hp_spec.1 hp_spec.2 hj1 hjp
            have hcop_ηs : (orderOf η).Coprime (∏ r ∈ s, r) := by
              rw [hη_ord]
              exact Nat.Coprime.prod_right fun r hr =>
                (hp_spec.1.coprime_iff_not_dvd).mpr fun hdvd =>
                  hp ((Nat.prime_dvd_prime_iff_eq hp_spec.1 (hs_spec r hr).1).mp hdvd ▸ hr)
            have hcop_mul : (orderOf (ψ * η)).Coprime (∏ r ∈ s, r) := by
              have hdvd : orderOf (ψ * η) ∣ orderOf ψ * orderOf η :=
                Commute.orderOf_mul_dvd_mul_orderOf (Commute.all ψ η)
              exact (hcop_s.mul_left hcop_ηs).coprime_dvd_left hdvd
            have hne1 : ψ * η ≠ 1 := by
              intro h1
              have hinv : η = ψ⁻¹ := eq_inv_of_mul_eq_one_right h1
              have hord_eq : orderOf η = orderOf ψ := by rw [hinv, orderOf_inv]
              rw [hη_ord] at hord_eq
              rw [← hord_eq] at hcop_p
              have h1 := hcop_p.gcd_eq_one; rw [Nat.gcd_self] at h1; exact absurd h1 hp_spec.1.ne_one
            simpa [hne1] using ih hs_spec (ψ * η) hcop_mul
        _ = ((p : ℝ) - 1) * (theta s * ((2 : ℝ) ^ s.card * Real.sqrt (Fintype.card F))) := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hp_spec.1.one_le, Nat.cast_one]
    have hfirst := ih hs_spec ψ hcop_s
    have htri := norm_sub_le
      ((1 - 1 / (p : ℂ)) * ∑ u : Fˣ, ψ (a₀ + u) * (indE s (a₀ + u) : ℂ) * χ u)
      ((1 / (p : ℂ)) * ∑ j ∈ Finset.Ico 1 p,
        ∑ u : Fˣ, (ψ * χ₀ ^ (j * (Fintype.card Fˣ / p))) (a₀ + u) * (indE s (a₀ + u) : ℂ) * χ u)
    rw [norm_mul, norm_mul, hnorm1, hnorm_inv] at htri
    have hcomb : ‖(1 - 1 / (p : ℂ)) * ∑ u : Fˣ, ψ (a₀ + u) * (indE s (a₀ + u) : ℂ) * χ u -
        (1 / (p : ℂ)) * ∑ j ∈ Finset.Ico 1 p,
          ∑ u : Fˣ, (ψ * χ₀ ^ (j * (Fintype.card Fˣ / p))) (a₀ + u) * (indE s (a₀ + u) : ℂ) * χ u‖ ≤
        (1 - 1 / (p : ℝ)) * (theta s * (if ψ = 1 then ((2 : ℝ) ^ s.card - 1) * Real.sqrt (Fintype.card F) + 1
          else (2 : ℝ) ^ s.card * Real.sqrt (Fintype.card F))) +
        (1 / (p : ℝ)) * (((p : ℝ) - 1) * (theta s * ((2 : ℝ) ^ s.card * Real.sqrt (Fintype.card F)))) := by
      have hA := mul_le_mul_of_nonneg_left hfirst h1sub_nn
      have hB := mul_le_mul_of_nonneg_left hsec (by positivity : (0 : ℝ) ≤ 1 / p)
      linarith
    have hfrac : (1 / (p : ℝ)) * ((p : ℝ) - 1) = 1 - 1 / (p : ℝ) := by field_simp [hp_pos.ne']
    have hθ_ins : theta (insert p s) = (1 - 1 / (p : ℝ)) * theta s := by
      simp only [theta, Finset.prod_insert hp]
    rw [Finset.card_insert_of_notMem hp, pow_succ, hθ_ins]
    refine hcomb.trans (le_of_eq ?_)
    split_ifs <;> · rw [← mul_assoc (1 / (p : ℝ)), hfrac]; ring

/-- Cohen–Trudgian lower-sieve function `g₀(x) = ∑_{p ∈ S} indE (insert p E) x - (|S| - 1) * indE E x`
(for `S = primeFactors n \ E`). -/
noncomputable def ctSieve (E S : Finset ℕ) (x : F) : ℝ :=
  if S = ∅ then indE E x
  else (∑ p ∈ S, indE (insert p E) x) - ((S.card : ℝ) - 1) * indE E x

lemma ctSieve_le_indPrim {E S : Finset ℕ}
    (hES : E ∪ S = (Fintype.card Fˣ).primeFactors) (x : F) :
    ctSieve E S x ≤ indE (Fintype.card Fˣ).primeFactors x := by
  unfold ctSieve
  split_ifs with hS
  · subst hS; rw [Finset.union_empty] at hES; rw [hES]
  · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    by_cases hxE : indE E x = 0
    · -- If indE E x = 0, then every indE (insert p E) x = 0 too!
      have h0 : ∀ p ∈ S, indE (insert p E) x = 0 := by
        intro p _
        have hle := indE_mono (Finset.subset_insert p E) x
        rcases indE_zero_or_one (insert p E) x with h | h <;> linarith
      rw [Finset.sum_eq_zero h0, hxE, mul_zero, sub_zero]
      rcases indE_zero_or_one (Fintype.card Fˣ).primeFactors x with h | h <;> linarith
    · have hxE1 : indE E x = 1 := (indE_zero_or_one E x).resolve_left hxE
      by_cases hxP : indE (Fintype.card Fˣ).primeFactors x = 1
      · rw [hxP, hxE1, mul_one]
        have hle1 : ∑ p ∈ S, indE (insert p E) x ≤ S.card := by
          calc ∑ p ∈ S, indE (insert p E) x ≤ ∑ _p ∈ S, (1 : ℝ) := by
                apply Finset.sum_le_sum; intro p _
                rcases indE_zero_or_one (insert p E) x with h | h <;> linarith
            _ = S.card := by simp
        linarith
      · have hxP0 : indE (Fintype.card Fˣ).primeFactors x = 0 :=
          (indE_zero_or_one _ x).resolve_right hxP
        -- Since indE (E ∪ S) x = 0 while indE E x = 1, some p₀ ∈ S has indP p₀ x = 0, so indE (insert p₀ E) x = 0!
        have hex0 : ∃ p₀ ∈ S, indE (insert p₀ E) x = 0 := by
          by_contra hall
          push Not at hall
          have hall1 : ∀ p ∈ S, indP p x = 1 := by
            intro p hp
            have h1 : indE (insert p E) x = 1 := (indE_zero_or_one _ x).resolve_left (hall p hp)
            by_cases hx0 : x = 0
            · simp [indE, hx0] at hxE1
            · by_cases hpE : p ∈ E
              · rw [Finset.insert_eq_of_mem hpE] at h1
                have hprod1 : ∏ r ∈ E, indP r x = 1 := by simpa [indE, hx0] using hxE1
                by_contra hne
                have h0 : indP p x = 0 := by
                  unfold indP at hne ⊢; split_ifs at hne ⊢ <;> tauto
                exact absurd (Finset.prod_eq_zero hpE h0) (by rw [hprod1]; norm_num)
              · rw [indE_insert hpE, hxE1, mul_one] at h1; exact h1
          have hx0 : x ≠ 0 := by intro h; simp [indE, h] at hxE1
          have hE1 : ∀ p ∈ E, indP p x = 1 := by
            intro p hp
            by_contra hne
            have h0 : indP p x = 0 := by unfold indP at hne ⊢; split_ifs at hne ⊢ <;> tauto
            have hprod0 : ∏ r ∈ E, indP r x = 0 := Finset.prod_eq_zero hp h0
            simp [indE, hx0, hprod0] at hxE1
          have hfull : indE (Fintype.card Fˣ).primeFactors x = 1 := by
            rw [← hES]; simp only [indE, hx0, ↓reduceIte]
            apply Finset.prod_eq_one
            intro p hp
            rcases Finset.mem_union.mp hp with h | h
            · exact hE1 p h
            · exact hall1 p h
          exact hxP hfull
        obtain ⟨p₀, hp₀S, hp₀0⟩ := hex0
        have hsum_le : ∑ p ∈ S, indE (insert p E) x ≤ (S.card : ℝ) - 1 := by
          rw [← Finset.add_sum_erase _ _ hp₀S, hp₀0, zero_add]
          calc ∑ p ∈ S.erase p₀, indE (insert p E) x ≤ ∑ _p ∈ S.erase p₀, (1 : ℝ) := by
                apply Finset.sum_le_sum; intro p _
                rcases indE_zero_or_one (insert p E) x with h | h <;> linarith
            _ = (S.erase p₀).card := by simp
            _ = (S.card : ℝ) - 1 := by
                rw [Finset.card_erase_of_mem hp₀S, Nat.cast_sub (Finset.card_pos.mpr hSne), Nat.cast_one]
        rw [hxP0, hxE1, mul_one]; linarith

/-- Principal sum and nontrivial Fourier bound for `ctSieve E S (a₀ + u)`. -/
lemma ctSieve_fourier_bounds (a₀ : F) (ha₀ : a₀ ≠ 0)
    (hnprim : ¬ IsPrimitiveRoot a₀ (Fintype.card Fˣ))
    {χ₀ : MulChar F ℂ} (hord : ∀ k : ℕ, χ₀ ^ k = 1 ↔ Fintype.card Fˣ ∣ k)
    {E S : Finset ℕ} (hdisj : Disjoint E S)
    (hES : E ∪ S = (Fintype.card Fˣ).primeFactors)
    (hΔ : 0 < 1 - ∑ p ∈ S, (1 : ℝ) / p) :
    let Δ : ℝ := 1 - ∑ p ∈ S, (1 : ℝ) / p
    let δ : ℝ := theta E * Δ
    let K : ℝ := if S = ∅ then (2 : ℝ) ^ E.card - 1
      else (2 : ℝ) ^ E.card * (((S.card : ℝ) - 1) / Δ + 2) - 1
    δ * (Fintype.card Fˣ : ℝ) ≤ ∑ u : Fˣ, ctSieve E S (a₀ + u) ∧
    ∀ χ : MulChar F ℂ, χ ≠ 1 →
      ‖∑ u : Fˣ, (ctSieve E S (a₀ + u) : ℂ) * χ u‖ ≤
        δ * (K * Real.sqrt (Fintype.card F) + 1) := by
  intro Δ δ K
  have hE_spec : ∀ p ∈ E, p.Prime ∧ p ∣ Fintype.card Fˣ := fun p hp => by
    have hmem : p ∈ (Fintype.card Fˣ).primeFactors := hES ▸ Finset.mem_union_left S hp
    exact ⟨Nat.prime_of_mem_primeFactors hmem, Nat.dvd_of_mem_primeFactors hmem⟩
  have hS_spec : ∀ p ∈ S, p.Prime ∧ p ∣ Fintype.card Fˣ := fun p hp => by
    have hmem : p ∈ (Fintype.card Fˣ).primeFactors := hES ▸ Finset.mem_union_right E hp
    exact ⟨Nat.prime_of_mem_primeFactors hmem, Nat.dvd_of_mem_primeFactors hmem⟩
  have hθ_pos : 0 < theta E := theta_pos fun p hp => (hE_spec p hp).1
  have hct_a0 : ctSieve E S a₀ ≤ 0 := by
    have hle := ctSieve_le_indPrim hES a₀
    rw [indE_primeFactors_eq_prim, if_neg hnprim] at hle
    exact hle
  -- Principal sum: ∑ u : Fˣ, ctSieve E S (a₀ + u) = (∑ x : F, ctSieve E S x) - ctSieve E S a₀
  have hsum_shift : ∀ f : F → ℝ, ∑ u : Fˣ, f (a₀ + u) = (∑ x : F, f x) - f a₀ := by
    intro f
    have h1 : ∑ x : F, f x = f a₀ + ∑ x ∈ Finset.univ.erase a₀, f x := by
      rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ a₀)]
    have h2 : ∑ u : Fˣ, f (a₀ + u) = ∑ x ∈ Finset.univ.erase a₀, f x := by
      refine Finset.sum_bij (fun (u : Fˣ) _ => a₀ + u)
        (fun u _ => Finset.mem_erase.mpr ⟨by simp [u.ne_zero], Finset.mem_univ _⟩)
        (fun u₁ _ u₂ _ h => Units.ext (add_left_cancel h))
        (fun x hx => ⟨Units.mk0 (x - a₀) (sub_ne_zero.mpr (Finset.mem_erase.mp hx).1),
          Finset.mem_univ _, by simp⟩)
        (fun _ _ => rfl)
    linarith
  -- Compute ∑ x : F, indE T x = theta T * n (in ℝ)
  have hsum_indE : ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime ∧ p ∣ Fintype.card Fˣ) →
      ∑ x : F, indE T x = theta T * Fintype.card Fˣ := by
    intro T hT
    have hC := sum_mul_indE hord T hT 1 (by simp)
    rw [if_pos rfl] at hC
    have hrew : ∑ x : F, (1 : MulChar F ℂ) x * (indE T x : ℂ) = ∑ x : F, (indE T x : ℂ) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x = 0
      · simp [indE, hx]
      · simp [MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]
    rw [hrew] at hC
    have hre := congrArg Complex.re hC
    simpa using hre
  -- Prove both parts!
  constructor
  · rw [hsum_shift]
    have htot : ∑ x : F, ctSieve E S x = δ * Fintype.card Fˣ := by
      unfold ctSieve
      split_ifs with hS
      · subst hS
        simp only [δ, Δ, Finset.sum_empty, sub_zero, mul_one]
        exact hsum_indE E hE_spec
      · rw [Finset.sum_sub_distrib, Finset.sum_comm, ← Finset.mul_sum, hsum_indE E hE_spec]
        have hSsum : ∑ p ∈ S, ∑ x : F, indE (insert p E) x =
            (∑ p ∈ S, (1 - 1 / (p : ℝ))) * (theta E * Fintype.card Fˣ) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun p hp => ?_
          have hpE : p ∉ E := Finset.disjoint_right.mp hdisj hp
          rw [hsum_indE (insert p E) (fun r hr => by
            rcases Finset.mem_insert.mp hr with rfl | hrE
            · exact hS_spec r hp
            · exact hE_spec r hrE)]
          dsimp only [theta]; rw [Finset.prod_insert hpE]; ring
        rw [hSsum]
        have hΔeq : ∑ p ∈ S, (1 - 1 / (p : ℝ)) - ((S.card : ℝ) - 1) = Δ := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]; ring
        dsimp [δ]
        linear_combination (theta E * Fintype.card Fˣ) * hΔeq
    linarith
  · intro χ hχ
    by_cases hS : S = ∅
    · subst hS
      have hrew : ∀ u : Fˣ, (ctSieve E ∅ (a₀ + u) : ℂ) * χ u =
          (1 : MulChar F ℂ) (a₀ + u) * (indE E (a₀ + u) : ℂ) * χ u := by
        intro u
        by_cases hx : a₀ + (u : F) = 0
        · simp [ctSieve, indE, hx]
        · simp [ctSieve, MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]
      simp_rw [hrew]
      have hb := norm_sum_mul_indE_le a₀ ha₀ hord hχ E hE_spec 1 (by simp)
      simpa [δ, Δ, K] using hb
    · -- S nonempty: expand ctSieve E S (a₀ + u) = Δ * indE E (a₀ + u) - ∑ p ∈ S, (1/p) * ∑ j ∈ Ico 1 p, η_{p,j}(a₀ + u) * indE E (a₀ + u)!
      have hrew : ∀ u : Fˣ, (ctSieve E S (a₀ + u) : ℂ) * χ u =
          (Δ : ℂ) * ((1 : MulChar F ℂ) (a₀ + u) * (indE E (a₀ + u) : ℂ) * χ u) -
          ∑ p ∈ S, (1 / (p : ℂ)) * ∑ j ∈ Finset.Ico 1 p,
            ((χ₀ ^ (j * (Fintype.card Fˣ / p))) (a₀ + u) * (indE E (a₀ + u) : ℂ) * χ u) := by
        intro u
        simp only [ctSieve, hS, ↓reduceIte, Complex.ofReal_sub, Complex.ofReal_sum,
          Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_one]
        by_cases hx : a₀ + (u : F) = 0
        · simp [indE, hx]
        · have h1x : (1 : MulChar F ℂ) (a₀ + u) = 1 := MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
          have hterm : ∀ p ∈ S, (indE (insert p E) (a₀ + u) : ℂ) =
              (1 - 1 / (p : ℂ)) * (indE E (a₀ + u) : ℂ) -
              (1 / (p : ℂ)) * ∑ j ∈ Finset.Ico 1 p,
                ((χ₀ ^ (j * (Fintype.card Fˣ / p))) (a₀ + u) * (indE E (a₀ + u) : ℂ)) := by
            intro p hp
            have hpE : p ∉ E := Finset.disjoint_right.mp hdisj hp
            rw [indE_insert hpE, Complex.ofReal_mul,
              indP_eq_char_sum hord (hS_spec p hp).1 (hS_spec p hp).2, h1x, mul_one,
              sub_mul, mul_assoc, ← Finset.sum_mul]
          rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_mul]
          have hΔC : (∑ p ∈ S, ((1 : ℂ) - 1 / (p : ℂ))) - ((S.card : ℂ) - 1) = (Δ : ℂ) := by
            rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
            simp only [Δ, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_sum,
              Complex.ofReal_div, Complex.ofReal_natCast]
            ring
          have hsec_eq : (∑ p ∈ S, (1 / (p : ℂ)) * ∑ j ∈ Finset.Ico 1 p,
              (χ₀ ^ (j * (Fintype.card Fˣ / p))) (a₀ + u) * (indE E (a₀ + u) : ℂ)) * χ u =
              ∑ p ∈ S, (1 / (p : ℂ)) * ∑ j ∈ Finset.Ico 1 p,
                (χ₀ ^ (j * (Fintype.card Fˣ / p))) (a₀ + u) * (indE E (a₀ + u) : ℂ) * χ u := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [mul_assoc, Finset.sum_mul]
          rw [sub_mul, sub_mul, hsec_eq, h1x, one_mul]
          have hmain_eq : (∑ p ∈ S, ((1 : ℂ) - 1 / (p : ℂ))) * (indE E (a₀ + u) : ℂ) * χ u -
              ((S.card : ℂ) - 1) * (indE E (a₀ + u) : ℂ) * χ u =
              (Δ : ℂ) * ((indE E (a₀ + u) : ℂ) * χ u) := by
            rw [← hΔC]; ring
          linear_combination hmain_eq
      simp_rw [hrew]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm]
      have htri := norm_sub_le
        ((Δ : ℂ) * ∑ u : Fˣ, (1 : MulChar F ℂ) (a₀ + u) * (indE E (a₀ + u) : ℂ) * χ u)
        (∑ p ∈ S, ∑ u : Fˣ, (1 / (p : ℂ)) * ∑ j ∈ Finset.Ico 1 p,
          (χ₀ ^ (j * (Fintype.card Fˣ / p))) (a₀ + u) * (indE E (a₀ + u) : ℂ) * χ u)
      have h1 : ‖(Δ : ℂ) * ∑ u : Fˣ, (1 : MulChar F ℂ) (a₀ + u) * (indE E (a₀ + u) : ℂ) * χ u‖ ≤
          Δ * (theta E * (((2 : ℝ) ^ E.card - 1) * Real.sqrt (Fintype.card F) + 1)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΔ]
        exact mul_le_mul_of_nonneg_left
          (by simpa using norm_sum_mul_indE_le a₀ ha₀ hord hχ E hE_spec 1 (by simp)) hΔ.le
      have h2 : ‖∑ p ∈ S, ∑ u : Fˣ, (1 / (p : ℂ)) * ∑ j ∈ Finset.Ico 1 p,
            (χ₀ ^ (j * (Fintype.card Fˣ / p))) (a₀ + u) * (indE E (a₀ + u) : ℂ) * χ u‖ ≤
          (∑ p ∈ S, (1 - 1 / (p : ℝ))) * (theta E * ((2 : ℝ) ^ E.card * Real.sqrt (Fintype.card F))) := by
        rw [Finset.sum_mul]
        calc ‖∑ p ∈ S, _‖ ≤ ∑ p ∈ S, ‖∑ u : Fˣ, (1 / (p : ℂ)) * ∑ j ∈ Finset.Ico 1 p,
              (χ₀ ^ (j * (Fintype.card Fˣ / p))) (a₀ + u) * (indE E (a₀ + u) : ℂ) * χ u‖ := norm_sum_le _ _
          _ ≤ ∑ p ∈ S, (1 - 1 / (p : ℝ)) * (theta E * ((2 : ℝ) ^ E.card * Real.sqrt (Fintype.card F))) := by
              apply Finset.sum_le_sum
              intro p hp
              have hp_spec := hS_spec p hp
              have hpE : p ∉ E := Finset.disjoint_right.mp hdisj hp
              have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp_spec.1.pos
              rw [← Finset.mul_sum, Finset.sum_comm, norm_mul]
              have hinv : ‖(1 : ℂ) / (p : ℂ)‖ = 1 / (p : ℝ) := by
                have : ((1 / (p : ℝ) : ℝ) : ℂ) = 1 / (p : ℂ) := by push_cast; rfl
                rw [← this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
              rw [hinv]
              have hjsum : ‖∑ j ∈ Finset.Ico 1 p,
                  ∑ u : Fˣ, (χ₀ ^ (j * (Fintype.card Fˣ / p))) (a₀ + u) * (indE E (a₀ + u) : ℂ) * χ u‖ ≤
                  ((p : ℝ) - 1) * (theta E * ((2 : ℝ) ^ E.card * Real.sqrt (Fintype.card F))) := by
                calc ‖∑ j ∈ Finset.Ico 1 p, _‖
                    ≤ ∑ j ∈ Finset.Ico 1 p, ‖∑ u : Fˣ,
                        (χ₀ ^ (j * (Fintype.card Fˣ / p))) (a₀ + u) * (indE E (a₀ + u) : ℂ) * χ u‖ :=
                      norm_sum_le _ _
                  _ ≤ ∑ _j ∈ Finset.Ico 1 p, (theta E * ((2 : ℝ) ^ E.card * Real.sqrt (Fintype.card F))) := by
                      apply Finset.sum_le_sum
                      intro j hj
                      let η : MulChar F ℂ := χ₀ ^ (j * (Fintype.card Fˣ / p))
                      have hη_ord : orderOf η = p :=
                        orderOf_char_prime hord hp_spec.1 hp_spec.2 (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
                      have hcop : (orderOf η).Coprime (∏ r ∈ E, r) := by
                        rw [hη_ord]
                        exact Nat.Coprime.prod_right fun r hr =>
                          (hp_spec.1.coprime_iff_not_dvd).mpr fun hdvd =>
                            hpE ((Nat.prime_dvd_prime_iff_eq hp_spec.1 (hE_spec r hr).1).mp hdvd ▸ hr)
                      have hne1 : η ≠ 1 := by
                        intro h1; rw [h1, orderOf_one] at hη_ord; exact hp_spec.1.ne_one hη_ord.symm
                      simpa [hne1] using norm_sum_mul_indE_le a₀ ha₀ hord hχ E hE_spec η hcop
                  _ = ((p : ℝ) - 1) * (theta E * ((2 : ℝ) ^ E.card * Real.sqrt (Fintype.card F))) := by
                      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
                        Nat.cast_sub hp_spec.1.one_le, Nat.cast_one]
              have hmul := mul_le_mul_of_nonneg_left hjsum (by positivity : (0 : ℝ) ≤ 1 / (p : ℝ))
              have hfrac : (1 / (p : ℝ)) * ((p : ℝ) - 1) = 1 - 1 / (p : ℝ) := by field_simp [hp_pos.ne']
              calc (1 / (p : ℝ)) * ‖∑ j ∈ Finset.Ico 1 p, _‖
                  ≤ (1 / (p : ℝ)) * (((p : ℝ) - 1) * (theta E * ((2 : ℝ) ^ E.card * Real.sqrt (Fintype.card F)))) := hmul
                _ = (1 - 1 / (p : ℝ)) * (theta E * ((2 : ℝ) ^ E.card * Real.sqrt (Fintype.card F))) := by
                    rw [← mul_assoc, hfrac]
      have hS_sum_eq : ∑ p ∈ S, (1 - 1 / (p : ℝ)) = ((S.card : ℝ) - 1) + Δ := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]; dsimp [Δ]; ring
      have htot : ‖(Δ : ℂ) * ∑ u : Fˣ, (1 : MulChar F ℂ) (a₀ + u) * (indE E (a₀ + u) : ℂ) * χ u -
          ∑ p ∈ S, ∑ u : Fˣ, (1 / (p : ℂ)) * ∑ j ∈ Finset.Ico 1 p,
            (χ₀ ^ (j * (Fintype.card Fˣ / p))) (a₀ + u) * (indE E (a₀ + u) : ℂ) * χ u‖ ≤
          δ * (K * Real.sqrt (Fintype.card F) + 1) := by
        have hstep := htri.trans (add_le_add h1 h2)
        refine hstep.trans (le_of_eq ?_)
        rw [hS_sum_eq]
        have hΔne : Δ ≠ 0 := hΔ.ne'
        dsimp [δ, K]
        rw [if_neg hS]
        field_simp [hΔne]
        ring
      exact htot

/-- Exact degree lower bound: every `x ∈ Fˣ` has at least `φ(n) - 1` neighbors in `G(F, a₀)`. -/
lemma degree_ge_totient_sub_one (a₀ : F) (hnprim : ¬ IsPrimitiveRoot a₀ (Fintype.card Fˣ))
    (x : Fˣ) :
    Nat.totient (Fintype.card Fˣ) - 1 ≤
      (Finset.univ.filter fun y : Fˣ => x ≠ y ∧ IsPrimitiveRoot ((x : F) * (y : F) + a₀) (Fintype.card Fˣ)).card := by
  let n := Fintype.card Fˣ
  obtain ⟨χ₀, hord, _⟩ := exists_gen_mulChar (F := F)
  have hsum_all : ∑ z : F, indE n.primeFactors z = theta n.primeFactors * n := by
    have hC := sum_mul_indE hord n.primeFactors
      (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, Nat.dvd_of_mem_primeFactors hp⟩) 1 (by simp)
    rw [if_pos rfl] at hC
    have hrew : ∑ z : F, (1 : MulChar F ℂ) z * (indE n.primeFactors z : ℂ) =
        ∑ z : F, (indE n.primeFactors z : ℂ) := by
      refine Finset.sum_congr rfl fun z _ => ?_
      by_cases hz : z = 0
      · simp [indE, hz]
      · simp [MulChar.one_apply (isUnit_iff_ne_zero.mpr hz)]
    rw [hrew] at hC
    simpa using congrArg Complex.re hC
  have htot_eq : theta n.primeFactors * n = (Nat.totient n : ℝ) := by
    have hQ := congrArg ((↑) : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors n)
    push_cast at hQ
    rw [hQ, mul_comm]
    congr 1
    simp only [theta, one_div]
  -- Count all y : Fˣ such that (x : F) * y + a₀ is primitive!
  have hcard_prim : (Finset.univ.filter fun y : Fˣ => IsPrimitiveRoot ((x : F) * (y : F) + a₀) n).card =
      Nat.totient n := by
    have h1 : ((Finset.univ.filter fun y : Fˣ => IsPrimitiveRoot ((x : F) * (y : F) + a₀) n).card : ℝ) =
        ∑ y : Fˣ, indE n.primeFactors ((x : F) * (y : F) + a₀) := by
      dsimp only [n]; simp_rw [indE_primeFactors_eq_prim]; rw [Finset.sum_boole]
    have h2 : ∑ y : Fˣ, indE n.primeFactors ((x : F) * (y : F) + a₀) =
        (∑ z : F, indE n.primeFactors z) - indE n.primeFactors a₀ := by
      have hbij : ∑ y : Fˣ, indE n.primeFactors ((x : F) * (y : F) + a₀) =
          ∑ z ∈ Finset.univ.erase a₀, indE n.primeFactors z := by
        refine Finset.sum_bij (fun (y : Fˣ) _ => (x : F) * (y : F) + a₀)
          (fun y _ => Finset.mem_erase.mpr ⟨by intro h; exact mul_ne_zero x.ne_zero y.ne_zero (by linear_combination h), Finset.mem_univ _⟩)
          (fun y₁ _ y₂ _ h => Units.ext (mul_left_cancel₀ x.ne_zero (add_right_cancel h)))
          (fun z hz => ⟨x⁻¹ * Units.mk0 (z - a₀) (sub_ne_zero.mpr (Finset.mem_erase.mp hz).1),
            Finset.mem_univ _, by simp [x.ne_zero]⟩)
          (fun _ _ => rfl)
      rw [hbij]
      have := Finset.sum_erase_add (s := Finset.univ) (f := indE n.primeFactors) (Finset.mem_univ a₀)
      linarith
    have ha0 : indE n.primeFactors a₀ = 0 := by rw [indE_primeFactors_eq_prim, if_neg hnprim]
    have heqR : ((Finset.univ.filter fun y : Fˣ => IsPrimitiveRoot ((x : F) * (y : F) + a₀) n).card : ℝ) =
        (Nat.totient n : ℝ) := by
      rw [h1, h2, ha0, sub_zero, hsum_all, htot_eq]
    exact_mod_cast heqR
  -- Subtracting at most the single element y = x leaves >= φ(n) - 1!
  have hsub : (Finset.univ.filter fun y : Fˣ => IsPrimitiveRoot ((x : F) * (y : F) + a₀) n) \ {x} ⊆
      Finset.univ.filter fun y : Fˣ => x ≠ y ∧ IsPrimitiveRoot ((x : F) * (y : F) + a₀) n := by
    intro y hy
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton] at hy ⊢
    exact ⟨Ne.symm hy.2, hy.1⟩
  have hle := Finset.card_le_card hsub
  have hsd : (Finset.univ.filter fun y : Fˣ => IsPrimitiveRoot ((x : F) * (y : F) + a₀) n).card - 1 ≤
      ((Finset.univ.filter fun y : Fˣ => IsPrimitiveRoot ((x : F) * (y : F) + a₀) n) \ {x}).card := by
    have := Finset.le_card_sdiff {x} (Finset.univ.filter fun y : Fˣ => IsPrimitiveRoot ((x : F) * (y : F) + a₀) n)
    simpa using this
  change Nat.totient n - 1 ≤ (Finset.univ.filter fun y : Fˣ => x ≠ y ∧ IsPrimitiveRoot ((x : F) * (y : F) + a₀) n).card
  omega

end PrimeSieves

section AnalyticCriterion

open Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Upper-sieve Fourier bounds for `indE E (a₀ + u)` (`E ⊆ n.primeFactors`). -/
lemma indE_fourier_bounds (a₀ : F) (ha₀ : a₀ ≠ 0)
    {χ₀ : MulChar F ℂ} (hord : ∀ k : ℕ, χ₀ ^ k = 1 ↔ Fintype.card Fˣ ∣ k)
    {E : Finset ℕ} (hE : E ⊆ (Fintype.card Fˣ).primeFactors) :
    ∑ u : Fˣ, indE E (a₀ + u) ≤ theta E * (Fintype.card Fˣ : ℝ) ∧
    ∀ χ : MulChar F ℂ, χ ≠ 1 →
      ‖∑ u : Fˣ, (indE E (a₀ + u) : ℂ) * χ u‖ ≤
        theta E * (((2 : ℝ) ^ E.card - 1) * Real.sqrt (Fintype.card F) + 1) := by
  have hE_spec : ∀ p ∈ E, p.Prime ∧ p ∣ Fintype.card Fˣ := fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors (hE hp), Nat.dvd_of_mem_primeFactors (hE hp)⟩
  constructor
  · have hC := sum_mul_indE hord E hE_spec 1 (by simp)
    rw [if_pos rfl] at hC
    have hrew : ∑ x : F, (1 : MulChar F ℂ) x * (indE E x : ℂ) = ∑ x : F, (indE E x : ℂ) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x = 0
      · simp [indE, hx]
      · simp [MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]
    rw [hrew] at hC
    have htot : ∑ x : F, indE E x = theta E * Fintype.card Fˣ := by
      simpa using congrArg Complex.re hC
    have hshift : ∑ u : Fˣ, indE E (a₀ + u) = (∑ x : F, indE E x) - indE E a₀ := by
      have h1 : ∑ x : F, indE E x = indE E a₀ + ∑ x ∈ Finset.univ.erase a₀, indE E x := by
        rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ a₀)]
      have h2 : ∑ u : Fˣ, indE E (a₀ + u) = ∑ x ∈ Finset.univ.erase a₀, indE E x := by
        refine Finset.sum_bij (fun (u : Fˣ) _ => a₀ + u)
          (fun u _ => Finset.mem_erase.mpr ⟨by simp [u.ne_zero], Finset.mem_univ _⟩)
          (fun u₁ _ u₂ _ h => Units.ext (add_left_cancel h))
          (fun x hx => ⟨Units.mk0 (x - a₀) (sub_ne_zero.mpr (Finset.mem_erase.mp hx).1),
            Finset.mem_univ _, by simp⟩)
          (fun _ _ => rfl)
      linarith
    have hnn : 0 ≤ indE E a₀ := by rcases indE_zero_or_one E a₀ with h | h <;> linarith
    linarith
  · intro χ hχ
    have hrew : ∀ u : Fˣ, (indE E (a₀ + u) : ℂ) * χ u =
        (1 : MulChar F ℂ) (a₀ + u) * (indE E (a₀ + u) : ℂ) * χ u := by
      intro u
      by_cases hx : a₀ + (u : F) = 0
      · simp [indE, hx]
      · simp [MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]
    simp_rw [hrew]
    simpa using norm_sum_mul_indE_le a₀ ha₀ hord hχ E hE_spec 1 (by simp)

/-- Master analytic Hamiltonicity criterion combining Chvátal–Erdős, exact degree `≥ φ(n) - 1`,
Cohen–Trudgian lower sieves, and `indE` upper sieves! -/
theorem exists_circ_perm_of_analytic
    (hCE_thm : ∀ (adj : Fˣ → Fˣ → Prop),
      (∀ ⦃x y⦄, adj x y → adj y x) → (∀ x, ¬ adj x x) → 3 ≤ Fintype.card Fˣ →
      (∀ (S A B I : Finset Fˣ),
        Disjoint S A → Disjoint S B → Disjoint A B →
        S ∪ A ∪ B = Finset.univ → A.Nonempty → B.Nonempty →
        (∀ x ∈ A, ∀ y ∈ B, ¬ adj x y) → (∀ x ∈ I, ∀ y ∈ I, ¬ adj x y) → I.card ≤ S.card) →
      ∃ a : Fin (Fintype.card Fˣ) ≃ Fˣ,
        ∀ i : Fin (Fintype.card Fˣ), adj (a i) (a ⟨(i.val + 1) % Fintype.card Fˣ,
          Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => Fin.elim0 (h ▸ i))⟩))
    (hF : 7 < Fintype.card F)
    (a₀ : F) (ha₀ : a₀ ≠ 0) (hnprim : ¬ IsPrimitiveRoot a₀ (Fintype.card F - 1))
    (hcontra :
      let q := Fintype.card F
      let n := q - 1
      ∀ (α k a b : ℕ),
        1 ≤ a → a ≤ b → a + b + k = n → k < α → α ≤ n →
        Nat.totient n ≤ a + k →
        -- Lower-sieve constraints (for any partition E ⊔ S = n.primeFactors with Δ > 0):
        (∀ (E Sp : Finset ℕ), Disjoint E Sp → E ∪ Sp = n.primeFactors →
          ∀ (_hΔ : 0 < 1 - ∑ p ∈ Sp, (1 : ℝ) / p),
            let Δ : ℝ := 1 - ∑ p ∈ Sp, (1 : ℝ) / p
            let δ : ℝ := theta E * Δ
            let K : ℝ := if Sp = ∅ then (2 : ℝ) ^ E.card - 1
              else (2 : ℝ) ^ E.card * (((Sp.card : ℝ) - 1) / Δ + 2) - 1
            let L : ℝ := K * Real.sqrt q + 1
            (α : ℝ) * (n + L) ≤ n * (L + 1 / δ) ∧
            (n : ℝ) ^ 2 * a * b ≤ L ^ 2 * (a + k) * (b + k)) →
        -- Upper-sieve constraints (for any E ⊆ n.primeFactors):
        (∀ (E : Finset ℕ), E ⊆ n.primeFactors →
          let Le : ℝ := ((2 : ℝ) ^ E.card - 1) * Real.sqrt q + 1
          ((Nat.totient n - 1 : ℕ) : ℝ) * n ≤ theta E * (n - α) * (n + Le) ∧
          (a : ℝ) * ((Nat.totient n - 1 : ℕ) : ℝ) * n ≤
            theta E * a * (a + k) * n +
              theta E * Le * Real.sqrt ((a : ℝ) * b * (a + k) * (b + k))) →
        False) :
    let m := Fintype.card F - 1
    ∃ a : Fin m ≃ Fˣ,
      ∀ i : Fin m, IsPrimitiveRoot
        ((a i : F) * (a ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩ : F) + a₀) m := by
  classical
  let q := Fintype.card F
  let m := q - 1
  have hcard_u : Fintype.card Fˣ = m := Fintype.card_units (α := F)
  have hm3 : 3 ≤ Fintype.card Fˣ := by omega
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnprim' : ¬ IsPrimitiveRoot a₀ (Fintype.card Fˣ) := hcard_u.symm ▸ hnprim
  let adj : Fˣ → Fˣ → Prop := fun x y => x ≠ y ∧ IsPrimitiveRoot ((x : F) * (y : F) + a₀) (Fintype.card Fˣ)
  have hsym : ∀ ⦃x y⦄, adj x y → adj y x := fun x y ⟨hne, hp⟩ => ⟨hne.symm, by rwa [mul_comm]⟩
  have hirr : ∀ x, ¬ adj x x := fun x h => h.1 rfl
  obtain ⟨χ₀, hord, horth⟩ := exists_gen_mulChar (F := F)
  have hCE : ∃ e : Fin (Fintype.card Fˣ) ≃ Fˣ,
      ∀ i : Fin (Fintype.card Fˣ),
        adj (e i) (e ⟨(i.val + 1) % Fintype.card Fˣ, Nat.mod_lt _ (by omega)⟩) := by
    apply hCE_thm adj hsym hirr hm3
    intro S A B I hSA hSB hAB hcov hAne hBne hnoAB hind
    by_contra hlt
    push Not at hlt
    -- WLOG assume A.card ≤ B.card (swap A, B if needed!)
    suffices hWLOG : ∀ (A' B' : Finset Fˣ),
        Disjoint S A' → Disjoint S B' → Disjoint A' B' →
        S ∪ A' ∪ B' = Finset.univ → A'.Nonempty → B'.Nonempty → A'.card ≤ B'.card →
        (∀ x ∈ A', ∀ y ∈ B', ¬ adj x y) → False by
      rcases le_total A.card B.card with hle | hle
      · exact hWLOG A B hSA hSB hAB hcov hAne hBne hle hnoAB
      · exact hWLOG B A hSB hSA hAB.symm
          (by ext z; have := Finset.ext_iff.mp hcov z; simp at this ⊢; tauto)
          hBne hAne hle (fun x hx y hy h => hnoAB y hy x hx (hsym h))
    intro A' B' hSA' hSB' hAB' hcov' hA'ne hB'ne hA'leB' hnoAB'
    have hsum_card : A'.card + B'.card + S.card = m := by
      have h1 : (S ∪ A' ∪ B').card = S.card + A'.card + B'.card := by
        rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hSB', hAB'⟩),
          Finset.card_union_of_disjoint hSA']
      rw [hcov', Finset.card_univ, hcard_u] at h1
      omega
    -- Minimum degree gives Nat.totient m ≤ A'.card + S.card!
    have htot_le : Nat.totient m ≤ A'.card + S.card := by
      obtain ⟨x₀, hx₀⟩ := hA'ne
      have hdeg := degree_ge_totient_sub_one a₀ hnprim' x₀
      have hsub : (Finset.univ.filter fun y : Fˣ => adj x₀ y) ⊆ (A'.erase x₀) ∪ S := by
        intro y hy
        have hadj := (Finset.mem_filter.mp hy).2
        have hy_ne : y ≠ x₀ := hadj.1.symm
        have hyU : y ∈ S ∪ A' ∪ B' := hcov'.symm ▸ Finset.mem_univ y
        simp only [Finset.mem_union] at hyU
        rcases hyU with (hyS | hyA) | hyB
        · exact Finset.mem_union_right _ hyS
        · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hy_ne, hyA⟩)
        · exact absurd hadj (hnoAB' x₀ hx₀ y hyB)
      have hle := Finset.card_le_card hsub
      have hdisj_er : Disjoint (A'.erase x₀) S :=
        Finset.disjoint_of_subset_left (Finset.erase_subset x₀ A') hSA'.symm
      rw [Finset.card_union_of_disjoint hdisj_er, Finset.card_erase_of_mem hx₀] at hle
      have hdeg' : Nat.totient m - 1 ≤ (Finset.univ.filter fun y : Fˣ => adj x₀ y).card := by
        simpa only [adj, hcard_u] using hdeg
      have hApos : 1 ≤ A'.card := Finset.card_pos.mpr ⟨x₀, hx₀⟩
      have htot_pos : 1 ≤ Nat.totient m := Nat.totient_pos.mpr (by omega)
      omega
    -- Apply hcontra!
    apply hcontra I.card S.card A'.card B'.card
      (Finset.card_pos.mpr hA'ne) hA'leB' hsum_card hlt
      (show I.card ≤ m from hcard_u ▸ Finset.card_le_univ I) htot_le
    · -- Lower-sieve constraints
      intro E Sp hdisj hES hΔ
      let Δ : ℝ := 1 - ∑ p ∈ Sp, (1 : ℝ) / p
      let δ : ℝ := theta E * Δ
      let K : ℝ := if Sp = ∅ then (2 : ℝ) ^ E.card - 1
        else (2 : ℝ) ^ E.card * (((Sp.card : ℝ) - 1) / Δ + 2) - 1
      let L : ℝ := K * Real.sqrt q + 1
      have hES' : E ∪ Sp = (Fintype.card Fˣ).primeFactors := hcard_u.symm ▸ hES
      have hE_prime : ∀ p ∈ E, p.Prime := fun p hp =>
        Nat.prime_of_mem_primeFactors (hES ▸ Finset.mem_union_left Sp hp)
      have hδ_pos : 0 < δ := mul_pos (theta_pos hE_prime) hΔ
      have hK_nn : 0 ≤ K := by
        dsimp [K]
        split_ifs with hSp
        · have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ E.card := one_le_pow₀ (by norm_num)
          linarith
        · have hSne : 1 ≤ Sp.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hSp)
          have hSpR : (1 : ℝ) ≤ Sp.card := by exact_mod_cast hSne
          have h1 : (0 : ℝ) ≤ ((Sp.card : ℝ) - 1) / Δ := div_nonneg (by linarith) hΔ.le
          have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ E.card := one_le_pow₀ (by norm_num)
          nlinarith only [h1, h2]
      have hL_nn : 0 ≤ L := by dsimp [L]; positivity
      have hfb := ctSieve_fourier_bounds a₀ ha₀ hnprim' hord hdisj hES' hΔ
      let f : Fˣ → ℝ := fun u => ctSieve E Sp (a₀ + u)
      have hhat : ∀ k : Fin (Fintype.card Fˣ), k.val ≠ 0 →
          ‖∑ u : Fˣ, (f u : ℂ) * (χ₀ ^ k.val) u‖ ≤ δ * L := by
        intro k hk
        have hχne : χ₀ ^ k.val ≠ 1 := by
          intro h1
          have hdvd := (hord k.val).mp h1
          exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hdvd) (not_le.mpr k.2)
        exact hfb.2 (χ₀ ^ k.val) hχne
      have hμ_ge : δ ≤ (∑ u : Fˣ, f u) / (Fintype.card Fˣ : ℝ) := by
        rw [le_div_iff₀ (Nat.cast_pos.mpr Fintype.card_pos)]
        exact hfb.1
      constructor
      · -- (1) Independent set bound on I × I!
        have hem := expander_mixing f I I hord horth (mul_nonneg hδ_pos.le hL_nn) hhat
        have hlow : (∑ u : Fˣ, f u) / (Fintype.card Fˣ : ℝ) * I.card * I.card -
            (δ * L) * Real.sqrt (I.card * (1 - I.card / (Fintype.card Fˣ : ℝ)) *
              (I.card * (1 - I.card / (Fintype.card Fˣ : ℝ)))) ≤
            ∑ x ∈ I, ∑ y ∈ I, f (x * y) := by
          linarith [(abs_le.mp hem).1]
        have hI_le_m : (I.card : ℝ) ≤ Fintype.card Fˣ := by
          exact_mod_cast Finset.card_le_univ I
        have h1sub_nn : 0 ≤ 1 - (I.card : ℝ) / (Fintype.card Fˣ : ℝ) := by
          rw [sub_nonneg, div_le_one (Nat.cast_pos.mpr Fintype.card_pos)]; exact hI_le_m
        have hsq_eq : Real.sqrt (I.card * (1 - I.card / (Fintype.card Fˣ : ℝ)) *
            (I.card * (1 - I.card / (Fintype.card Fˣ : ℝ)))) =
            I.card * (1 - I.card / (Fintype.card Fˣ : ℝ)) :=
          Real.sqrt_mul_self (mul_nonneg (Nat.cast_nonneg _) h1sub_nn)
        rw [hsq_eq] at hlow
        -- Upper bound: ∑_{x,y ∈ I} f(xy) ≤ I.card (off-diagonal is ≤ 0, diagonal is ≤ 1)!
        have hup : ∑ x ∈ I, ∑ y ∈ I, f (x * y) ≤ I.card := by
          have hterm : ∀ x ∈ I, ∑ y ∈ I, f (x * y) ≤ 1 := by
            intro x hx
            rw [← Finset.add_sum_erase _ _ hx]
            have hdiag : f (x * x) ≤ 1 := by
              have h1 := ctSieve_le_indPrim hES' (a₀ + (x * x : Fˣ))
              rcases indE_zero_or_one (Fintype.card Fˣ).primeFactors (a₀ + (x * x : Fˣ)) with h | h <;> linarith
            have hoff : ∑ y ∈ I.erase x, f (x * y) ≤ 0 := by
              apply Finset.sum_nonpos
              intro y hy
              have hyne : x ≠ y := (Finset.mem_erase.mp hy).1.symm
              have hyI : y ∈ I := (Finset.mem_erase.mp hy).2
              have hnp : ¬ IsPrimitiveRoot ((x : F) * (y : F) + a₀) (Fintype.card Fˣ) :=
                fun hp => hind x hx y hyI ⟨hyne, hp⟩
              have hle := ctSieve_le_indPrim hES' (a₀ + (x * y : Fˣ))
              rw [indE_primeFactors_eq_prim, add_comm a₀, Units.val_mul, if_neg hnp] at hle
              simpa [f, Units.val_mul, add_comm] using hle
            linarith
          calc ∑ x ∈ I, ∑ y ∈ I, f (x * y) ≤ ∑ _x ∈ I, (1 : ℝ) := Finset.sum_le_sum hterm
            _ = I.card := by simp
        have hI_pos : (0 : ℝ) < I.card := by exact_mod_cast (show 0 < I.card by omega)
        have hcomb : δ * I.card * I.card - δ * L * (I.card * (1 - I.card / (m : ℝ))) ≤ I.card := by
          have hμ' : δ * I.card * I.card ≤ (∑ u : Fˣ, f u) / (Fintype.card Fˣ : ℝ) * I.card * I.card :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμ_ge (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
          rw [hcard_u] at hlow hμ'
          linarith
        -- Divide by δ * I.card > 0 and multiply by m > 0!
        have hstep : δ * I.card * ((I.card : ℝ) * (m + L)) ≤ δ * I.card * (m * (L + 1 / δ)) := by
          have hmne : (m : ℝ) ≠ 0 := hm_pos.ne'
          have hδne : δ ≠ 0 := hδ_pos.ne'
          have hδinv : δ * (1 / δ) = 1 := mul_one_div_cancel hδne
          have hminv : (m : ℝ) * ((I.card : ℝ) / (m : ℝ)) = I.card := mul_div_cancel₀ _ hmne
          have h1 : δ * I.card * ((I.card : ℝ) * (m + L)) - δ * I.card * (m * (L + 1 / δ)) =
              m * (δ * I.card * I.card - δ * L * (I.card * (1 - I.card / (m : ℝ))) - I.card) := by
            linear_combination -(I.card : ℝ) * m * hδinv - δ * L * I.card * hminv
          have h2 : m * (δ * I.card * I.card - δ * L * (I.card * (1 - I.card / (m : ℝ))) - I.card) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hm_pos.le (by linarith)
          linarith
        exact le_of_mul_le_mul_left hstep (mul_pos hδ_pos hI_pos)
      · -- (2) Vertex-cut bound on A' × B'!
        have hem := expander_mixing f A' B' hord horth (mul_nonneg hδ_pos.le hL_nn) hhat
        have hlow : (∑ u : Fˣ, f u) / (Fintype.card Fˣ : ℝ) * A'.card * B'.card -
            (δ * L) * Real.sqrt (A'.card * (1 - A'.card / (Fintype.card Fˣ : ℝ)) *
              (B'.card * (1 - B'.card / (Fintype.card Fˣ : ℝ)))) ≤
            ∑ x ∈ A', ∑ y ∈ B', f (x * y) := by
          linarith [(abs_le.mp hem).1]
        have hup : ∑ x ∈ A', ∑ y ∈ B', f (x * y) ≤ 0 := by
          apply Finset.sum_nonpos; intro x hx
          apply Finset.sum_nonpos; intro y hy
          have hne : x ≠ y := fun h => Finset.disjoint_left.mp hAB' hx (h ▸ hy)
          have hnp : ¬ IsPrimitiveRoot ((x : F) * (y : F) + a₀) (Fintype.card Fˣ) :=
            fun hp => hnoAB' x hx y hy ⟨hne, hp⟩
          have hle := ctSieve_le_indPrim hES' (a₀ + (x * y : Fˣ))
          rw [indE_primeFactors_eq_prim, add_comm a₀, Units.val_mul, if_neg hnp] at hle
          simpa [f, Units.val_mul, add_comm] using hle
        rw [hcard_u] at hlow hμ_ge
        have h1 : δ * A'.card * B'.card ≤
            δ * L * Real.sqrt (A'.card * (1 - A'.card / (m : ℝ)) * (B'.card * (1 - B'.card / (m : ℝ)))) := by
          have hμ' : δ * A'.card * B'.card ≤ (∑ u : Fˣ, f u) / (m : ℝ) * A'.card * B'.card :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμ_ge (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
          linarith
        have h2 : (A'.card : ℝ) * B'.card ≤
            L * Real.sqrt (A'.card * (1 - A'.card / (m : ℝ)) * (B'.card * (1 - B'.card / (m : ℝ)))) := by
          apply le_of_mul_le_mul_left _ hδ_pos
          linarith [mul_assoc δ (A'.card : ℝ) (B'.card : ℝ),
            mul_assoc δ L (Real.sqrt (A'.card * (1 - A'.card / (m : ℝ)) * (B'.card * (1 - B'.card / (m : ℝ)))))]
        have hsubA : 1 - (A'.card : ℝ) / (m : ℝ) = ((B'.card : ℝ) + S.card) / m := by
          have hm_cast : (m : ℝ) = A'.card + B'.card + S.card := by exact_mod_cast hsum_card.symm
          rw [eq_div_iff hm_pos.ne', sub_mul, one_mul, div_mul_cancel₀ _ hm_pos.ne']; linarith
        have hsubB : 1 - (B'.card : ℝ) / (m : ℝ) = ((A'.card : ℝ) + S.card) / m := by
          have hm_cast : (m : ℝ) = A'.card + B'.card + S.card := by exact_mod_cast hsum_card.symm
          rw [eq_div_iff hm_pos.ne', sub_mul, one_mul, div_mul_cancel₀ _ hm_pos.ne']; linarith
        rw [hsubA, hsubB] at h2
        have hsq : ((A'.card : ℝ) * B'.card) ^ 2 ≤
            (L * Real.sqrt ((A'.card : ℝ) * (((B'.card : ℝ) + S.card) / m) *
              ((B'.card : ℝ) * (((A'.card : ℝ) + S.card) / m)))) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) h2 2
        have hrad_nn : 0 ≤ (A'.card : ℝ) * (((B'.card : ℝ) + S.card) / m) *
            ((B'.card : ℝ) * (((A'.card : ℝ) + S.card) / m)) :=
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hm_pos.le))
            (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hm_pos.le))
        rw [mul_pow L, Real.sq_sqrt hrad_nn] at hsq
        have hA_pos : (0 : ℝ) < A'.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hA'ne)
        have hB_pos : (0 : ℝ) < B'.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hB'ne)
        have hm2_pos : (0 : ℝ) < (m : ℝ) ^ 2 := sq_pos_of_pos hm_pos
        -- Multiply hsq by m^2 and cancel A'.card * B'.card > 0!
        have hstep : ((A'.card : ℝ) * B'.card) * ((m : ℝ) ^ 2 * A'.card * B'.card) ≤
            ((A'.card : ℝ) * B'.card) * (L ^ 2 * (A'.card + S.card) * (B'.card + S.card)) := by
          have hmul := mul_le_mul_of_nonneg_left hsq hm2_pos.le
          have hlhs : (m : ℝ) ^ 2 * ((A'.card : ℝ) * B'.card) ^ 2 =
              ((A'.card : ℝ) * B'.card) * ((m : ℝ) ^ 2 * A'.card * B'.card) := by ring
          have hm_c1 : (m : ℝ) * (((B'.card : ℝ) + S.card) / m) = (B'.card : ℝ) + S.card :=
            mul_div_cancel₀ _ hm_pos.ne'
          have hm_c2 : (m : ℝ) * (((A'.card : ℝ) + S.card) / m) = (A'.card : ℝ) + S.card :=
            mul_div_cancel₀ _ hm_pos.ne'
          have hrhs : (m : ℝ) ^ 2 * (L ^ 2 * ((A'.card : ℝ) * (((B'.card : ℝ) + S.card) / m) *
              ((B'.card : ℝ) * (((A'.card : ℝ) + S.card) / m)))) =
              ((A'.card : ℝ) * B'.card) * (L ^ 2 * (A'.card + S.card) * (B'.card + S.card)) := by
            calc (m : ℝ) ^ 2 * (L ^ 2 * ((A'.card : ℝ) * (((B'.card : ℝ) + S.card) / m) *
                    ((B'.card : ℝ) * (((A'.card : ℝ) + S.card) / m))))
                = ((A'.card : ℝ) * B'.card) * (L ^ 2 * ((m : ℝ) * (((A'.card : ℝ) + S.card) / m)) *
                    ((m : ℝ) * (((B'.card : ℝ) + S.card) / m))) := by ring
              _ = _ := by rw [hm_c1, hm_c2]
          linarith
        exact le_of_mul_le_mul_left hstep (mul_pos hA_pos hB_pos)
    · -- Upper-sieve constraints (for any E ⊆ m.primeFactors)
      intro E hE
      let Le : ℝ := ((2 : ℝ) ^ E.card - 1) * Real.sqrt q + 1
      have hE' : E ⊆ (Fintype.card Fˣ).primeFactors := hcard_u.symm ▸ hE
      have hE_prime : ∀ p ∈ E, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hE hp)
      have hθ_pos : 0 < theta E := theta_pos hE_prime
      have hLe_nn : 0 ≤ Le := by
        dsimp [Le]
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ E.card := one_le_pow₀ (by norm_num)
        nlinarith only [h1, Real.sqrt_nonneg (q : ℝ)]
      have hfb := indE_fourier_bounds a₀ ha₀ hord hE'
      let f : Fˣ → ℝ := fun u => indE E (a₀ + u)
      have hhat : ∀ k : Fin (Fintype.card Fˣ), k.val ≠ 0 →
          ‖∑ u : Fˣ, (f u : ℂ) * (χ₀ ^ k.val) u‖ ≤ theta E * Le := by
        intro k hk
        have hχne : χ₀ ^ k.val ≠ 1 := by
          intro h1
          have hdvd := (hord k.val).mp h1
          exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hdvd) (not_le.mpr k.2)
        exact hfb.2 (χ₀ ^ k.val) hχne
      have hμ_le : (∑ u : Fˣ, f u) / (Fintype.card Fˣ : ℝ) ≤ theta E := by
        rw [div_le_iff₀ (Nat.cast_pos.mpr Fintype.card_pos)]
        exact hfb.1
      constructor
      · -- (1) Upper sieve on I × (univ \ I)!
        let J : Finset Fˣ := Finset.univ \ I
        have hJ_card : (J.card : ℝ) = (m : ℝ) - I.card := by
          have h1 : J.card = m - I.card := by
            rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hcard_u]
          have hle : I.card ≤ m := hcard_u ▸ Finset.card_le_univ I
          rw [h1, Nat.cast_sub hle]
        have hlow_sum : (I.card : ℝ) * ((Nat.totient m - 1 : ℕ) : ℝ) ≤ ∑ x ∈ I, ∑ y ∈ J, f (x * y) := by
          have hterm : ∀ x ∈ I, ((Nat.totient m - 1 : ℕ) : ℝ) ≤ ∑ y ∈ J, f (x * y) := by
            intro x hx
            have hdeg := degree_ge_totient_sub_one a₀ hnprim' x
            have hdeg' : Nat.totient m - 1 ≤ (Finset.univ.filter fun y : Fˣ => adj x y).card := by
              simpa only [adj, hcard_u] using hdeg
            have hsub : (Finset.univ.filter fun y : Fˣ => adj x y) ⊆ J := by
              intro y hy
              have hadj := (Finset.mem_filter.mp hy).2
              exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, fun hyI => hind x hx y hyI hadj⟩
            have hge1 : ∀ y ∈ Finset.univ.filter (fun y : Fˣ => adj x y), (1 : ℝ) ≤ f (x * y) := by
              intro y hy
              have hp := (Finset.mem_filter.mp hy).2.2
              have hmono := indE_mono hE' (a₀ + (x * y : Fˣ))
              rw [indE_primeFactors_eq_prim, add_comm a₀, Units.val_mul, if_pos hp] at hmono
              simpa [f, Units.val_mul, add_comm] using hmono
            have hnn : ∀ y ∈ J, 0 ≤ f (x * y) := fun y _ => by
              rcases indE_zero_or_one E (a₀ + (x * y : Fˣ)) with h | h <;> linarith
            calc ((Nat.totient m - 1 : ℕ) : ℝ)
                ≤ ((Finset.univ.filter fun y : Fˣ => adj x y).card : ℝ) := by exact_mod_cast hdeg'
              _ = ∑ _y ∈ Finset.univ.filter (fun y : Fˣ => adj x y), (1 : ℝ) := by simp
              _ ≤ ∑ y ∈ Finset.univ.filter (fun y : Fˣ => adj x y), f (x * y) := Finset.sum_le_sum hge1
              _ ≤ ∑ y ∈ J, f (x * y) := Finset.sum_le_sum_of_subset_of_nonneg hsub fun y hy _ => hnn y hy
          calc (I.card : ℝ) * ((Nat.totient m - 1 : ℕ) : ℝ)
              = ∑ _x ∈ I, ((Nat.totient m - 1 : ℕ) : ℝ) := by simp
            _ ≤ ∑ x ∈ I, ∑ y ∈ J, f (x * y) := Finset.sum_le_sum hterm
        have hem := expander_mixing f I J hord horth (mul_nonneg hθ_pos.le hLe_nn) hhat
        have hup : ∑ x ∈ I, ∑ y ∈ J, f (x * y) ≤
            theta E * I.card * J.card +
            theta E * Le * Real.sqrt (I.card * (1 - I.card / (m : ℝ)) * (J.card * (1 - J.card / (m : ℝ)))) := by
          have h1 := (abs_le.mp hem).2
          rw [hcard_u] at h1 hμ_le
          have h2 : (∑ u : Fˣ, f u) / (m : ℝ) * I.card * J.card ≤ theta E * I.card * J.card :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμ_le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
          linarith
        have hrad : Real.sqrt (I.card * (1 - I.card / (m : ℝ)) * (J.card * (1 - J.card / (m : ℝ)))) =
            (I.card : ℝ) * J.card / m := by
          have h1 : 1 - (I.card : ℝ) / (m : ℝ) = (J.card : ℝ) / m := by
            rw [eq_div_iff hm_pos.ne', sub_mul, one_mul, div_mul_cancel₀ _ hm_pos.ne', hJ_card]
          have h2 : 1 - (J.card : ℝ) / (m : ℝ) = (I.card : ℝ) / m := by
            rw [eq_div_iff hm_pos.ne', sub_mul, one_mul, div_mul_cancel₀ _ hm_pos.ne', hJ_card]; ring
          rw [h1, h2]
          have hsq : (I.card : ℝ) * ((J.card : ℝ) / m) * ((J.card : ℝ) * ((I.card : ℝ) / m)) =
              ((I.card : ℝ) * J.card / m) ^ 2 := by ring
          rw [hsq, Real.sqrt_sq (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hm_pos.le)]
        rw [hrad] at hup
        have hI_pos : (0 : ℝ) < I.card := by exact_mod_cast (show 0 < I.card by omega)
        have hcomb : (I.card : ℝ) * (((Nat.totient m - 1 : ℕ) : ℝ) * m) ≤
            (I.card : ℝ) * (theta E * ((m : ℝ) - I.card) * (m + Le)) := by
          have hle := hlow_sum.trans hup
          rw [hJ_card] at hle
          have hmul := mul_le_mul_of_nonneg_left hle hm_pos.le
          have hm_c : (m : ℝ) * ((I.card : ℝ) * ((m : ℝ) - I.card) / m) = (I.card : ℝ) * ((m : ℝ) - I.card) :=
            mul_div_cancel₀ _ hm_pos.ne'
          have hrhs : (m : ℝ) * (theta E * I.card * ((m : ℝ) - I.card) +
              theta E * Le * ((I.card : ℝ) * ((m : ℝ) - I.card) / m)) =
              (I.card : ℝ) * (theta E * ((m : ℝ) - I.card) * (m + Le)) := by
            linear_combination theta E * Le * hm_c
          linarith
        exact le_of_mul_le_mul_left hcomb hI_pos
      · -- (2) Upper sieve on A' × (A' ∪ S)!
        let Y : Finset Fˣ := A' ∪ S
        have hY_card : (Y.card : ℝ) = (A'.card : ℝ) + S.card := by
          rw [Finset.card_union_of_disjoint hSA'.symm, Nat.cast_add]
        have hlow_sum : (A'.card : ℝ) * ((Nat.totient m - 1 : ℕ) : ℝ) ≤ ∑ x ∈ A', ∑ y ∈ Y, f (x * y) := by
          have hterm : ∀ x ∈ A', ((Nat.totient m - 1 : ℕ) : ℝ) ≤ ∑ y ∈ Y, f (x * y) := by
            intro x hx
            have hdeg := degree_ge_totient_sub_one a₀ hnprim' x
            have hdeg' : Nat.totient m - 1 ≤ (Finset.univ.filter fun y : Fˣ => adj x y).card := by
              simpa only [adj, hcard_u] using hdeg
            have hsub : (Finset.univ.filter fun y : Fˣ => adj x y) ⊆ Y := by
              intro y hy
              have hadj := (Finset.mem_filter.mp hy).2
              have hyU : y ∈ S ∪ A' ∪ B' := hcov'.symm ▸ Finset.mem_univ y
              simp only [Finset.mem_union] at hyU
              rcases hyU with (hyS | hyA) | hyB
              · exact Finset.mem_union_right _ hyS
              · exact Finset.mem_union_left _ hyA
              · exact absurd hadj (hnoAB' x hx y hyB)
            have hge1 : ∀ y ∈ Finset.univ.filter (fun y : Fˣ => adj x y), (1 : ℝ) ≤ f (x * y) := by
              intro y hy
              have hp := (Finset.mem_filter.mp hy).2.2
              have hmono := indE_mono hE' (a₀ + (x * y : Fˣ))
              rw [indE_primeFactors_eq_prim, add_comm a₀, Units.val_mul, if_pos hp] at hmono
              simpa [f, Units.val_mul, add_comm] using hmono
            have hnn : ∀ y ∈ Y, 0 ≤ f (x * y) := fun y _ => by
              rcases indE_zero_or_one E (a₀ + (x * y : Fˣ)) with h | h <;> linarith
            calc ((Nat.totient m - 1 : ℕ) : ℝ)
                ≤ ((Finset.univ.filter fun y : Fˣ => adj x y).card : ℝ) := by exact_mod_cast hdeg'
              _ = ∑ _y ∈ Finset.univ.filter (fun y : Fˣ => adj x y), (1 : ℝ) := by simp
              _ ≤ ∑ y ∈ Finset.univ.filter (fun y : Fˣ => adj x y), f (x * y) := Finset.sum_le_sum hge1
              _ ≤ ∑ y ∈ Y, f (x * y) := Finset.sum_le_sum_of_subset_of_nonneg hsub fun y hy _ => hnn y hy
          calc (A'.card : ℝ) * ((Nat.totient m - 1 : ℕ) : ℝ)
              = ∑ _x ∈ A', ((Nat.totient m - 1 : ℕ) : ℝ) := by simp
            _ ≤ ∑ x ∈ A', ∑ y ∈ Y, f (x * y) := Finset.sum_le_sum hterm
        have hem := expander_mixing f A' Y hord horth (mul_nonneg hθ_pos.le hLe_nn) hhat
        have hup : ∑ x ∈ A', ∑ y ∈ Y, f (x * y) ≤
            theta E * A'.card * Y.card +
            theta E * Le * Real.sqrt (A'.card * (1 - A'.card / (m : ℝ)) * (Y.card * (1 - Y.card / (m : ℝ)))) := by
          have h1 := (abs_le.mp hem).2
          rw [hcard_u] at h1 hμ_le
          have h2 : (∑ u : Fˣ, f u) / (m : ℝ) * A'.card * Y.card ≤ theta E * A'.card * Y.card :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμ_le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
          linarith
        have hsubA : 1 - (A'.card : ℝ) / (m : ℝ) = ((B'.card : ℝ) + S.card) / m := by
          have hm_cast : (m : ℝ) = A'.card + B'.card + S.card := by exact_mod_cast hsum_card.symm
          rw [eq_div_iff hm_pos.ne', sub_mul, one_mul, div_mul_cancel₀ _ hm_pos.ne']; linarith
        have hsubY : 1 - (Y.card : ℝ) / (m : ℝ) = (B'.card : ℝ) / m := by
          have hm_cast : (m : ℝ) = A'.card + B'.card + S.card := by exact_mod_cast hsum_card.symm
          rw [eq_div_iff hm_pos.ne', sub_mul, one_mul, div_mul_cancel₀ _ hm_pos.ne', hY_card]; linarith
        rw [hsubA, hsubY, hY_card] at hup
        have hsq_rw : (A'.card : ℝ) * (((B'.card : ℝ) + S.card) / m) *
            (((A'.card : ℝ) + S.card) * ((B'.card : ℝ) / m)) =
            ((A'.card : ℝ) * B'.card * (A'.card + S.card) * (B'.card + S.card)) / (m : ℝ) ^ 2 := by
          ring
        rw [hsq_rw, Real.sqrt_div (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
            (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
            (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))), Real.sqrt_sq hm_pos.le] at hup
        have hle := hlow_sum.trans hup
        have hmul := mul_le_mul_of_nonneg_left hle hm_pos.le
        have hm_c : (m : ℝ) * (Real.sqrt ((A'.card : ℝ) * B'.card * (A'.card + S.card) * (B'.card + S.card)) / m) =
            Real.sqrt ((A'.card : ℝ) * B'.card * (A'.card + S.card) * (B'.card + S.card)) :=
          mul_div_cancel₀ _ hm_pos.ne'
        have hrhs : (m : ℝ) * (theta E * A'.card * (A'.card + S.card) +
            theta E * Le * (Real.sqrt ((A'.card : ℝ) * B'.card * (A'.card + S.card) * (B'.card + S.card)) / m)) =
            theta E * A'.card * (A'.card + S.card) * m +
              theta E * Le * Real.sqrt ((A'.card : ℝ) * B'.card * (A'.card + S.card) * (B'.card + S.card)) := by
          linear_combination theta E * Le * hm_c
        linarith
  obtain ⟨e, he⟩ := hCE
  refine ⟨(Fin.castOrderIso hcard_u.symm).toEquiv.trans e, fun i => ?_⟩
  have hspec := he ⟨i.val, by omega⟩
  have hi1 : (Fin.castOrderIso hcard_u.symm).toEquiv i = ⟨i.val, by omega⟩ := by
    ext; rfl
  have hi2 : (Fin.castOrderIso hcard_u.symm).toEquiv ⟨(i.val + 1) % (Fintype.card F - 1), Nat.mod_lt _ (by omega)⟩ =
      ⟨(i.val + 1) % Fintype.card Fˣ, Nat.mod_lt _ (by omega)⟩ := by
    ext; simp [hcard_u, m, q]
  simp only [Equiv.trans_apply, hi1, hi2]
  let x : F := (e ⟨i.val, by omega⟩ : F) *
      (e ⟨(i.val + 1) % Fintype.card Fˣ, Nat.mod_lt _ (by omega)⟩ : F) + a₀
  have h2 : IsPrimitiveRoot x (Fintype.card Fˣ) := hspec.2
  rw [hcard_u] at h2
  exact h2

end AnalyticCriterion


-- Stage 2 draft: Unconditional analytic coverage for all q > 7 outside the 43 exceptions.
-- (Will be combined with Stage 1 once solver3_part1.lean finishes compiling!)

/- ### Part 3: Unconditional analytic coverage for all `q ≥ 8100` and `q < 8100` non-exceptions -/

section LargeQ

open Finset BigOperators

/-- Universal constant-bound Chvátal–Erdős contradiction: if `n ≥ n_lo`, `φ(n) ≥ θ_lo * n`,
`K ≤ K_hi`, `δ ≥ δ_lo`, and the rational parameters `(u0, c0, a0)` pass at `n_lo`,
then no `(α, k, a, b)` can satisfy the lower-sieve + degree constraints! -/
lemma ce_of_const_bounds
    {q n α k a b : ℕ} (hq : q = n + 1) (hn : 7 ≤ n)
    (_ha1 : 1 ≤ a) (hab : a ≤ b) (hsum : a + b + k = n) (hka : k < α)
    (hdeg : Nat.totient n ≤ a + k)
    {δ K : ℝ} (hδ_pos : 0 < δ) (hK_nn : 0 ≤ K)
    (hI : (α : ℝ) * (n + (K * Real.sqrt q + 1)) ≤ n * ((K * Real.sqrt q + 1) + 1 / δ))
    (hCut : (n : ℝ) ^ 2 * a * b ≤ (K * Real.sqrt q + 1) ^ 2 * (a + k) * (b + k))
    {n_lo θ_lo K_hi δ_lo sq_hi u0 c0 a0 : ℝ}
    (hn_lo_pos : 0 < n_lo) (hn_ge : n_lo ≤ n)
    (hθ_pos : 0 < θ_lo) (hθ_half : θ_lo ≤ 1 / 2)
    (hφ_ge : θ_lo * n ≤ (Nat.totient n : ℝ))
    (hK_le : K ≤ K_hi) (hδ_ge : δ_lo ≤ δ) (hδ_lo_pos : 0 < δ_lo)
    (hsq_pos : 0 < sq_hi) (hsq_ge : (n_lo + 1) ≤ sq_hi ^ 2)
    (hu0_def : (K_hi * sq_hi + 1) / n_lo ≤ u0) (hu0_lt1 : u0 < 1)
    (hc0_def : 1 / (δ_lo * n_lo) ≤ c0) (hc0_lt1 : c0 < 1)
    (ha0_def : (u0 + c0) / (1 + u0) ≤ a0) (_ha0_lt : a0 < θ_lo)
    (hmain : a0 * u0 ^ 2 < (θ_lo - a0) * (1 - θ_lo) * (1 - u0 ^ 2)) :
    False := by
  have hn_pos : (0 : ℝ) < n := lt_of_lt_of_le hn_lo_pos hn_ge
  let L : ℝ := K * Real.sqrt q + 1
  let u : ℝ := L / n
  let c : ℝ := 1 / (δ * n)
  have hL_pos : 0 < L := by dsimp [L]; positivity
  have hu_pos : 0 < u := div_pos hL_pos hn_pos
  -- Show u ≤ u0: (K * sqrt(n+1) + 1) / n ≤ (K_hi * sq_hi + 1) / n_lo
  -- Because sqrt(n+1)/n ≤ sqrt(n_lo+1)/n_lo ≤ sq_hi/n_lo (since (n+1)*n_lo^2 ≤ (n_lo+1)*n^2 for n ≥ n_lo ≥ 1)!
  have hsq_ratio : Real.sqrt (q : ℝ) / n ≤ sq_hi / n_lo := by
    rw [div_le_div_iff₀ hn_pos hn_lo_pos]
    have hq_cast : (q : ℝ) = n + 1 := by exact_mod_cast hq
    have hsq_le : ((n : ℝ) + 1) * n_lo ^ 2 ≤ (sq_hi * n) ^ 2 := by
      have h1 : ((n : ℝ) + 1) * n_lo ^ 2 ≤ (n_lo + 1) * (n : ℝ) ^ 2 := by
        have hid : (n_lo + 1) * (n : ℝ) ^ 2 - ((n : ℝ) + 1) * n_lo ^ 2 = ((n : ℝ) - n_lo) * ((n : ℝ) * n_lo + n + n_lo) := by ring
        have hf1 : 0 ≤ (n : ℝ) - n_lo := by linarith
        have hf2 : 0 ≤ (n : ℝ) * n_lo + n + n_lo := by positivity
        linarith [mul_nonneg hf1 hf2]
      have h2 : (n_lo + 1) * (n : ℝ) ^ 2 ≤ sq_hi ^ 2 * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hsq_ge (sq_nonneg (n : ℝ))
      linarith [mul_pow sq_hi (n : ℝ) 2]
    have hmul : (Real.sqrt (q : ℝ) * n_lo) ^ 2 ≤ (sq_hi * n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), hq_cast]
      exact hsq_le
    exact le_of_sq_le_sq hmul (by positivity)
  have hu_le : u ≤ u0 := by
    have hK_hi_nn : 0 ≤ K_hi := le_trans hK_nn hK_le
    have h1 : K * Real.sqrt (q : ℝ) / n ≤ K_hi * sq_hi / n_lo := by
      calc K * Real.sqrt (q : ℝ) / n = K * (Real.sqrt (q : ℝ) / n) := by ring
        _ ≤ K_hi * (sq_hi / n_lo) :=
            mul_le_mul hK_le hsq_ratio (by positivity) hK_hi_nn
        _ = K_hi * sq_hi / n_lo := by ring
    have h2 : 1 / (n : ℝ) ≤ 1 / n_lo := one_div_le_one_div_of_le hn_lo_pos hn_ge
    dsimp [u, L]
    have h3 : (K * Real.sqrt (q : ℝ) + 1) / n = K * Real.sqrt (q : ℝ) / n + 1 / n := add_div _ _ _
    have h4 : (K_hi * sq_hi + 1) / n_lo = K_hi * sq_hi / n_lo + 1 / n_lo := add_div _ _ _
    linarith
  have hc_le : c ≤ c0 := by
    dsimp [c]
    exact (one_div_le_one_div_of_le (mul_pos hδ_lo_pos hn_lo_pos)
      (mul_le_mul hδ_ge hn_ge hn_lo_pos.le hδ_pos.le)).trans hc0_def
  have hc_pos : 0 < c := by dsimp [c]; positivity
  have hu0_pos : 0 < u0 := lt_of_lt_of_le hu_pos hu_le
  have ha0_nn : 0 ≤ a0 := le_trans (div_nonneg (by linarith) (by linarith)) ha0_def
  -- Show (α : ℝ) / n ≤ a0!
  have hα_div : (α : ℝ) / n ≤ a0 := by
    have h1 : (α : ℝ) / n ≤ (u + c) / (1 + u) := by
      rw [div_le_div_iff₀ hn_pos (by linarith)]
      have hrew : (u + c) * n = L + 1 / δ := by
        dsimp [u, c]; field_simp [hn_pos.ne', hδ_pos.ne']
      have hrew2 : (1 + u) * n = n + L := by
        dsimp [u]; field_simp [hn_pos.ne']
      have hmul : (α : ℝ) * (1 + u) * n ≤ (u + c) * n * n := by
        have hlhs : (α : ℝ) * (1 + u) * n = (α : ℝ) * ((1 + u) * n) := by ring
        rw [hlhs, hrew, hrew2]; linarith
      exact le_of_mul_le_mul_right hmul hn_pos
    have h2 : (u + c) / (1 + u) ≤ a0 := by
      have h2' : (u + c) / (1 + u) ≤ (u0 + c0) / (1 + u0) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        have hid : (u0 + c0) * (1 + u) - (u + c) * (1 + u0) =
            (u0 - u) * (1 - c0) + (c0 - c) * (1 + u0) := by ring
        have hp1 : 0 ≤ (u0 - u) * (1 - c0) := mul_nonneg (by linarith) (by linarith)
        have hp2 : 0 ≤ (c0 - c) * (1 + u0) := mul_nonneg (by linarith) (by linarith)
        linarith
      exact h2'.trans ha0_def
    exact h1.trans h2
  have hk_le : (k : ℝ) ≤ a0 * n := by
    have hk_lt : (k : ℝ) < α := by exact_mod_cast hka
    have hα_le : (α : ℝ) ≤ a0 * n := (div_le_iff₀ hn_pos).mp hα_div
    linarith
  have hL_le : L ≤ u0 * n := (div_le_iff₀ hn_pos).mp hu_le
  -- Check Dirac-cut: if 2 * φ(n) > (1 + a0) * n, instant contradiction with a ≤ b and a + b + k = n!
  have hsumR : (a : ℝ) + b + k = n := by exact_mod_cast hsum
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hdegR : (Nat.totient n : ℝ) ≤ a + k := by exact_mod_cast hdeg
  have hφ_hi : (Nat.totient n : ℝ) ≤ ((1 + a0) / 2) * n := by linarith
  -- Algebraic identity 1: a * b ≥ (φ - k) * (n - φ) ≥ (φ - a0 * n) * (n - φ) ≥ (θ_lo - a0) * (1 - θ_lo) * n^2!
  have hφ_le_n : (Nat.totient n : ℝ) ≤ n := by exact_mod_cast Nat.totient_le n
  have hab_ge1 : ((Nat.totient n : ℝ) - k) * (n - Nat.totient n) ≤ (a : ℝ) * b := by
    have hid : (a : ℝ) * b - ((Nat.totient n : ℝ) - k) * (n - Nat.totient n) =
        ((a : ℝ) + k - Nat.totient n) * ((b : ℝ) + k - Nat.totient n) := by
      linear_combination ((Nat.totient n : ℝ) - k) * hsumR
    have h1 : 0 ≤ (a : ℝ) + k - Nat.totient n := by linarith
    have h2 : 0 ≤ (b : ℝ) + k - Nat.totient n := by linarith
    linarith [mul_nonneg h1 h2]
  have hab_ge2 : (θ_lo - a0) * (1 - θ_lo) * (n : ℝ) ^ 2 ≤ (a : ℝ) * b := by
    have h1 : ((Nat.totient n : ℝ) - a0 * n) * (n - Nat.totient n) ≤
        ((Nat.totient n : ℝ) - k) * (n - Nat.totient n) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : (θ_lo - a0) * (1 - θ_lo) * (n : ℝ) ^ 2 ≤
        ((Nat.totient n : ℝ) - a0 * n) * (n - Nat.totient n) := by
      have hid : ((Nat.totient n : ℝ) - a0 * n) * (n - Nat.totient n) -
          (θ_lo - a0) * (1 - θ_lo) * (n : ℝ) ^ 2 =
          ((Nat.totient n : ℝ) - θ_lo * n) * ((1 + a0) * n - Nat.totient n - θ_lo * n) := by ring
      have hfac1 : 0 ≤ (Nat.totient n : ℝ) - θ_lo * n := by linarith
      have hθn : θ_lo * n ≤ (1 / 2) * n := mul_le_mul_of_nonneg_right hθ_half hn_pos.le
      have ha0n : 0 ≤ a0 * n := mul_nonneg ha0_nn hn_pos.le
      have hfac2 : 0 ≤ (1 + a0) * n - Nat.totient n - θ_lo * n := by linarith
      linarith [mul_nonneg hfac1 hfac2]
    linarith
  -- Algebraic identity 2: (a + k) * (b + k) = a * b + k * n, so a * b * (n^2 - L^2) ≤ k * n * L^2!
  have hcut2 : (a : ℝ) * b * ((n : ℝ) ^ 2 - L ^ 2) ≤ k * n * L ^ 2 := by
    have hid : ((a : ℝ) + k) * ((b : ℝ) + k) = a * b + k * n := by
      linear_combination k * hsumR
    have hCut' : (n : ℝ) ^ 2 * a * b ≤ L ^ 2 * ((a : ℝ) * b + k * n) := by
      have : L ^ 2 * ((a : ℝ) + k) * ((b : ℝ) + k) = L ^ 2 * (((a : ℝ) + k) * ((b : ℝ) + k)) := by ring
      rw [← hid, ← this]; exact hCut
    linarith [show (n : ℝ) ^ 2 * a * b - L ^ 2 * ((a : ℝ) * b + k * n) =
        (a : ℝ) * b * ((n : ℝ) ^ 2 - L ^ 2) - k * n * L ^ 2 by ring]
  have hL2_le : L ^ 2 ≤ u0 ^ 2 * (n : ℝ) ^ 2 := by
    have h1 : L * L ≤ (u0 * n) * (u0 * n) :=
      mul_le_mul hL_le hL_le hL_pos.le (mul_nonneg hu0_pos.le hn_pos.le)
    linarith [sq L, sq (u0 * n), mul_pow u0 (n : ℝ) 2]
  have h1sub_pos : 0 < 1 - u0 ^ 2 := by nlinarith only [hu0_pos, hu0_lt1]
  have hfinal_lhs : (θ_lo - a0) * (1 - θ_lo) * (1 - u0 ^ 2) * (n : ℝ) ^ 4 ≤
      (a : ℝ) * b * ((n : ℝ) ^ 2 - L ^ 2) := by
    have h1 : (1 - u0 ^ 2) * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 - L ^ 2 := by linarith
    have h3 : ((θ_lo - a0) * (1 - θ_lo) * (n : ℝ) ^ 2) * ((1 - u0 ^ 2) * (n : ℝ) ^ 2) ≤
        ((a : ℝ) * b) * ((n : ℝ) ^ 2 - L ^ 2) :=
      mul_le_mul hab_ge2 h1 (mul_nonneg h1sub_pos.le (sq_nonneg _))
        (mul_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b))
    linarith [show ((θ_lo - a0) * (1 - θ_lo) * (n : ℝ) ^ 2) * ((1 - u0 ^ 2) * (n : ℝ) ^ 2) =
        (θ_lo - a0) * (1 - θ_lo) * (1 - u0 ^ 2) * (n : ℝ) ^ 4 by ring]
  have hfinal_rhs : (k : ℝ) * n * L ^ 2 ≤ a0 * u0 ^ 2 * (n : ℝ) ^ 4 := by
    have hkn : (k : ℝ) * n ≤ (a0 * n) * n := mul_le_mul_of_nonneg_right hk_le hn_pos.le
    have h1 : (k : ℝ) * n * L ^ 2 ≤ (a0 * n) * n * (u0 ^ 2 * (n : ℝ) ^ 2) :=
      mul_le_mul hkn hL2_le (sq_nonneg L) (mul_nonneg (mul_nonneg ha0_nn hn_pos.le) hn_pos.le)
    linarith [show (a0 * (n : ℝ)) * n * (u0 ^ 2 * (n : ℝ) ^ 2) = a0 * u0 ^ 2 * (n : ℝ) ^ 4 by ring]
  have hn4_pos : (0 : ℝ) < (n : ℝ) ^ 4 := pow_pos hn_pos 4
  have hlt := mul_lt_mul_of_pos_right hmain hn4_pos
  linarith

/-- Helper: lower bounds on the first 8 primes of a strictly sorted list of primes. -/
lemma sorted_primes_ge {l : List ℕ} (hprime : ∀ p ∈ l, p.Prime) (hsorted : l.Pairwise (· < ·)) :
    (∀ h : 0 < l.length, 2 ≤ l[0]) ∧
    (∀ h : 1 < l.length, 3 ≤ l[1]) ∧
    (∀ h : 2 < l.length, 5 ≤ l[2]) ∧
    (∀ h : 3 < l.length, 7 ≤ l[3]) ∧
    (∀ h : 4 < l.length, 11 ≤ l[4]) ∧
    (∀ h : 5 < l.length, 13 ≤ l[5]) ∧
    (∀ h : 6 < l.length, 17 ≤ l[6]) ∧
    (∀ h : 7 < l.length, 19 ≤ l[7]) := by
  have hlt : ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i < j → l[i] < l[j] :=
    fun i j hi hj hij => List.pairwise_iff_getElem.mp hsorted i j hi hj hij
  have h0 : ∀ h : 0 < l.length, 2 ≤ l[0] := fun h => (hprime _ (List.getElem_mem h)).two_le
  have h1 : ∀ h : 1 < l.length, 3 ≤ l[1] := fun h => by
    have := h0 (by omega); have := hlt 0 1 (by omega) h (by omega); omega
  have h2 : ∀ h : 2 < l.length, 5 ≤ l[2] := fun h => by
    have := h1 (by omega); have := hlt 1 2 (by omega) h (by omega)
    have hp := hprime _ (List.getElem_mem h)
    by_contra hle; have heq : l[2] = 4 := by omega
    rw [heq] at hp; exact absurd hp (by decide)
  have h3 : ∀ h : 3 < l.length, 7 ≤ l[3] := fun h => by
    have := h2 (by omega); have := hlt 2 3 (by omega) h (by omega)
    have hp := hprime _ (List.getElem_mem h)
    by_contra hle; have heq : l[3] = 6 := by omega
    rw [heq] at hp; exact absurd hp (by decide)
  have h4 : ∀ h : 4 < l.length, 11 ≤ l[4] := fun h => by
    have := h3 (by omega); have := hlt 3 4 (by omega) h (by omega)
    have hp := hprime _ (List.getElem_mem h)
    by_contra hle
    have hcases : l[4] = 8 ∨ l[4] = 9 ∨ l[4] = 10 := by omega
    rcases hcases with heq | heq | heq <;> (rw [heq] at hp; exact absurd hp (by decide))
  have h5 : ∀ h : 5 < l.length, 13 ≤ l[5] := fun h => by
    have := h4 (by omega); have := hlt 4 5 (by omega) h (by omega)
    have hp := hprime _ (List.getElem_mem h)
    by_contra hle; have heq : l[5] = 12 := by omega
    rw [heq] at hp; exact absurd hp (by decide)
  have h6 : ∀ h : 6 < l.length, 17 ≤ l[6] := fun h => by
    have := h5 (by omega); have := hlt 5 6 (by omega) h (by omega)
    have hp := hprime _ (List.getElem_mem h)
    by_contra hle
    have hcases : l[6] = 14 ∨ l[6] = 15 ∨ l[6] = 16 := by omega
    rcases hcases with heq | heq | heq <;> (rw [heq] at hp; exact absurd hp (by decide))
  have h7 : ∀ h : 7 < l.length, 19 ≤ l[7] := fun h => by
    have := h6 (by omega); have := hlt 6 7 (by omega) h (by omega)
    have hp := hprime _ (List.getElem_mem h)
    by_contra hle; have heq : l[7] = 18 := by omega
    rw [heq] at hp; exact absurd hp (by decide)
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

/-- All `ω(n) ≥ 8` pass unconditionally with plain `s = 0` (`E = n.primeFactors, Sp = ∅`)! -/
lemma omega_ge_eight_contradiction
    {q n α k a b : ℕ} (hq : q = n + 1) (hn : 7 ≤ n)
    (hω : 8 ≤ n.primeFactors.card)
    (ha1 : 1 ≤ a) (hab : a ≤ b) (hsum : a + b + k = n) (hka : k < α)
    (hdeg : Nat.totient n ≤ a + k)
    (hI : (α : ℝ) * (n + (((2 : ℝ) ^ n.primeFactors.card - 1) * Real.sqrt q + 1)) ≤
      n * ((((2 : ℝ) ^ n.primeFactors.card - 1) * Real.sqrt q + 1) + 1 / theta n.primeFactors))
    (hCut : (n : ℝ) ^ 2 * a * b ≤
      (((2 : ℝ) ^ n.primeFactors.card - 1) * Real.sqrt q + 1) ^ 2 * (a + k) * (b + k)) :
    False := by
  let S := n.primeFactors
  let P8 : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19}
  have hP8_card : P8.card = 8 := by decide
  have hP8_prod : ∏ p ∈ P8, p = 9699690 := by decide
  have hP8_phi : ∏ p ∈ P8, (p - 1) = 1658880 := by decide
  have hS_prime : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hrad_le_n : ∏ p ∈ S, p ≤ n := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)
  -- Compare B = S \ P8 (all primes ≥ 23) and C = P8 \ S (all primes ≤ 19), with |C| ≤ |B|!
  let A_set := S ∩ P8
  let B_set := S \ P8
  let C_set := P8 \ S
  have hBC_card : C_set.card ≤ B_set.card := by
    have hS8 : 8 ≤ S.card := hω
    have h1 : A_set.card + B_set.card = S.card := Finset.card_inter_add_card_sdiff S P8
    have h2 : A_set.card + C_set.card = P8.card := by
      have : A_set = P8 ∩ S := Finset.inter_comm S P8
      rw [this]; exact Finset.card_inter_add_card_sdiff P8 S
    omega
  have hAB_disj : Disjoint A_set B_set :=
    Finset.disjoint_left.mpr fun x h1 h2 => (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2
  have hAC_disj : Disjoint A_set C_set :=
    Finset.disjoint_left.mpr fun x h1 h2 => (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).1
  have hS_eq_AB : A_set ∪ B_set = S := by
    rw [Finset.union_comm]; exact Finset.sdiff_union_inter S P8
  have hP8_eq_AC : A_set ∪ C_set = P8 := by
    dsimp only [A_set, C_set]; rw [Finset.inter_comm, Finset.union_comm]; exact Finset.sdiff_union_inter P8 S
  have hB_ge23 : ∀ p ∈ B_set, 23 ≤ p := by
    intro p hp
    have hpr := hS_prime p (Finset.mem_sdiff.mp hp).1
    have hnot := (Finset.mem_sdiff.mp hp).2
    by_contra hlt
    have hle : p ≤ 22 := by omega
    -- Every prime ≤ 22 is in P8!
    have hmem : p ∈ P8 := by
      interval_cases p <;> first | (exfalso; exact absurd hpr (by decide)) | decide
    exact hnot hmem
  have hC_le19 : ∀ p ∈ C_set, p ≤ 19 := by
    intro p hp
    have hmem := (Finset.mem_sdiff.mp hp).1
    simp only [P8, Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hC_ge2 : ∀ p ∈ C_set, 2 ≤ p := by
    intro p hp
    have hmem := (Finset.mem_sdiff.mp hp).1
    simp only [P8, Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  -- (1) 9699690 ≤ ∏ S ≤ n!
  have hn_ge : 9699690 ≤ n := by
    have hCB : ∏ p ∈ C_set, p ≤ ∏ p ∈ B_set, p := by
      calc ∏ p ∈ C_set, p ≤ ∏ _p ∈ C_set, 19 := Finset.prod_le_prod' fun p hp => hC_le19 p hp
        _ = 19 ^ C_set.card := by simp
        _ ≤ 23 ^ B_set.card := le_trans (Nat.pow_le_pow_left (by norm_num) _) (Nat.pow_le_pow_right (by norm_num) hBC_card)
        _ = ∏ _p ∈ B_set, 23 := by simp
        _ ≤ ∏ p ∈ B_set, p := Finset.prod_le_prod' fun p hp => hB_ge23 p hp
    have hS_split : ∏ p ∈ S, p = (∏ p ∈ A_set, p) * (∏ p ∈ B_set, p) := by
      rw [← Finset.prod_union hAB_disj, hS_eq_AB]
    have hP8_split : ∏ p ∈ P8, p = (∏ p ∈ A_set, p) * (∏ p ∈ C_set, p) := by
      rw [← Finset.prod_union hAC_disj, hP8_eq_AC]
    have hprod_ge : 9699690 ≤ ∏ p ∈ S, p := by
      rw [← hP8_prod, hP8_split, hS_split]
      exact Nat.mul_le_mul_left _ hCB
    omega
  -- (2) 4^|S| * 9699690 ≤ 4^8 * ∏ S (hence 2^|S| / √n ≤ 256 / √9699690 < 0.083)!
  have h2pow_sq : 4 ^ S.card * 9699690 ≤ 4 ^ 8 * n := by
    have hCB : 4 ^ B_set.card * ∏ p ∈ C_set, p ≤ 4 ^ C_set.card * ∏ p ∈ B_set, p := by
      have h1 : ∏ p ∈ C_set, p ≤ 19 ^ C_set.card := by
        simpa using Finset.prod_le_prod' (s := C_set) (f := id) (g := fun _ => 19) fun p hp => hC_le19 p hp
      have h2 : 23 ^ B_set.card ≤ ∏ p ∈ B_set, p := by
        simpa using Finset.prod_le_prod' (s := B_set) (f := fun _ => 23) (g := id) fun p hp => hB_ge23 p hp
      have h3 : 4 ^ B_set.card * 19 ^ C_set.card ≤ 4 ^ C_set.card * 23 ^ B_set.card := by
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hBC_card
        rw [hd, pow_add, pow_add]
        have h19_23 : 19 ^ C_set.card ≤ 23 ^ C_set.card := Nat.pow_le_pow_left (by norm_num) _
        have h4_23 : 4 ^ d ≤ 23 ^ d := Nat.pow_le_pow_left (by norm_num) _
        calc 4 ^ C_set.card * 4 ^ d * 19 ^ C_set.card
            = 4 ^ C_set.card * (19 ^ C_set.card * 4 ^ d) := by ring
          _ ≤ 4 ^ C_set.card * (23 ^ C_set.card * 23 ^ d) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul h19_23 h4_23)
      calc 4 ^ B_set.card * ∏ p ∈ C_set, p
          ≤ 4 ^ B_set.card * 19 ^ C_set.card := Nat.mul_le_mul_left _ h1
        _ ≤ 4 ^ C_set.card * 23 ^ B_set.card := h3
        _ ≤ 4 ^ C_set.card * ∏ p ∈ B_set, p := Nat.mul_le_mul_left _ h2
    have hS_card : S.card = A_set.card + B_set.card := (Finset.card_inter_add_card_sdiff S P8).symm
    have hP8_c : 8 = A_set.card + C_set.card := by
      rw [← hP8_card]; dsimp only [A_set, C_set]; rw [Finset.inter_comm]; exact (Finset.card_inter_add_card_sdiff P8 S).symm
    have hS_split : ∏ p ∈ S, p = (∏ p ∈ A_set, p) * (∏ p ∈ B_set, p) := by
      rw [← Finset.prod_union hAB_disj, hS_eq_AB]
    have hP8_split : ∏ p ∈ P8, p = (∏ p ∈ A_set, p) * (∏ p ∈ C_set, p) := by
      rw [← Finset.prod_union hAC_disj, hP8_eq_AC]
    have hrad_ineq : 4 ^ S.card * 9699690 ≤ 4 ^ 8 * ∏ p ∈ S, p := by
      rw [← hP8_prod, hS_card, hP8_c, pow_add, pow_add, hS_split, hP8_split]
      calc 4 ^ A_set.card * 4 ^ B_set.card * ((∏ p ∈ A_set, p) * ∏ p ∈ C_set, p)
          = (4 ^ A_set.card * ∏ p ∈ A_set, p) * (4 ^ B_set.card * ∏ p ∈ C_set, p) := by ring
        _ ≤ (4 ^ A_set.card * ∏ p ∈ A_set, p) * (4 ^ C_set.card * ∏ p ∈ B_set, p) :=
            Nat.mul_le_mul_left _ hCB
        _ = 4 ^ A_set.card * 4 ^ C_set.card * ((∏ p ∈ A_set, p) * ∏ p ∈ B_set, p) := by ring
    exact hrad_ineq.trans (Nat.mul_le_mul_left _ hrad_le_n)
  -- (3) Magic cutoff 18: for p ∈ C (≤ 19), (p-1)^2 ≤ 18*p; for p ∈ B (≥ 23), 18*p ≤ (p-1)^2!
  have htheta_sq : (∏ p ∈ P8, ((p - 1 : ℝ) ^ 2 / (4 * p))) ≤ ∏ p ∈ S, ((p - 1 : ℝ) ^ 2 / (4 * p)) := by
    have hC_ub : ∀ p ∈ C_set, ((p - 1 : ℝ) ^ 2 / (4 * p)) ≤ 9 / 2 := by
      intro p hp
      have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hC_ge2 p hp
      have hp19R : (p : ℝ) ≤ 19 := by exact_mod_cast hC_le19 p hp
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith only [hpR, hp19R]
    have hB_lb : ∀ p ∈ B_set, (9 / 2 : ℝ) ≤ (p - 1 : ℝ) ^ 2 / (4 * p) := by
      intro p hp
      have hp23 : (23 : ℝ) ≤ p := by exact_mod_cast hB_ge23 p hp
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith only [hp23]
    have hCB : ∏ p ∈ C_set, ((p - 1 : ℝ) ^ 2 / (4 * p)) ≤ ∏ p ∈ B_set, ((p - 1 : ℝ) ^ 2 / (4 * p)) := by
      calc ∏ p ∈ C_set, ((p - 1 : ℝ) ^ 2 / (4 * p))
          ≤ ∏ _p ∈ C_set, (9 / 2 : ℝ) := Finset.prod_le_prod (fun _ _ => by positivity) hC_ub
        _ = (9 / 2 : ℝ) ^ C_set.card := Finset.prod_const _
        _ ≤ (9 / 2 : ℝ) ^ B_set.card := pow_le_pow_right₀ (by norm_num) hBC_card
        _ = ∏ _p ∈ B_set, (9 / 2 : ℝ) := (Finset.prod_const _).symm
        _ ≤ ∏ p ∈ B_set, ((p - 1 : ℝ) ^ 2 / (4 * p)) :=
            Finset.prod_le_prod (fun _ _ => by norm_num) hB_lb
    have hS_split : ∏ p ∈ S, ((p - 1 : ℝ) ^ 2 / (4 * p)) =
        (∏ p ∈ A_set, ((p - 1 : ℝ) ^ 2 / (4 * p))) * (∏ p ∈ B_set, ((p - 1 : ℝ) ^ 2 / (4 * p))) := by
      rw [← Finset.prod_union hAB_disj, hS_eq_AB]
    have hP8_split : ∏ p ∈ P8, ((p - 1 : ℝ) ^ 2 / (4 * p)) =
        (∏ p ∈ A_set, ((p - 1 : ℝ) ^ 2 / (4 * p))) * (∏ p ∈ C_set, ((p - 1 : ℝ) ^ 2 / (4 * p))) := by
      rw [← Finset.prod_union hAC_disj, hP8_eq_AC]
    rw [hP8_split, hS_split]
    exact mul_le_mul_of_nonneg_left hCB (Finset.prod_nonneg fun _ _ => by positivity)
  have hP8_val : (43 / 10 : ℝ) < ∏ p ∈ P8, ((p - 1 : ℝ) ^ 2 / (4 * p)) := by
    dsimp only [P8]
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton]
    norm_num
  have hS_prod_eq : ∏ p ∈ S, ((p - 1 : ℝ) ^ 2 / (4 * p)) =
      (theta S) ^ 2 * (∏ p ∈ S, (p : ℝ)) / ((2 : ℝ) ^ S.card) ^ 2 := by
    have hterm : ∀ p ∈ S, ((p - 1 : ℝ) ^ 2 / (4 * p)) = (1 - 1 / (p : ℝ)) ^ 2 * (p : ℝ) / 4 := by
      intro p hp
      have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (hS_prime p hp).pos
      field_simp [hp_pos.ne']
    rw [Finset.prod_congr rfl hterm, Finset.prod_div_distrib, Finset.prod_mul_distrib,
      Finset.prod_pow, Finset.prod_const]
    have h4pow : (4 : ℝ) ^ S.card = ((2 : ℝ) ^ S.card) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h4pow]; rfl
  have hθ_pos : 0 < theta S := theta_pos hS_prime
  have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ S.card := by positivity
  have hrad_le_nR : ∏ p ∈ S, (p : ℝ) ≤ n := by rw [← Nat.cast_prod]; exact_mod_cast hrad_le_n
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq_le : (q : ℝ) ≤ (9699691 / 9699690 : ℝ) * n := by
    have hqR : (q : ℝ) = n + 1 := by exact_mod_cast hq
    have hnR : (9699690 : ℝ) ≤ n := by exact_mod_cast hn_ge
    linarith
  have h2pow_theta_sq : (43 / 10 : ℝ) * ((2 : ℝ) ^ S.card) ^ 2 ≤ (theta S) ^ 2 * n := by
    have h2 := hP8_val.le.trans htheta_sq
    rw [hS_prod_eq, le_div_iff₀ (sq_pos_of_pos h2pow_pos)] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left hrad_le_nR (sq_nonneg (theta S)))
  have h2pow_n_sq : ((2 : ℝ) ^ S.card) ^ 2 * 9699690 ≤ 65536 * n := by
    have hcast : (4 : ℝ) ^ S.card * 9699690 ≤ (4 : ℝ) ^ 8 * n := by exact_mod_cast h2pow_sq
    have h4eq : (4 : ℝ) ^ S.card = ((2 : ℝ) ^ S.card) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h4eq] at hcast
    linarith [show (4 : ℝ) ^ 8 = 65536 by norm_num]
  let L : ℝ := ((2 : ℝ) ^ S.card - 1) * Real.sqrt q + 1
  have hL_le_2sq : L ≤ (2 : ℝ) ^ S.card * Real.sqrt q := by
    have hsq1 : (1 : ℝ) ≤ Real.sqrt q := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ q by omega))
    dsimp [L]; linarith
  -- Bound 1: L ≤ (49/100) * (theta S * n)
  have hL_le_θ : L ≤ (49 / 100 : ℝ) * (theta S * n) := by
    have hsq : ((2 : ℝ) ^ S.card * Real.sqrt (q : ℝ)) ^ 2 ≤ ((49 / 100 : ℝ) * (theta S * n)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      have h3 : ((2 : ℝ) ^ S.card) ^ 2 * q ≤ ((2 : ℝ) ^ S.card) ^ 2 * ((9699691 / 9699690 : ℝ) * n) :=
        mul_le_mul_of_nonneg_left hq_le (sq_nonneg _)
      have h4 : ((2 : ℝ) ^ S.card) ^ 2 ≤ (10 / 43 : ℝ) * (theta S) ^ 2 * n := by linarith
      have h5 : (10 / 43 : ℝ) * (9699691 / 9699690 : ℝ) ≤ (49 / 100 : ℝ) ^ 2 := by norm_num
      have h6 : ((2 : ℝ) ^ S.card) ^ 2 * ((9699691 / 9699690 : ℝ) * n) ≤
          ((10 / 43 : ℝ) * (theta S) ^ 2 * n) * ((9699691 / 9699690 : ℝ) * n) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
      have h7 : ((10 / 43 : ℝ) * (theta S) ^ 2 * n) * ((9699691 / 9699690 : ℝ) * n) ≤
          ((49 / 100 : ℝ) * (theta S * n)) ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right h5 (mul_nonneg (sq_nonneg (theta S)) (sq_nonneg (n : ℝ)))
        linarith [show ((10 / 43 : ℝ) * (theta S) ^ 2 * n) * ((9699691 / 9699690 : ℝ) * n) =
            ((10 / 43 : ℝ) * (9699691 / 9699690 : ℝ)) * ((theta S) ^ 2 * (n : ℝ) ^ 2) by ring,
          show ((49 / 100 : ℝ) * (theta S * n)) ^ 2 = (49 / 100 : ℝ) ^ 2 * ((theta S) ^ 2 * (n : ℝ) ^ 2) by ring]
      linarith
    have h2 : (2 : ℝ) ^ S.card * Real.sqrt (q : ℝ) ≤ (49 / 100 : ℝ) * (theta S * n) :=
      le_of_sq_le_sq hsq (by positivity)
    linarith
  -- Bound 2: L ≤ (1/10) * n
  have hL_le_n : L ≤ (1 / 10 : ℝ) * n := by
    have hsq : ((2 : ℝ) ^ S.card * Real.sqrt (q : ℝ)) ^ 2 ≤ ((1 / 10 : ℝ) * n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      have h3 : ((2 : ℝ) ^ S.card) ^ 2 * q ≤ ((2 : ℝ) ^ S.card) ^ 2 * ((9699691 / 9699690 : ℝ) * n) :=
        mul_le_mul_of_nonneg_left hq_le (sq_nonneg _)
      have h4 : ((2 : ℝ) ^ S.card) ^ 2 ≤ (65536 / 9699690 : ℝ) * n := by linarith
      have h5 : (65536 / 9699690 : ℝ) * (9699691 / 9699690 : ℝ) ≤ (1 / 10 : ℝ) ^ 2 := by norm_num
      have h6 : ((2 : ℝ) ^ S.card) ^ 2 * ((9699691 / 9699690 : ℝ) * n) ≤
          ((65536 / 9699690 : ℝ) * n) * ((9699691 / 9699690 : ℝ) * n) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
      have h7 : ((65536 / 9699690 : ℝ) * n) * ((9699691 / 9699690 : ℝ) * n) ≤ ((1 / 10 : ℝ) * n) ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right h5 (sq_nonneg (n : ℝ))
        linarith [show ((65536 / 9699690 : ℝ) * n) * ((9699691 / 9699690 : ℝ) * n) =
            ((65536 / 9699690 : ℝ) * (9699691 / 9699690 : ℝ)) * (n : ℝ) ^ 2 by ring,
          show ((1 / 10 : ℝ) * n) ^ 2 = (1 / 10 : ℝ) ^ 2 * (n : ℝ) ^ 2 by ring]
      linarith
    have h2 : (2 : ℝ) ^ S.card * Real.sqrt (q : ℝ) ≤ (1 / 10 : ℝ) * n :=
      le_of_sq_le_sq hsq (by positivity)
    linarith
  -- Bound 3: 1 / theta S ≤ (1 / 100) * (theta S * n)
  have hinv_le : 1 / theta S ≤ (1 / 100 : ℝ) * (theta S * n) := by
    have h256 : (256 : ℝ) ≤ (2 : ℝ) ^ S.card := by
      calc (256 : ℝ) = (2 : ℝ) ^ 8 := by norm_num
        _ ≤ (2 : ℝ) ^ S.card := pow_le_pow_right₀ (by norm_num) hω
    have h256_sq : (256 : ℝ) ^ 2 ≤ ((2 : ℝ) ^ S.card) ^ 2 := by nlinarith only [h256]
    have hbig : (100 : ℝ) ≤ (theta S) ^ 2 * n := by linarith
    rw [div_le_iff₀ hθ_pos]
    linarith [show (1 / 100 : ℝ) * (theta S * n) * theta S = (1 / 100 : ℝ) * ((theta S) ^ 2 * n) by ring]
  -- Therefore α ≤ L + 1 / theta S ≤ (1/2) * (theta S * n) = (1/2) * φ(n)!
  have htot_eq : (Nat.totient n : ℝ) = theta S * n := by
    have hQ := congrArg ((↑) : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors n)
    push_cast at hQ
    rw [hQ, mul_comm]; congr 1; simp only [theta, S, one_div]
  have hL_pos : 0 < L := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ S.card := one_le_pow₀ (by norm_num)
    dsimp [L]; nlinarith only [h1, Real.sqrt_nonneg (q : ℝ)]
  have hα_le : (α : ℝ) ≤ (1 / 2 : ℝ) * (Nat.totient n : ℝ) := by
    have h1 : (α : ℝ) * n ≤ (α : ℝ) * (n + L) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg α)
    have h2 : (α : ℝ) * n ≤ n * (L + 1 / theta S) := h1.trans hI
    have h3 : (α : ℝ) ≤ L + 1 / theta S := le_of_mul_le_mul_left (by linarith) hn_pos
    rw [htot_eq]; linarith
  have hk_le : (k : ℝ) ≤ (1 / 2 : ℝ) * (Nat.totient n : ℝ) := by
    have : (k : ℝ) < α := by exact_mod_cast hka
    linarith
  have hsumR : (a : ℝ) + b + k = n := by exact_mod_cast hsum
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hdegR : (Nat.totient n : ℝ) ≤ a + k := by exact_mod_cast hdeg
  have hφ_pos : (0 : ℝ) < Nat.totient n := by rw [htot_eq]; positivity
  have hφ_le_n : (Nat.totient n : ℝ) ≤ n := by exact_mod_cast Nat.totient_le n
  have hφ_hi : (Nat.totient n : ℝ) ≤ (n + k) / 2 := by linarith
  have hnf_ge : (1 / 4 : ℝ) * n ≤ n - Nat.totient n := by linarith
  -- a * b ≥ (φ - k) * (n - φ) ≥ (1/2 * φ) * (1/4 * n) = (1/8) * φ * n!
  have hab_ge : (1 / 8 : ℝ) * (Nat.totient n : ℝ) * n ≤ (a : ℝ) * b := by
    have hid : (a : ℝ) * b - ((Nat.totient n : ℝ) - k) * (n - Nat.totient n) =
        ((a : ℝ) + k - Nat.totient n) * ((b : ℝ) + k - Nat.totient n) := by
      linear_combination ((Nat.totient n : ℝ) - k) * hsumR
    have h1 : 0 ≤ (a : ℝ) + k - Nat.totient n := by linarith
    have h2 : 0 ≤ (b : ℝ) + k - Nat.totient n := by linarith
    have hprod := mul_le_mul (show (1 / 2 : ℝ) * Nat.totient n ≤ Nat.totient n - k by linarith)
      hnf_ge (by positivity) (by linarith)
    linarith [mul_nonneg h1 h2]
  have hcut2 : (a : ℝ) * b * ((n : ℝ) ^ 2 - L ^ 2) ≤ k * n * L ^ 2 := by
    have hid : ((a : ℝ) + k) * ((b : ℝ) + k) = a * b + k * n := by linear_combination k * hsumR
    have hCut' : (n : ℝ) ^ 2 * a * b ≤ L ^ 2 * ((a : ℝ) * b + k * n) := by
      have : L ^ 2 * ((a : ℝ) + k) * ((b : ℝ) + k) = L ^ 2 * (((a : ℝ) + k) * ((b : ℝ) + k)) := by ring
      rw [← hid, ← this]; exact hCut
    linarith [show (n : ℝ) ^ 2 * a * b - L ^ 2 * ((a : ℝ) * b + k * n) =
        (a : ℝ) * b * ((n : ℝ) ^ 2 - L ^ 2) - k * n * L ^ 2 by ring]
  have hL2 : L ^ 2 ≤ (1 / 100 : ℝ) * (n : ℝ) ^ 2 := by
    have h1 : L * L ≤ ((1 / 10 : ℝ) * n) * ((1 / 10 : ℝ) * n) :=
      mul_le_mul hL_le_n hL_le_n hL_pos.le (by positivity)
    linarith [sq L, show ((1 / 10 : ℝ) * n) * ((1 / 10 : ℝ) * n) = (1 / 100 : ℝ) * (n : ℝ) ^ 2 by ring]
  have hlhs : (99 / 800 : ℝ) * (Nat.totient n : ℝ) * (n : ℝ) ^ 3 ≤ (a : ℝ) * b * ((n : ℝ) ^ 2 - L ^ 2) := by
    have h1 : (99 / 100 : ℝ) * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 - L ^ 2 := by linarith
    have h2 := mul_le_mul hab_ge h1 (by positivity) (by positivity)
    linarith [show ((1 / 8 : ℝ) * (Nat.totient n : ℝ) * n) * ((99 / 100 : ℝ) * (n : ℝ) ^ 2) =
        (99 / 800 : ℝ) * (Nat.totient n : ℝ) * (n : ℝ) ^ 3 by ring]
  have hrhs : (k : ℝ) * n * L ^ 2 ≤ (1 / 200 : ℝ) * (Nat.totient n : ℝ) * (n : ℝ) ^ 3 := by
    have hkn : (k : ℝ) * n ≤ ((1 / 2 : ℝ) * Nat.totient n) * n := mul_le_mul_of_nonneg_right hk_le hn_pos.le
    have h2 := mul_le_mul hkn hL2 (sq_nonneg L) (by positivity)
    linarith [show (((1 / 2 : ℝ) * Nat.totient n) * n) * ((1 / 100 : ℝ) * (n : ℝ) ^ 2) =
        (1 / 200 : ℝ) * (Nat.totient n : ℝ) * (n : ℝ) ^ 3 by ring]
  have hφn3 : (0 : ℝ) < (Nat.totient n : ℝ) * (n : ℝ) ^ 3 := mul_pos hφ_pos (pow_pos hn_pos 3)
  linarith

end LargeQ

section SmallOmegaAndRange

open Finset BigOperators

/-- Helper: `1 - 1 / p` is monotone increasing in `p` for `p > 0`. -/
lemma one_sub_inv_le_of_le {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    (1 : ℝ) - 1 / (a : ℝ) ≤ 1 - 1 / (b : ℝ) := by
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have habR : (a : ℝ) ≤ b := Nat.cast_le.mpr hab
  have h1 : 1 / (b : ℝ) ≤ 1 / (a : ℝ) := one_div_le_one_div_of_le haR habR
  linarith

/-- Helper: `theta S = ∏ p ∈ S.sort (· ≤ ·), (1 - 1 / p)`. -/
lemma theta_eq_list_prod (S : Finset ℕ) :
    theta S = ((S.sort (· ≤ ·)).map fun (p : ℕ) => (1 : ℝ) - 1 / (p : ℝ)).prod := by
  unfold theta
  rw [← Finset.prod_map_toList]
  exact ((Finset.sort_perm_toList S (· ≤ ·)).map (fun p : ℕ => (1 : ℝ) - 1 / (p : ℝ))).prod_eq.symm

/-- Unconditional analytic contradiction for ALL `q ≥ 8100` (covers `r = 1..7` and `r ≥ 8`)! -/
lemma analytic_ge_8100
    {q n α k a b : ℕ} (hq : q = n + 1) (hq_ge : 8100 ≤ q)
    (ha1 : 1 ≤ a) (hab : a ≤ b) (hsum : a + b + k = n) (hka : k < α)
    (hdeg : Nat.totient n ≤ a + k)
    (hLower : ∀ (E Sp : Finset ℕ), Disjoint E Sp → E ∪ Sp = n.primeFactors →
      ∀ (_hΔ : 0 < 1 - ∑ p ∈ Sp, (1 : ℝ) / p),
        let Δ : ℝ := 1 - ∑ p ∈ Sp, (1 : ℝ) / p
        let δ : ℝ := theta E * Δ
        let K : ℝ := if Sp = ∅ then (2 : ℝ) ^ E.card - 1
          else (2 : ℝ) ^ E.card * (((Sp.card : ℝ) - 1) / Δ + 2) - 1
        let L : ℝ := K * Real.sqrt q + 1
        (α : ℝ) * (n + L) ≤ n * (L + 1 / δ) ∧
        (n : ℝ) ^ 2 * a * b ≤ L ^ 2 * (a + k) * (b + k)) :
    False := by
  have hn : 8099 ≤ n := by omega
  have hn7 : 7 ≤ n := by omega
  let S := n.primeFactors
  have hS_prime : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have htot_eq : (Nat.totient n : ℝ) = theta S * n := by
    have hQ := congrArg ((↑) : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors n)
    push_cast at hQ
    rw [hQ, mul_comm]; congr 1; simp only [theta, S, one_div]
  have hω_pos : 1 ≤ S.card := by
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    exact Finset.card_pos.mpr ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by omega⟩⟩
  by_cases h8 : 8 ≤ S.card
  · have hL := hLower S ∅ (Finset.disjoint_empty_right S) (Finset.union_empty S) (by simp)
    simp only [Finset.sum_empty, sub_zero, mul_one, ↓reduceIte] at hL
    exact omega_ge_eight_contradiction hq hn7 h8 ha1 hab hsum hka hdeg hL.1 hL.2
  · -- S.card ∈ {1, 2, 3, 4, 5, 6, 7}: extract sorted list `l` of length `S.card`!
    let l := S.sort (· ≤ ·)
    have hl_len : l.length = S.card := Finset.length_sort _
    have hl_mem : ∀ x, x ∈ l ↔ x ∈ S := fun x => Finset.mem_sort _
    have hl_nd : l.Nodup := Finset.sort_nodup _ _
    have hl_sorted : l.Pairwise (· < ·) := by
      have hle := Finset.pairwise_sort S (· ≤ ·)
      rw [List.pairwise_iff_getElem] at hle ⊢
      intro i j hi hj hij
      exact lt_of_le_of_ne (hle i j hi hj hij)
        (fun h => absurd ((List.Nodup.getElem_inj_iff hl_nd).mp h) (Nat.ne_of_lt hij))
    have hpr_l : ∀ p ∈ l, p.Prime := fun p hp => hS_prime p ((hl_mem p).mp hp)
    have hge := sorted_primes_ge hpr_l hl_sorted
    have hrad_le : ∏ p ∈ S, p ≤ n := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)
    have hrad_eq_l : ∏ p ∈ S, p = l.prod := by
      have hperm := Finset.sort_perm_toList S (· ≤ ·)
      rw [← Finset.prod_toList]; exact hperm.prod_eq.symm
    have hθ_eq_l : theta S = (l.map fun (p : ℕ) => (1 : ℝ) - 1 / (p : ℝ)).prod := theta_eq_list_prod S
    -- Split by exact value of S.card ∈ {1, 2, 3, 4, 5, 6, 7}!
    have hcases : S.card = 1 ∨ S.card = 2 ∨ S.card = 3 ∨ S.card = 4 ∨ S.card = 5 ∨ S.card = 6 ∨ S.card = 7 := by
      omega
    -- Helper to apply s = 0 (r = 1, 2, 3, 7)
    have h_s0 : ∀ (n_lo θ_lo K_hi sq_hi u0 c0 a0 : ℝ),
        0 < n_lo → n_lo ≤ n → 0 < θ_lo → θ_lo ≤ 1 / 2 → θ_lo ≤ theta S →
        ((2 : ℝ) ^ S.card - 1) ≤ K_hi → 0 < sq_hi → n_lo + 1 ≤ sq_hi ^ 2 →
        (K_hi * sq_hi + 1) / n_lo ≤ u0 → u0 < 1 →
        1 / (θ_lo * n_lo) ≤ c0 → c0 < 1 →
        (u0 + c0) / (1 + u0) ≤ a0 → a0 < θ_lo →
        a0 * u0 ^ 2 < (θ_lo - a0) * (1 - θ_lo) * (1 - u0 ^ 2) → False := by
      intro n_lo θ_lo K_hi sq_hi u0 c0 a0 hn0 hnge hθ0 hθh hθle hKle hsq0 hsqge hu0 hu1 hc0 hc1 ha0 ha1' hmain
      have hL := hLower S ∅ (Finset.disjoint_empty_right S) (Finset.union_empty S) (by simp)
      simp only [Finset.sum_empty, sub_zero, mul_one, ↓reduceIte] at hL
      have hK_nn : 0 ≤ (2 : ℝ) ^ S.card - 1 := by
        have : (1 : ℝ) ≤ (2 : ℝ) ^ S.card := one_le_pow₀ (by norm_num); linarith
      exact ce_of_const_bounds hq hn7 ha1 hab hsum hka hdeg (theta_pos hS_prime) hK_nn hL.1 hL.2
        hn0 hnge hθ0 hθh (by rw [htot_eq]; exact mul_le_mul_of_nonneg_right hθle (Nat.cast_nonneg n))
        hKle hθle hθ0 hsq0 hsqge hu0 hu1 hc0 hc1 ha0 ha1' hmain
    -- Helper to apply s = r - 2 (r = 4, 5, 6), taking E = {p0, p1} and Sp = S \ E!
    have h_s_from2 : ∀ (p0 p1 : ℕ) (hp0 : p0 ∈ S) (hp1 : p1 ∈ S) (hne : p0 ≠ p1) (hSp_ne : (S \ {p0, p1}).Nonempty)
        (n_lo θ_lo Δ_lo K_hi sq_hi u0 c0 a0 : ℝ),
        0 < n_lo → n_lo ≤ n → 0 < θ_lo → θ_lo ≤ 1 / 2 → θ_lo ≤ theta S →
        0 < Δ_lo → Δ_lo ≤ 1 - ∑ p ∈ (S \ {p0, p1}), (1 : ℝ) / p →
        (1 / 3 : ℝ) ≤ theta {p0, p1} →
        4 * (((((S \ {p0, p1}).card : ℝ) - 1) / Δ_lo) + 2) - 1 ≤ K_hi →
        0 < sq_hi → n_lo + 1 ≤ sq_hi ^ 2 →
        (K_hi * sq_hi + 1) / n_lo ≤ u0 → u0 < 1 →
        1 / ((1 / 3 * Δ_lo) * n_lo) ≤ c0 → c0 < 1 →
        (u0 + c0) / (1 + u0) ≤ a0 → a0 < θ_lo →
        a0 * u0 ^ 2 < (θ_lo - a0) * (1 - θ_lo) * (1 - u0 ^ 2) → False := by
      intro p0 p1 hp0 hp1 hne hSp_ne n_lo θ_lo Δ_lo K_hi sq_hi u0 c0 a0
        hn0 hnge hθ0 hθh hθle hΔ0 hΔle hθE hKle hsq0 hsqge hu0 hu1 hc0 hc1 ha0 ha1' hmain
      let E : Finset ℕ := {p0, p1}
      let Sp : Finset ℕ := S \ E
      have hE_sub : E ⊆ S := by
        intro x hx; simp only [E, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have hE_card : E.card = 2 := Finset.card_pair hne
      have hdisj : Disjoint E Sp := Finset.disjoint_sdiff
      have hES : E ∪ Sp = S := Finset.union_sdiff_of_subset hE_sub
      have hΔ_pos : 0 < 1 - ∑ p ∈ Sp, (1 : ℝ) / p := lt_of_lt_of_le hΔ0 hΔle
      have hL := hLower E Sp hdisj hES hΔ_pos
      let Δ : ℝ := 1 - ∑ p ∈ Sp, (1 : ℝ) / p
      let δ : ℝ := theta E * Δ
      let K : ℝ := if Sp = ∅ then (2 : ℝ) ^ E.card - 1
        else (2 : ℝ) ^ E.card * (((Sp.card : ℝ) - 1) / Δ + 2) - 1
      have hδ_ge : 1 / 3 * Δ_lo ≤ δ := mul_le_mul hθE hΔle hΔ0.le (by linarith)
      have hδ_pos : 0 < δ := lt_of_lt_of_le (by positivity) hδ_ge
      have hK_nn : 0 ≤ K := by
        dsimp [K]; split_ifs with hSp
        · rw [hE_card]; norm_num
        · have h1 : 1 ≤ Sp.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hSp)
          have h1R : (1 : ℝ) ≤ Sp.card := by exact_mod_cast h1
          have h2 : (0 : ℝ) ≤ ((Sp.card : ℝ) - 1) / Δ := div_nonneg (by linarith) hΔ_pos.le
          rw [hE_card]; norm_num; linarith
      have hK_le : K ≤ K_hi := by
        dsimp [K]; split_ifs with hSp
        · exact absurd hSp (Finset.nonempty_iff_ne_empty.mp hSp_ne)
        · have h1 : 1 ≤ Sp.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hSp)
          have h1R : (1 : ℝ) ≤ Sp.card := by exact_mod_cast h1
          have hnum : (0 : ℝ) ≤ (Sp.card : ℝ) - 1 := by linarith
          have hdiv : ((Sp.card : ℝ) - 1) / Δ ≤ ((Sp.card : ℝ) - 1) / Δ_lo :=
            div_le_div_of_nonneg_left hnum hΔ0 hΔle
          rw [hE_card]
          norm_num at hKle ⊢
          linarith
      exact ce_of_const_bounds hq hn7 ha1 hab hsum hka hdeg hδ_pos hK_nn hL.1 hL.2
        hn0 hnge hθ0 hθh (by rw [htot_eq]; exact mul_le_mul_of_nonneg_right hθle (Nat.cast_nonneg n))
        hK_le hδ_ge (by positivity) hsq0 hsqge hu0 hu1 hc0 hc1 ha0 ha1' hmain
    -- Now discharge all 7 values of S.card = 1..7 with tiny 2-digit rounded rationals!
    rcases hcases with hr | hr | hr | hr | hr | hr | hr
    · -- r = 1
      rcases List.length_eq_one_iff.mp (hl_len.trans hr) with ⟨p0, hl_eq⟩
      have hp0 : 2 ≤ p0 := by have h := hge.1 (by omega); simp only [hl_eq] at h; exact h
      have hθ : (1 / 2 : ℝ) ≤ theta S := by
        rw [hθ_eq_l, hl_eq]; simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        have h0 := one_sub_inv_le_of_le (by norm_num) hp0
        linarith [show (1 : ℝ) - 1 / ((2 : ℕ) : ℝ) = 1 / 2 by norm_num]
      exact h_s0 8099 (1/2) 1 90 (1/50) (1/1000) (1/40)
        (by norm_num) (by exact_mod_cast hn) (by norm_num) (by norm_num) hθ
        (by rw [hr]; norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · -- r = 2
      rcases l with _ | ⟨p0, _ | ⟨p1, _ | ⟨_, _⟩⟩⟩ <;> try (simp at hl_len; omega)
      have hp0 : 2 ≤ p0 := hge.1 (by simp)
      have hp1 : 3 ≤ p1 := hge.2.1 (by simp)
      have hθ : (1 / 3 : ℝ) ≤ theta S := by
        rw [hθ_eq_l]; simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        have h0 := one_sub_inv_le_of_le (by norm_num) hp0
        have h1 := one_sub_inv_le_of_le (by norm_num) hp1
        nlinarith only [h0, h1]
      exact h_s0 8099 (1/3) 3 90 (1/20) (1/1000) (1/20)
        (by norm_num) (by exact_mod_cast hn) (by norm_num) (by norm_num) hθ
        (by rw [hr]; norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · -- r = 3
      rcases l with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨_, _⟩⟩⟩⟩ <;> try (simp at hl_len; omega)
      have hp0 : 2 ≤ p0 := hge.1 (by simp)
      have hp1 : 3 ≤ p1 := hge.2.1 (by simp)
      have hp2 : 5 ≤ p2 := hge.2.2.1 (by simp)
      have hθ : (4 / 15 : ℝ) ≤ theta S := by
        rw [hθ_eq_l]; simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        have h0 := one_sub_inv_le_of_le (by norm_num) hp0
        have h1 := one_sub_inv_le_of_le (by norm_num) hp1
        have h2 := one_sub_inv_le_of_le (by norm_num) hp2
        have h12 : (8 / 15 : ℝ) ≤ (1 - 1 / (p1 : ℝ)) * (1 - 1 / (p2 : ℝ)) := by nlinarith only [h1, h2]
        nlinarith only [h0, h12]
      exact h_s0 8099 (4/15) 7 90 (1/10) (1/1000) (1/10)
        (by norm_num) (by exact_mod_cast hn) (by norm_num) (by norm_num) hθ
        (by rw [hr]; norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · -- r = 4
      rcases l with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> try (simp at hl_len; omega)
      have hp0 : 2 ≤ p0 := hge.1 (by simp)
      have hp1 : 3 ≤ p1 := hge.2.1 (by simp)
      have hp2 : 5 ≤ p2 := hge.2.2.1 (by simp)
      have hp3 : 7 ≤ p3 := hge.2.2.2.1 (by simp)
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hl_nd
      have hS_eq : S = {p0, p1, p2, p3} := by ext x; rw [← hl_mem]; simp
      have hSp_eq : S \ {p0, p1} = {p2, p3} := by
        rw [hS_eq]; ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl | rfl | rfl, hnot⟩ <;> simp at hnot ⊢
        · rintro (rfl | rfl) <;> refine ⟨by simp, ?_⟩
          · push Not; exact ⟨Ne.symm hl_nd.1.2.1, Ne.symm hl_nd.2.1.1⟩
          · push Not; exact ⟨Ne.symm hl_nd.1.2.2, Ne.symm hl_nd.2.1.2⟩
      have hθ : (8 / 35 : ℝ) ≤ theta S := by
        rw [hθ_eq_l]; simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        have h0 := one_sub_inv_le_of_le (by norm_num) hp0
        have h1 := one_sub_inv_le_of_le (by norm_num) hp1
        have h2 := one_sub_inv_le_of_le (by norm_num) hp2
        have h3 := one_sub_inv_le_of_le (by norm_num) hp3
        have h23 : (24 / 35 : ℝ) ≤ (1 - 1 / (p2 : ℝ)) * (1 - 1 / (p3 : ℝ)) := by nlinarith only [h2, h3]
        have h123 : (16 / 35 : ℝ) ≤ (1 - 1 / (p1 : ℝ)) * ((1 - 1 / (p2 : ℝ)) * (1 - 1 / (p3 : ℝ))) := by nlinarith only [h1, h23]
        nlinarith only [h0, h123]
      have hθE : (1 / 3 : ℝ) ≤ theta {p0, p1} := by
        rw [theta, Finset.prod_pair hl_nd.1.1]
        have h0 := one_sub_inv_le_of_le (by norm_num) hp0
        have h1 := one_sub_inv_le_of_le (by norm_num) hp1
        nlinarith only [h0, h1]
      have hΔ : (23 / 35 : ℝ) ≤ 1 - ∑ p ∈ S \ {p0, p1}, (1 : ℝ) / p := by
        rw [hSp_eq, Finset.sum_pair hl_nd.2.2.1]
        have h2 : (1 : ℝ) / p2 ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp2)
        have h3 : (1 : ℝ) / p3 ≤ 1 / 7 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp3)
        linarith
      have hSp_card : (S \ {p0, p1}).card = 2 := by rw [hSp_eq, Finset.card_pair hl_nd.2.2.1]
      exact h_s_from2 p0 p1 ((hl_mem _).mp (by simp)) ((hl_mem _).mp (by simp)) hl_nd.1.1 (Finset.card_pos.mp (by omega))
        8099 (8/35) (23/35) (301/23) 90 (15/100) (1/1500) (14/100)
        (by norm_num) (by exact_mod_cast hn) (by norm_num) (by norm_num) hθ
        (by norm_num) hΔ hθE (by rw [hSp_card]; norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · -- r = 5
      rcases l with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;> try (simp at hl_len; omega)
      have hp0 : 2 ≤ p0 := hge.1 (by simp)
      have hp1 : 3 ≤ p1 := hge.2.1 (by simp)
      have hp2 : 5 ≤ p2 := hge.2.2.1 (by simp)
      have hp3 : 7 ≤ p3 := hge.2.2.2.1 (by simp)
      have hp4 : 11 ≤ p4 := hge.2.2.2.2.1 (by simp)
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hl_nd
      have hS_eq : S = {p0, p1, p2, p3, p4} := by ext x; rw [← hl_mem]; simp
      have hSp_eq : S \ {p0, p1} = {p2, p3, p4} := by
        rw [hS_eq]; ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl | rfl | rfl | rfl, hnot⟩ <;> simp at hnot ⊢
        · rintro (rfl | rfl | rfl) <;> refine ⟨by simp, ?_⟩
          · push Not; exact ⟨Ne.symm hl_nd.1.2.1, Ne.symm hl_nd.2.1.1⟩
          · push Not; exact ⟨Ne.symm hl_nd.1.2.2.1, Ne.symm hl_nd.2.1.2.1⟩
          · push Not; exact ⟨Ne.symm hl_nd.1.2.2.2, Ne.symm hl_nd.2.1.2.2⟩
      have hθ : (16 / 77 : ℝ) ≤ theta S := by
        rw [hθ_eq_l]; simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        have h0 := one_sub_inv_le_of_le (by norm_num) hp0
        have h1 := one_sub_inv_le_of_le (by norm_num) hp1
        have h2 := one_sub_inv_le_of_le (by norm_num) hp2
        have h3 := one_sub_inv_le_of_le (by norm_num) hp3
        have h4 := one_sub_inv_le_of_le (by norm_num) hp4
        have h34 : (60 / 77 : ℝ) ≤ (1 - 1 / (p3 : ℝ)) * (1 - 1 / (p4 : ℝ)) := by nlinarith only [h3, h4]
        have h234 : (48 / 77 : ℝ) ≤ (1 - 1 / (p2 : ℝ)) * ((1 - 1 / (p3 : ℝ)) * (1 - 1 / (p4 : ℝ))) := by nlinarith only [h2, h34]
        have h1234 : (32 / 77 : ℝ) ≤ (1 - 1 / (p1 : ℝ)) * ((1 - 1 / (p2 : ℝ)) * ((1 - 1 / (p3 : ℝ)) * (1 - 1 / (p4 : ℝ)))) := by nlinarith only [h1, h234]
        nlinarith only [h0, h1234]
      have hθE : (1 / 3 : ℝ) ≤ theta {p0, p1} := by
        rw [theta, Finset.prod_pair hl_nd.1.1]
        have h0 := one_sub_inv_le_of_le (by norm_num) hp0
        have h1 := one_sub_inv_le_of_le (by norm_num) hp1
        nlinarith only [h0, h1]
      have hΔ : (218 / 385 : ℝ) ≤ 1 - ∑ p ∈ S \ {p0, p1}, (1 : ℝ) / p := by
        rw [hSp_eq, Finset.sum_insert (by simp [hl_nd.2.2.1.1, hl_nd.2.2.1.2]), Finset.sum_pair hl_nd.2.2.2.1]
        have h2 : (1 : ℝ) / p2 ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp2)
        have h3 : (1 : ℝ) / p3 ≤ 1 / 7 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp3)
        have h4 : (1 : ℝ) / p4 ≤ 1 / 11 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp4)
        linarith
      have hSp_card : (S \ {p0, p1}).card = 3 := by
        rw [hSp_eq, Finset.card_insert_of_notMem (by simp [hl_nd.2.2.1.1, hl_nd.2.2.1.2]), Finset.card_pair hl_nd.2.2.2.1]
      exact h_s_from2 p0 p1 ((hl_mem _).mp (by simp)) ((hl_mem _).mp (by simp)) hl_nd.1.1 (Finset.card_pos.mp (by omega))
        8099 (16/77) (218/385) (4606/218) 90 (235/1000) (1/1500) (191/1000)
        (by norm_num) (by exact_mod_cast hn) (by norm_num) (by norm_num) hθ
        (by norm_num) hΔ hθE (by rw [hSp_card]; norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · -- r = 6
      rcases l with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, _ | ⟨p5, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩ <;> try (simp at hl_len; omega)
      have hp0 : 2 ≤ p0 := hge.1 (by simp)
      have hp1 : 3 ≤ p1 := hge.2.1 (by simp)
      have hp2 : 5 ≤ p2 := hge.2.2.1 (by simp)
      have hp3 : 7 ≤ p3 := hge.2.2.2.1 (by simp)
      have hp4 : 11 ≤ p4 := hge.2.2.2.2.1 (by simp)
      have hp5 : 13 ≤ p5 := hge.2.2.2.2.2.1 (by simp)
      have hn30030 : 30030 ≤ n := by
        have h45 : 143 ≤ p4 * p5 := Nat.mul_le_mul hp4 hp5
        have h35 : 1001 ≤ p3 * (p4 * p5) := Nat.mul_le_mul hp3 h45
        have h25 : 5005 ≤ p2 * (p3 * (p4 * p5)) := Nat.mul_le_mul hp2 h35
        have h15 : 15015 ≤ p1 * (p2 * (p3 * (p4 * p5))) := Nat.mul_le_mul hp1 h25
        have hprod : 30030 ≤ p0 * (p1 * (p2 * (p3 * (p4 * p5)))) := Nat.mul_le_mul hp0 h15
        have heq : p0 * (p1 * (p2 * (p3 * (p4 * p5)))) = [p0, p1, p2, p3, p4, p5].prod := by simp
        omega
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hl_nd
      have hS_eq : S = {p0, p1, p2, p3, p4, p5} := by ext x; rw [← hl_mem]; simp
      have hSp_eq : S \ {p0, p1} = {p2, p3, p4, p5} := by
        rw [hS_eq]; ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl | rfl | rfl | rfl | rfl, hnot⟩ <;> simp at hnot ⊢
        · rintro (rfl | rfl | rfl | rfl) <;> refine ⟨by simp, ?_⟩
          · push Not; exact ⟨Ne.symm hl_nd.1.2.1, Ne.symm hl_nd.2.1.1⟩
          · push Not; exact ⟨Ne.symm hl_nd.1.2.2.1, Ne.symm hl_nd.2.1.2.1⟩
          · push Not; exact ⟨Ne.symm hl_nd.1.2.2.2.1, Ne.symm hl_nd.2.1.2.2.1⟩
          · push Not; exact ⟨Ne.symm hl_nd.1.2.2.2.2, Ne.symm hl_nd.2.1.2.2.2⟩
      have hθ : (192 / 1001 : ℝ) ≤ theta S := by
        rw [hθ_eq_l]; simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        have h0 := one_sub_inv_le_of_le (by norm_num) hp0
        have h1 := one_sub_inv_le_of_le (by norm_num) hp1
        have h2 := one_sub_inv_le_of_le (by norm_num) hp2
        have h3 := one_sub_inv_le_of_le (by norm_num) hp3
        have h4 := one_sub_inv_le_of_le (by norm_num) hp4
        have h5 := one_sub_inv_le_of_le (by norm_num) hp5
        have h45 : (120 / 143 : ℝ) ≤ (1 - 1 / (p4 : ℝ)) * (1 - 1 / (p5 : ℝ)) := by nlinarith only [h4, h5]
        have h35 : (720 / 1001 : ℝ) ≤ (1 - 1 / (p3 : ℝ)) * ((1 - 1 / (p4 : ℝ)) * (1 - 1 / (p5 : ℝ))) := by nlinarith only [h3, h45]
        have h25 : (576 / 1001 : ℝ) ≤ (1 - 1 / (p2 : ℝ)) * ((1 - 1 / (p3 : ℝ)) * ((1 - 1 / (p4 : ℝ)) * (1 - 1 / (p5 : ℝ)))) := by nlinarith only [h2, h35]
        have h15 : (384 / 1001 : ℝ) ≤ (1 - 1 / (p1 : ℝ)) * ((1 - 1 / (p2 : ℝ)) * ((1 - 1 / (p3 : ℝ)) * ((1 - 1 / (p4 : ℝ)) * (1 - 1 / (p5 : ℝ))))) := by nlinarith only [h1, h25]
        nlinarith only [h0, h15]
      have hθE : (1 / 3 : ℝ) ≤ theta {p0, p1} := by
        rw [theta, Finset.prod_pair hl_nd.1.1]
        have h0 := one_sub_inv_le_of_le (by norm_num) hp0
        have h1 := one_sub_inv_le_of_le (by norm_num) hp1
        nlinarith only [h0, h1]
      have hΔ : (2449 / 5005 : ℝ) ≤ 1 - ∑ p ∈ S \ {p0, p1}, (1 : ℝ) / p := by
        rw [hSp_eq,
          Finset.sum_insert (by simp [hl_nd.2.2.1.1, hl_nd.2.2.1.2.1, hl_nd.2.2.1.2.2]),
          Finset.sum_insert (by simp [hl_nd.2.2.2.1.1, hl_nd.2.2.2.1.2]),
          Finset.sum_pair hl_nd.2.2.2.2.1]
        have h2 : (1 : ℝ) / p2 ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp2)
        have h3 : (1 : ℝ) / p3 ≤ 1 / 7 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp3)
        have h4 : (1 : ℝ) / p4 ≤ 1 / 11 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp4)
        have h5 : (1 : ℝ) / p5 ≤ 1 / 13 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp5)
        linarith
      have hSp_card : (S \ {p0, p1}).card = 4 := by
        rw [hSp_eq,
          Finset.card_insert_of_notMem (by simp [hl_nd.2.2.1.1, hl_nd.2.2.1.2.1, hl_nd.2.2.1.2.2]),
          Finset.card_insert_of_notMem (by simp [hl_nd.2.2.2.1.1, hl_nd.2.2.2.1.2]),
          Finset.card_pair hl_nd.2.2.2.2.1]
      exact h_s_from2 p0 p1 ((hl_mem _).mp (by simp)) ((hl_mem _).mp (by simp)) hl_nd.1.1 (Finset.card_pos.mp (by omega))
        30030 (192/1001) (2449/5005) (77203/2449) 174 (19/100) (1/4000) (16/100)
        (by norm_num) (by exact_mod_cast hn30030) (by norm_num) (by norm_num) hθ
        (by norm_num) hΔ hθE (by rw [hSp_card]; norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · -- r = 7
      rcases l with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, _ | ⟨p5, _ | ⟨p6, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩ <;> try (simp at hl_len; omega)
      have hp0 : 2 ≤ p0 := hge.1 (by simp)
      have hp1 : 3 ≤ p1 := hge.2.1 (by simp)
      have hp2 : 5 ≤ p2 := hge.2.2.1 (by simp)
      have hp3 : 7 ≤ p3 := hge.2.2.2.1 (by simp)
      have hp4 : 11 ≤ p4 := hge.2.2.2.2.1 (by simp)
      have hp5 : 13 ≤ p5 := hge.2.2.2.2.2.1 (by simp)
      have hp6 : 17 ≤ p6 := hge.2.2.2.2.2.2.1 (by simp)
      have hn510510 : 510510 ≤ n := by
        have h56 : 221 ≤ p5 * p6 := Nat.mul_le_mul hp5 hp6
        have h46 : 2431 ≤ p4 * (p5 * p6) := Nat.mul_le_mul hp4 h56
        have h36 : 17017 ≤ p3 * (p4 * (p5 * p6)) := Nat.mul_le_mul hp3 h46
        have h26 : 85085 ≤ p2 * (p3 * (p4 * (p5 * p6))) := Nat.mul_le_mul hp2 h36
        have h16 : 255255 ≤ p1 * (p2 * (p3 * (p4 * (p5 * p6)))) := Nat.mul_le_mul hp1 h26
        have hprod : 510510 ≤ p0 * (p1 * (p2 * (p3 * (p4 * (p5 * p6))))) := Nat.mul_le_mul hp0 h16
        have heq : p0 * (p1 * (p2 * (p3 * (p4 * (p5 * p6))))) = [p0, p1, p2, p3, p4, p5, p6].prod := by simp
        omega
      have hθ : (3072 / 17017 : ℝ) ≤ theta S := by
        rw [hθ_eq_l]; simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        have h0 := one_sub_inv_le_of_le (by norm_num) hp0
        have h1 := one_sub_inv_le_of_le (by norm_num) hp1
        have h2 := one_sub_inv_le_of_le (by norm_num) hp2
        have h3 := one_sub_inv_le_of_le (by norm_num) hp3
        have h4 := one_sub_inv_le_of_le (by norm_num) hp4
        have h5 := one_sub_inv_le_of_le (by norm_num) hp5
        have h6 := one_sub_inv_le_of_le (by norm_num) hp6
        have h56 : (192 / 221 : ℝ) ≤ (1 - 1 / (p5 : ℝ)) * (1 - 1 / (p6 : ℝ)) := by nlinarith only [h5, h6]
        have h46 : (1920 / 2431 : ℝ) ≤ (1 - 1 / (p4 : ℝ)) * ((1 - 1 / (p5 : ℝ)) * (1 - 1 / (p6 : ℝ))) := by nlinarith only [h4, h56]
        have h36 : (11520 / 17017 : ℝ) ≤ (1 - 1 / (p3 : ℝ)) * ((1 - 1 / (p4 : ℝ)) * ((1 - 1 / (p5 : ℝ)) * (1 - 1 / (p6 : ℝ)))) := by nlinarith only [h3, h46]
        have h26 : (9216 / 17017 : ℝ) ≤ (1 - 1 / (p2 : ℝ)) * ((1 - 1 / (p3 : ℝ)) * ((1 - 1 / (p4 : ℝ)) * ((1 - 1 / (p5 : ℝ)) * (1 - 1 / (p6 : ℝ))))) := by nlinarith only [h2, h36]
        have h16 : (6144 / 17017 : ℝ) ≤ (1 - 1 / (p1 : ℝ)) * ((1 - 1 / (p2 : ℝ)) * ((1 - 1 / (p3 : ℝ)) * ((1 - 1 / (p4 : ℝ)) * ((1 - 1 / (p5 : ℝ)) * (1 - 1 / (p6 : ℝ)))))) := by nlinarith only [h1, h26]
        nlinarith only [h0, h16]
      exact h_s0 510510 (3072/17017) 127 715 (18/100) (1/90000) (153/1000)
        (by norm_num) (by exact_mod_cast hn510510) (by norm_num) (by norm_num) hθ
        (by rw [hr]; norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end SmallOmegaAndRange

section RangeChecker
def isPrimeAux (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, d =>
    if d * d > n then true
    else if n % d == 0 then false
    else isPrimeAux n fuel (d + 1)

def isPrimeBool (n : ℕ) : Bool :=
  2 ≤ n && isPrimeAux n n 2

lemma isPrimeAux_sound (n : ℕ) : ∀ fuel d, 2 ≤ d →
    (∀ k, 2 ≤ k → k < d → ¬ k ∣ n) →
    isPrimeAux n fuel d = true → ∀ k, 2 ≤ k → k * k ≤ n → ¬ k ∣ n
  | 0, _, _, _, h => by simp [isPrimeAux] at h
  | fuel + 1, d, hd2, hprev, h => by
    unfold isPrimeAux at h
    by_cases hgt : d * d > n
    · intro k hk2 hksq
      exact hprev k hk2 (by nlinarith)
    · rw [if_neg hgt] at h
      by_cases hdiv : n % d = 0
      · simp [hdiv] at h
      · have hbeq : (n % d == 0) = false := beq_false_of_ne hdiv
        rw [hbeq] at h; dsimp at h
        apply isPrimeAux_sound n fuel (d + 1) (by omega) _ h
        intro k hk2 hklt
        by_cases hkd : k < d
        · exact hprev k hk2 hkd
        · have heq : k = d := by omega
          subst heq
          intro hdvd; exact hdiv (Nat.dvd_iff_mod_eq_zero.mp hdvd)

lemma isPrimeBool_sound {n : ℕ} (h : isPrimeBool n = true) : n.Prime := by
  unfold isPrimeBool at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hnodiv := isPrimeAux_sound n n 2 le_rfl (fun k hk1 hk2 => by omega) h.2
  rw [Nat.prime_def_lt']
  refine ⟨h.1, fun m hm2 hmlt hdvd => ?_⟩
  by_cases hsq : m * m ≤ n
  · exact hnodiv m hm2 hsq hdvd
  · obtain ⟨q, hq⟩ := hdvd
    have hq2 : 2 ≤ q := by nlinarith
    have hqsq : q * q ≤ n := by nlinarith
    exact hnodiv q hq2 hqsq ⟨m, by linarith⟩

def stripPowAux (p : ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | fuel + 1, n => if n % p == 0 then stripPowAux p fuel (n / p) else n

def stripPow (n p : ℕ) : ℕ := stripPowAux p 16 n

lemma stripPowAux_pow_eq_one {p : ℕ} (hp : 2 ≤ p) : ∀ fuel k, k ≤ fuel → stripPowAux p fuel (p ^ k) = 1
  | fuel, 0, _ => by
    cases fuel with
    | zero => rfl
    | succ f =>
      unfold stripPowAux
      have : 1 % p ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
      simp [this]
  | 0, k + 1, hk => by omega
  | fuel + 1, k + 1, hk => by
    unfold stripPowAux
    have hmod : p ^ (k + 1) % p = 0 := by rw [pow_succ]; simp
    have hdiv : p ^ (k + 1) / p = p ^ k := by rw [pow_succ, Nat.mul_div_cancel _ (by omega)]
    simp only [hmod, beq_self_eq_true, ↓reduceIte, hdiv]
    exact stripPowAux_pow_eq_one hp fuel k (by omega)

def firstPrimeDivAux (q : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => q
  | fuel + 1, d =>
    if d * d > q then q
    else if q % d == 0 then d
    else firstPrimeDivAux q fuel (d + 1)

def firstPrimeDiv (q : ℕ) : ℕ := firstPrimeDivAux q q 2

lemma not_prime_pow_of_stripPow {q d : ℕ} (hq : q < 8100) (hd : d.Prime) (hdvd : d ∣ q)
    (hne : stripPow q d ≠ 1) : ¬ ∃ p e : ℕ, p.Prime ∧ 0 < e ∧ q = p ^ e := by
  rintro ⟨p, e, hp, he, rfl⟩
  have hdp : d = p := (Nat.prime_dvd_prime_iff_eq hd hp).mp (hd.dvd_of_dvd_pow hdvd)
  subst hdp
  have he16 : e ≤ 16 := by
    by_contra hgt
    have h17 : 17 ≤ e := by omega
    have h2 : 2 ^ 17 ≤ d ^ e := le_trans (Nat.pow_le_pow_right (by norm_num) h17)
      (Nat.pow_le_pow_left hd.two_le e)
    omega
  exact hne (stripPowAux_pow_eq_one hd.two_le 16 e he16)

def isSortedLt : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (a < b) && isSortedLt (b :: rest)

def stripAll : ℕ → List ℕ → ℕ
  | n, [] => n
  | n, p :: ps => stripAll (stripPow n p) ps

def validPrimeFactors (n : ℕ) (ps : List ℕ) : Bool :=
  isSortedLt ps && ps.all (fun p => isPrimeBool p && (n % p == 0)) && (stripAll n ps == 1)

def findPrimeFactorsAux : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | fuel + 1, n, d =>
    if n ≤ 1 then []
    else if d * d > n then [n]
    else if n % d == 0 then d :: findPrimeFactorsAux fuel (stripPow n d) (d + 1)
    else findPrimeFactorsAux fuel n (d + 1)

def findPrimeFactors (n : ℕ) : List ℕ := findPrimeFactorsAux n n 2

def listProd : List ℕ → ℕ
  | [] => 1
  | x :: xs => x * listProd xs

def listPhiProd : List ℕ → ℕ
  | [] => 1
  | x :: xs => (x - 1) * listPhiProd xs

def sumRecipNum (P : ℕ) : List ℕ → ℕ
  | [] => 0
  | p :: ps => P / p + sumRecipNum P ps

def lowerSieveParams (n sq16 : ℕ) (e_ps s_ps : List ℕ) : Bool × ℕ × ℕ × ℕ :=
  let P_e := listProd e_ps
  let phi_e := listPhiProd e_ps
  let P_s := listProd s_ps
  let s_sum := sumRecipNum P_s s_ps
  if P_s ≤ s_sum then (false, 0, 1, n)
  else
    let D_num := P_s - s_sum
    let W_e := 1 <<< e_ps.length
    let s := s_ps.length
    let K_num := if s == 0 then W_e - 1 else W_e * ((s - 1) * P_s + 2 * D_num) - D_num
    let K_den := if s == 0 then 1 else D_num
    let L_num := K_num * sq16 + 16 * K_den
    let L_den := 16 * K_den
    let g := Nat.gcd L_num L_den
    let Ln := L_num / g
    let Ld := L_den / g
    let num := n * Ln * phi_e * D_num + n * Ld * P_e * P_s
    let den := (n * Ld + Ln) * phi_e * D_num
    (true, Ln, Ld, num / den)

def upperAlphaUb (n phi sq16 : ℕ) (e_ps : List ℕ) : ℕ :=
  let P_e := listProd e_ps
  let phi_e := listPhiProd e_ps
  let Le_num := ((1 <<< e_ps.length) - 1) * sq16 + 16
  let Le_den := 16
  let lhs := (phi - 1) * P_e * n * Le_den
  let den := phi_e * (n * Le_den + Le_num)
  if den == 0 then n
  else
    let min_na := (lhs + den - 1) / den
    if min_na ≤ n then n - min_na else 0

def upperKillsA (n phi sq16 k_max a : ℕ) (e_ps : List ℕ) : Bool :=
  let P_e := listProd e_ps
  let phi_e := listPhiProd e_ps
  let Le_num := ((1 <<< e_ps.length) - 1) * sq16 + 16
  let Le_den := 16
  let M := a + k_max
  let lhs0 := n * P_e * (phi - 1)
  let rhs0 := n * phi_e * M
  if lhs0 ≤ rhs0 then false
  else
    let rem := lhs0 - rhs0
    (rem * Le_den) * (rem * Le_den) * a > (phi_e * Le_num) * (phi_e * Le_num) * (n - phi) * M * (n - a)

def upperKillsA_any (n phi sq16 k_max a : ℕ) (ps : List ℕ) : ℕ → Bool
  | 0 => false
  | t + 1 => upperKillsA n phi sq16 k_max a (ps.take (t + 1)) || upperKillsA_any n phi sq16 k_max a ps t

def checkRangeUpper (n phi sq16 k_max : ℕ) (ps : List ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | rem + 1, a => upperKillsA_any n phi sq16 k_max a ps ps.length && checkRangeUpper n phi sq16 k_max ps rem (a + 1)

def lowerCutHolds (n Ln Ld k_max a : ℕ) : Bool :=
  let b := n - k_max - a
  (Ln < n * Ld) && (n * n * a * b * Ld * Ld > Ln * Ln * (a + k_max) * (b + k_max))

def findACutAux (n Ln Ld k_max a_lim : ℕ) : ℕ → ℕ → ℕ
  | 0, a => a
  | fuel + 1, a =>
    if a > a_lim then a
    else if lowerCutHolds n Ln Ld k_max a then a
    else findACutAux n Ln Ld k_max a_lim fuel (a + 1)

def loopLowerAux (n sq16 : ℕ) (ps : List ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ
  | 0, bestA, bestLn, bestLd => (bestA, bestLn, bestLd)
  | rem + 1, bestA, bestLn, bestLd =>
    let r := ps.length
    let s := r - rem
    let (ok, Ln, Ld, aub) := lowerSieveParams n sq16 (ps.take (r - s)) (ps.drop (r - s))
    if ok then
      let bestA' := min bestA aub
      let (bestLn', bestLd') := if Ln * bestLd < bestLn * Ld then (Ln, Ld) else (bestLn, bestLd)
      loopLowerAux n sq16 ps rem bestA' bestLn' bestLd'
    else loopLowerAux n sq16 ps rem bestA bestLn bestLd

def loopUpperAlphaAux (n phi sq16 : ℕ) (ps : List ℕ) : ℕ → ℕ → ℕ
  | 0, bestA => bestA
  | t + 1, bestA => loopUpperAlphaAux n phi sq16 ps t (min bestA (upperAlphaUb n phi sq16 (ps.take (t + 1))))

def checkAnalyticQ (q : ℕ) : Bool :=
  let n := q - 1
  let ps := findPrimeFactors n
  if !validPrimeFactors n ps then false
  else
    let phi := ps.foldl (fun acc p => acc / p * (p - 1)) n
    let sq16 := Nat.sqrt (256 * q - 1) + 1
    if 256 * q > sq16 * sq16 then false
    else
      let r := ps.length
      let (bestA0, bestLn, bestLd) := loopLowerAux n sq16 ps (r + 1) n (n + 1) 1
      let bestA := loopUpperAlphaAux n phi sq16 ps r bestA0
      if bestA == 0 then true
      else
        let k_max := bestA - 1
        if 2 * phi > n + k_max then true
        else
          let a_lo := if phi > k_max then phi - k_max else 1
          let a_hi := n / 2
          if a_lo > a_hi then true
          else if lowerCutHolds n bestLn bestLd k_max a_lo then true
          else
            let a_lim := (n - k_max) / 2
            let a_cut := findACutAux n bestLn bestLd k_max a_lim (a_lim - a_lo + 1) a_lo
            if lowerCutHolds n bestLn bestLd k_max a_cut then
              checkRangeUpper n phi sq16 k_max ps (a_cut - a_lo) a_lo
            else
              checkRangeUpper n phi sq16 k_max ps (a_hi - a_lo + 1) a_lo

def except44 : List ℕ :=
  [9, 11, 13, 16, 19, 23, 25, 27, 29, 31, 37, 41, 43, 49, 61, 67, 71, 79, 103,
   121, 127, 151, 169, 181, 211, 241, 271, 331, 361, 421, 463, 547, 571,
   631, 661, 841, 991, 1051, 1471, 1681, 2311, 2731, 3571, 4621]

def checkOneQ (q : ℕ) : Bool :=
  let d := firstPrimeDiv q
  if isPrimeBool d && (q % d == 0) && (stripPow q d != 1) then true
  else if except44.contains q then true
  else checkAnalyticQ q

def checkAllBelow8100 : ℕ → ℕ → Bool
  | 0, _ => true
  | rem + 1, q => checkOneQ q && checkAllBelow8100 rem (q + 1)

end RangeChecker

section RangeCheckerSoundness

lemma dvd_stripPowAux_of_prime {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : r ≠ p) :
    ∀ fuel n, r ∣ n → r ∣ stripPowAux p fuel n
  | 0, _, h => h
  | fuel + 1, n, h => by
    unfold stripPowAux
    split_ifs with hd
    · apply dvd_stripPowAux_of_prime hp hr hne fuel (n / p)
      have hpdvd : p ∣ n := Nat.dvd_of_mod_eq_zero (by simpa using hd)
      have hmul : r ∣ p * (n / p) := by rwa [Nat.mul_div_cancel' hpdvd]
      rcases hr.dvd_mul.mp hmul with hrp | hrdiv
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hr hp).mp hrp) hne
      · exact hrdiv
    · exact h

lemma isSortedLt_pairwise : ∀ l : List ℕ, isSortedLt l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    unfold isSortedLt at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have hrec := isSortedLt_pairwise (b :: rest) h.2
    rw [List.pairwise_cons] at hrec ⊢
    refine ⟨fun x hx => ?_, List.pairwise_cons.mpr hrec⟩
    rcases List.mem_cons.mp hx with rfl | hxr
    · exact h.1
    · exact lt_trans h.1 (hrec.1 x hxr)

lemma stripAll_ne_zero_of_eq_one {n : ℕ} {ps : List ℕ} (h : stripAll n ps = 1) : n ≠ 0 := by
  intro hn0; subst hn0
  have h0 : ∀ l : List ℕ, stripAll 0 l = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons p t ih =>
      unfold stripAll
      have hsp : ∀ fuel, stripPowAux p fuel 0 = 0 := by
        intro fuel; induction fuel with
        | zero => rfl
        | succ f ihf => simp [stripPowAux, ihf]
      rw [show stripPow 0 p = 0 from hsp 16, ih]
  rw [h0] at h; omega

lemma validPrimeFactors_sound {n : ℕ} {ps : List ℕ} (h : validPrimeFactors n ps = true) :
    ps.Pairwise (· < ·) ∧ ps.Nodup ∧ ps.toFinset = n.primeFactors := by
  unfold validPrimeFactors at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hsort, hall⟩, hstrip⟩ := h
  have hpw : ps.Pairwise (· < ·) := isSortedLt_pairwise ps hsort
  have hnd : ps.Nodup := hpw.imp Nat.ne_of_lt
  have hn0 : n ≠ 0 := stripAll_ne_zero_of_eq_one hstrip
  have hmem_pr : ∀ p ∈ ps, p.Prime ∧ p ∣ n := by
    intro p hp
    have h1 := List.all_eq_true.mp hall p hp
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    exact ⟨isPrimeBool_sound h1.1, Nat.dvd_of_mod_eq_zero h1.2⟩
  refine ⟨hpw, hnd, ?_⟩
  ext r
  rw [List.mem_toFinset, Nat.mem_primeFactors]
  constructor
  · intro hr; obtain ⟨hpr, hdvd⟩ := hmem_pr r hr; exact ⟨hpr, hdvd, hn0⟩
  · rintro ⟨hr_prime, hr_dvd, _⟩
    by_contra hr_nmem
    have hkeep : ∀ l : List ℕ, ∀ m : ℕ, (∀ p ∈ l, p.Prime) → r ∉ l → r ∣ m → r ∣ stripAll m l := by
      intro l
      induction l with
      | nil => intro m _ _ hm; exact hm
      | cons p t ih =>
        intro m hpr hnotin hm
        unfold stripAll
        have hp_pr := hpr p List.mem_cons_self
        have hr_ne_p : r ≠ p := fun heq => hnotin (heq ▸ List.mem_cons_self)
        apply ih (stripPow m p) (fun x hx => hpr x (List.mem_cons_of_mem p hx))
          (fun hx => hnotin (List.mem_cons_of_mem p hx))
        exact dvd_stripPowAux_of_prime hp_pr hr_prime hr_ne_p 16 m hm
    have h1 : r ∣ stripAll n ps := hkeep ps n (fun p hp => (hmem_pr p hp).1) hr_nmem hr_dvd
    rw [hstrip] at h1
    exact absurd (Nat.dvd_one.mp h1) hr_prime.ne_one

lemma listProd_eq_prod {l : List ℕ} (hnd : l.Nodup) : (listProd l : ℝ) = ∏ p ∈ l.toFinset, (p : ℝ) := by
  induction l with
  | nil => simp [listProd]
  | cons a t ih =>
    obtain ⟨hat, htnd⟩ := List.nodup_cons.mp hnd
    simp only [listProd, Nat.cast_mul, List.toFinset_cons]
    rw [Finset.prod_insert (by simpa using hat), ih htnd]

lemma listPhiProd_eq_prod {l : List ℕ} (hnd : l.Nodup) (hge : ∀ p ∈ l, 1 ≤ p) :
    (listPhiProd l : ℝ) = ∏ p ∈ l.toFinset, ((p : ℝ) - 1) := by
  induction l with
  | nil => simp [listPhiProd]
  | cons a t ih =>
    obtain ⟨hat, htnd⟩ := List.nodup_cons.mp hnd
    have ha1 := hge a List.mem_cons_self
    simp only [listPhiProd, Nat.cast_mul, Nat.cast_sub ha1, Nat.cast_one, List.toFinset_cons]
    rw [Finset.prod_insert (by simpa using hat), ih htnd fun x hx => hge x (List.mem_cons_of_mem a hx)]

lemma theta_eq_listPhiProd_div {l : List ℕ} (hnd : l.Nodup) (hpr : ∀ p ∈ l, p.Prime) :
    theta l.toFinset = (listPhiProd l : ℝ) / (listProd l : ℝ) := by
  rw [listPhiProd_eq_prod hnd (fun p hp => (hpr p hp).one_le), listProd_eq_prod hnd]
  rw [theta, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (hpr p (List.mem_toFinset.mp hp)).pos
  field_simp [hp_pos.ne']

lemma sumRecipNum_eq_mul_sum {l : List ℕ} (hnd : l.Nodup) (hpr : ∀ p ∈ l, p.Prime)
    {P : ℕ} (hdvd : ∀ p ∈ l, p ∣ P) :
    (sumRecipNum P l : ℝ) = (P : ℝ) * ∑ p ∈ l.toFinset, (1 : ℝ) / p := by
  induction l with
  | nil => simp [sumRecipNum]
  | cons a t ih =>
    obtain ⟨hat, htnd⟩ := List.nodup_cons.mp hnd
    have hadvd := hdvd a List.mem_cons_self
    have ha_pos : (0 : ℝ) < a := Nat.cast_pos.mpr (hpr a List.mem_cons_self).pos
    simp only [sumRecipNum, Nat.cast_add, List.toFinset_cons]
    rw [Finset.sum_insert (by simpa using hat), mul_add,
      ih htnd (fun x hx => hpr x (List.mem_cons_of_mem a hx)) (fun x hx => hdvd x (List.mem_cons_of_mem a hx))]
    congr 1
    rw [Nat.cast_div hadvd ha_pos.ne']; ring

lemma listProd_dvd_of_mem : ∀ {l : List ℕ} {p : ℕ}, p ∈ l → p ∣ listProd l
  | [], _, h => by cases h
  | a :: t, p, h => by
    unfold listProd
    rcases List.mem_cons.mp h with rfl | ht
    · exact dvd_mul_right p (listProd t)
    · exact dvd_mul_of_dvd_right (listProd_dvd_of_mem ht) a

lemma foldl_phi_eq_totient {n : ℕ} {ps : List ℕ} (_hn : 0 < n)
    (hnd : ps.Nodup) (hset : ps.toFinset = n.primeFactors) :
    ps.foldl (fun acc p => acc / p * (p - 1)) n = Nat.totient n := by
  have hfold : ∀ (l : List ℕ) (m : ℕ), (∀ p ∈ l, p.Prime) → l.Nodup → listProd l ∣ m →
      l.foldl (fun acc p => acc / p * (p - 1)) m = m / listProd l * listPhiProd l := by
    intro l
    induction l with
    | nil => intro m _ _ _; simp [listProd, listPhiProd]
    | cons a t ih =>
      intro m hpr hnd' hdvd
      obtain ⟨hat, htnd⟩ := List.nodup_cons.mp hnd'
      have ha_pr := hpr a List.mem_cons_self
      have ht_pr : ∀ p ∈ t, p.Prime := fun p hp => hpr p (List.mem_cons_of_mem a hp)
      have ht_dvd_div : listProd t ∣ m / a := by
        obtain ⟨k, hk⟩ := hdvd
        refine ⟨k, ?_⟩
        rw [hk, listProd, mul_assoc, Nat.mul_div_right _ ha_pr.pos]
      have ht_dvd_next : listProd t ∣ m / a * (a - 1) := dvd_mul_of_dvd_left ht_dvd_div (a - 1)
      simp only [List.foldl_cons]
      rw [ih (m / a * (a - 1)) ht_pr htnd ht_dvd_next, listProd, listPhiProd]
      have ht_pos : 0 < listProd t := by
        have : (0 : ℝ) < listProd t := by
          rw [listProd_eq_prod htnd]; exact Finset.prod_pos fun p hp => Nat.cast_pos.mpr (ht_pr p (List.mem_toFinset.mp hp)).pos
        exact_mod_cast this
      have hdiv_eq : (m / a * (a - 1)) / listProd t = (m / (a * listProd t)) * (a - 1) := by
        obtain ⟨q, hq⟩ := ht_dvd_div
        rw [← Nat.div_div_eq_div_mul, hq, mul_assoc, Nat.mul_div_right _ ht_pos, Nat.mul_div_right _ ht_pos]
      rw [hdiv_eq]; ring
  have hpr : ∀ p ∈ ps, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hset ▸ List.mem_toFinset.mpr hp)
  have hprod_eq : listProd ps = ∏ p ∈ n.primeFactors, p := by
    have h1 := listProd_eq_prod hnd
    rw [hset] at h1
    rw [← Nat.cast_prod] at h1
    exact_mod_cast h1
  have hprod_dvd : listProd ps ∣ n := hprod_eq ▸ Nat.prod_primeFactors_dvd n
  rw [hfold ps n hpr hnd hprod_dvd]
  have hR : ((n / listProd ps * listPhiProd ps : ℕ) : ℝ) = (Nat.totient n : ℝ) := by
    have hQ := congrArg ((↑) : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors n)
    push_cast at hQ
    rw [hQ]
    have hpos : (0 : ℝ) < listProd ps := by
      rw [listProd_eq_prod hnd]
      exact Finset.prod_pos fun p hp => Nat.cast_pos.mpr (hpr p (List.mem_toFinset.mp hp)).pos
    rw [Nat.cast_mul, Nat.cast_div hprod_dvd hpos.ne', div_mul_eq_mul_div, mul_div_assoc,
      ← theta_eq_listPhiProd_div hnd hpr, hset]
    simp [theta, one_div]
  exact_mod_cast hR

lemma lowerSieveParams_sound
    {q n α k a b sq16 : ℕ} (_hq : q = n + 1) (hn7 : 7 ≤ n) (hαn : α ≤ n) (hsq : 256 * q ≤ sq16 * sq16)
    {ps : List ℕ} (hnd : ps.Nodup) (hset : ps.toFinset = n.primeFactors)
    {s : ℕ} (_hs : s ≤ ps.length)
    (hLower : ∀ (E Sp : Finset ℕ), Disjoint E Sp → E ∪ Sp = n.primeFactors →
      ∀ (_hΔ : 0 < 1 - ∑ p ∈ Sp, (1 : ℝ) / p),
        let Δ : ℝ := 1 - ∑ p ∈ Sp, (1 : ℝ) / p
        let δ : ℝ := theta E * Δ
        let K : ℝ := if Sp = ∅ then (2 : ℝ) ^ E.card - 1
          else (2 : ℝ) ^ E.card * (((Sp.card : ℝ) - 1) / Δ + 2) - 1
        let L : ℝ := K * Real.sqrt q + 1
        (α : ℝ) * (n + L) ≤ n * (L + 1 / δ) ∧
        (n : ℝ) ^ 2 * a * b ≤ L ^ 2 * (a + k) * (b + k)) :
    let res := lowerSieveParams n sq16 (ps.take (ps.length - s)) (ps.drop (ps.length - s))
    res.1 = true →
      0 < res.2.2.1 ∧
      α ≤ res.2.2.2 ∧
      (n : ℝ) ^ 2 * a * b * (res.2.2.1 : ℝ) ^ 2 ≤ (res.2.1 : ℝ) ^ 2 * (a + k) * (b + k) := by
  intro res hok
  set e_ps := ps.take (ps.length - s)
  set s_ps := ps.drop (ps.length - s)
  have hsplit : e_ps ++ s_ps = ps := List.take_append_drop _ _
  have hnd_app : e_ps.Nodup ∧ s_ps.Nodup ∧ List.Disjoint e_ps s_ps := by
    have h1 := List.nodup_append.mp (hsplit.symm ▸ hnd)
    exact ⟨h1.1, h1.2.1, fun x hxe hxs => h1.2.2 x hxe x hxs rfl⟩
  let E := e_ps.toFinset
  let Sp := s_ps.toFinset
  have hdisj : Disjoint E Sp := by
    rw [Finset.disjoint_left]; intro x hxE hxSp
    exact hnd_app.2.2 (List.mem_toFinset.mp hxE) (List.mem_toFinset.mp hxSp)
  have hES : E ∪ Sp = n.primeFactors := by
    rw [← hset, ← List.toFinset_append, hsplit]
  have he_pr : ∀ p ∈ e_ps, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (hES ▸ Finset.mem_union_left Sp (List.mem_toFinset.mpr hp))
  have hs_pr : ∀ p ∈ s_ps, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (hES ▸ Finset.mem_union_right E (List.mem_toFinset.mpr hp))
  set P_e := listProd e_ps
  set phi_e := listPhiProd e_ps
  set P_s := listProd s_ps
  set s_sum := sumRecipNum P_s s_ps
  by_cases hbad : P_s ≤ s_sum
  · dsimp only [res, lowerSieveParams] at hok
    rw [if_pos hbad] at hok
    simp at hok
  · push Not at hbad
    set D_num := P_s - s_sum
    have hD_pos : 0 < D_num := by omega
    have hPs_pos : 0 < P_s := by
      have : (0 : ℝ) < P_s := by
        rw [listProd_eq_prod hnd_app.2.1]; exact Finset.prod_pos fun p hp => Nat.cast_pos.mpr (hs_pr p (List.mem_toFinset.mp hp)).pos
      exact_mod_cast this
    have hPe_pos : 0 < P_e := by
      have : (0 : ℝ) < P_e := by
        rw [listProd_eq_prod hnd_app.1]; exact Finset.prod_pos fun p hp => Nat.cast_pos.mpr (he_pr p (List.mem_toFinset.mp hp)).pos
      exact_mod_cast this
    have hphie_pos : 0 < phi_e := by
      have : (0 : ℝ) < phi_e := by
        rw [listPhiProd_eq_prod hnd_app.1 (fun p hp => (he_pr p hp).one_le)]
        exact Finset.prod_pos fun p hp => by
          have : (2 : ℝ) ≤ p := by exact_mod_cast (he_pr p (List.mem_toFinset.mp hp)).two_le
          linarith
      exact_mod_cast this
    have hΔ_eq : 1 - ∑ p ∈ Sp, (1 : ℝ) / p = (D_num : ℝ) / (P_s : ℝ) := by
      have hsr := sumRecipNum_eq_mul_sum hnd_app.2.1 hs_pr (fun p hp => listProd_dvd_of_mem hp)
      have hsub : (D_num : ℝ) = (P_s : ℝ) - s_sum := Nat.cast_sub (le_of_lt hbad)
      rw [hsub, hsr]; field_simp [Nat.cast_ne_zero.mpr hPs_pos.ne']
      dsimp only [Sp, P_s]; ring
    have hΔ_pos : 0 < 1 - ∑ p ∈ Sp, (1 : ℝ) / p := by rw [hΔ_eq]; positivity
    have hLow := hLower E Sp hdisj hES hΔ_pos
    set Δ : ℝ := 1 - ∑ p ∈ Sp, (1 : ℝ) / p
    set δ : ℝ := theta E * Δ
    set K : ℝ := if Sp = ∅ then (2 : ℝ) ^ E.card - 1
      else (2 : ℝ) ^ E.card * (((Sp.card : ℝ) - 1) / Δ + 2) - 1
    set L : ℝ := K * Real.sqrt q + 1
    have hE_card : E.card = e_ps.length := List.toFinset_card_of_nodup hnd_app.1
    have hSp_card : Sp.card = s_ps.length := List.toFinset_card_of_nodup hnd_app.2.1
    have hθE : theta E = (phi_e : ℝ) / (P_e : ℝ) := theta_eq_listPhiProd_div hnd_app.1 he_pr
    have hδ_eq : δ = ((phi_e : ℝ) * D_num) / ((P_e : ℝ) * P_s) := by
      dsimp [δ]; rw [hθE, hΔ_eq]; ring
    set W_e := 1 <<< e_ps.length
    set slen := s_ps.length
    set K_num := if slen == 0 then W_e - 1 else W_e * ((slen - 1) * P_s + 2 * D_num) - D_num
    set K_den := if slen == 0 then 1 else D_num
    have hWe_eq : (W_e : ℝ) = (2 : ℝ) ^ E.card := by
      rw [hE_card]; simp [W_e, Nat.shiftLeft_eq]
    have hKden_pos : 0 < K_den := by dsimp [K_den]; split_ifs <;> omega
    have hK_eq : K = (K_num : ℝ) / (K_den : ℝ) := by
      by_cases hsl : slen = 0
      · have hSp0 : Sp = ∅ := Finset.card_eq_zero.mp (hSp_card.trans hsl)
        have hW1 : 1 ≤ W_e := by rw [show W_e = 2 ^ e_ps.length by simp [W_e, Nat.shiftLeft_eq]]; exact Nat.one_le_two_pow
        simp only [K, K_num, K_den, hSp0, hsl, ↓reduceIte, beq_self_eq_true, Nat.cast_one, div_one,
          Nat.cast_sub hW1, hWe_eq]
      · have hSp_ne : Sp ≠ ∅ := fun h => hsl (by rw [← hSp_card, h]; rfl)
        have hsl1 : 1 ≤ slen := by omega
        have hgeD : D_num ≤ W_e * ((slen - 1) * P_s + 2 * D_num) := by
          have hW1 : 1 ≤ W_e := by rw [show W_e = 2 ^ e_ps.length by simp [W_e, Nat.shiftLeft_eq]]; exact Nat.one_le_two_pow
          calc D_num ≤ 1 * (2 * D_num) := by omega
            _ ≤ W_e * ((slen - 1) * P_s + 2 * D_num) := Nat.mul_le_mul hW1 (by omega)
        simp only [K, K_num, K_den, hSp_ne, beq_iff_eq, hsl, ↓reduceIte, hSp_card, hΔ_eq]
        rw [Nat.cast_sub hgeD, Nat.cast_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hsl1,
          Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, hWe_eq]
        field_simp [Nat.cast_ne_zero.mpr hD_pos.ne', Nat.cast_ne_zero.mpr hPs_pos.ne']
    set L_num := K_num * sq16 + 16 * K_den
    set L_den := 16 * K_den
    set g := Nat.gcd L_num L_den
    set Ln := L_num / g
    set Ld := L_den / g
    have hLden_pos : 0 < L_den := by omega
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right L_num hLden_pos
    have hLd_pos : 0 < Ld := Nat.div_pos (Nat.le_of_dvd hLden_pos (Nat.gcd_dvd_right _ _)) hg_pos
    have hL_ratio : (Ln : ℝ) / (Ld : ℝ) = (L_num : ℝ) / (L_den : ℝ) := by
      have hg_ne : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hg_pos.ne'
      rw [Nat.cast_div (Nat.gcd_dvd_left _ _) hg_ne, Nat.cast_div (Nat.gcd_dvd_right _ _) hg_ne,
        div_div_div_cancel_right₀ hg_ne]
    have hsq_le : Real.sqrt (q : ℝ) ≤ (sq16 : ℝ) / 16 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have hcast : (256 : ℝ) * q ≤ (sq16 : ℝ) * sq16 := by exact_mod_cast hsq
      nlinarith only [hcast]
    have hL_le : L ≤ (Ln : ℝ) / (Ld : ℝ) := by
      rw [hL_ratio]
      dsimp [L, L_num, L_den]
      rw [hK_eq]
      have hK_nn : 0 ≤ (K_num : ℝ) / (K_den : ℝ) := by positivity
      have h1 : (K_num : ℝ) / (K_den : ℝ) * Real.sqrt (q : ℝ) + 1 ≤
          (K_num : ℝ) / (K_den : ℝ) * ((sq16 : ℝ) / 16) + 1 := by
        linarith [mul_le_mul_of_nonneg_left hsq_le hK_nn]
      refine h1.trans (le_of_eq ?_)
      push_cast; field_simp [Nat.cast_ne_zero.mpr hKden_pos.ne']
    have hL_nn : 0 ≤ L := by dsimp [L]; rw [hK_eq]; positivity
    have hLd_posR : (0 : ℝ) < Ld := Nat.cast_pos.mpr hLd_pos
    have hn_posR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    dsimp only [res, lowerSieveParams]
    rw [if_neg (not_le.mpr hbad)]
    dsimp only
    refine ⟨hLd_pos, ?_, ?_⟩
    · have hα_ineq : (α : ℝ) * (n + (Ln : ℝ) / (Ld : ℝ)) ≤ n * ((Ln : ℝ) / (Ld : ℝ) + 1 / δ) := by
        have hαnR : (α : ℝ) ≤ n := by exact_mod_cast hαn
        have hdiff : (α : ℝ) * ((Ln : ℝ) / (Ld : ℝ) - L) ≤ n * ((Ln : ℝ) / (Ld : ℝ) - L) :=
          mul_le_mul_of_nonneg_right hαnR (by linarith)
        linarith [hLow.1]
      set num := n * Ln * phi_e * D_num + n * Ld * P_e * P_s
      set den := (n * Ld + Ln) * phi_e * D_num
      have hden_pos : 0 < den := by
        have : 0 < n * Ld + Ln := Nat.add_pos_left (Nat.mul_pos (by omega) hLd_pos) Ln
        exact Nat.mul_pos (Nat.mul_pos this hphie_pos) hD_pos
      have hmul_le : α * den ≤ num := by
        have hR : (α : ℝ) * (den : ℝ) ≤ (num : ℝ) := by
          have hpos_fac : (0 : ℝ) < (Ld : ℝ) * phi_e * D_num := by positivity
          have h1 := mul_le_mul_of_nonneg_right hα_ineq hpos_fac.le
          have hlhs : (α : ℝ) * (n + (Ln : ℝ) / (Ld : ℝ)) * ((Ld : ℝ) * phi_e * D_num) = (α : ℝ) * (den : ℝ) := by
            dsimp [den]; push_cast; field_simp [hLd_posR.ne']
          have hrhs : n * ((Ln : ℝ) / (Ld : ℝ) + 1 / δ) * ((Ld : ℝ) * phi_e * D_num) = (num : ℝ) := by
            rw [hδ_eq]; dsimp [num]; push_cast
            field_simp [hLd_posR.ne', Nat.cast_ne_zero.mpr hphie_pos.ne', Nat.cast_ne_zero.mpr hD_pos.ne']
          linarith
        exact_mod_cast hR
      exact (Nat.le_div_iff_mul_le hden_pos).mpr hmul_le
    · have hcut := hLow.2
      have hsq' : L ^ 2 ≤ ((Ln : ℝ) / (Ld : ℝ)) ^ 2 := by nlinarith only [hL_nn, hL_le]
      have hmul : (n : ℝ) ^ 2 * a * b ≤ ((Ln : ℝ) / (Ld : ℝ)) ^ 2 * (a + k) * (b + k) := by
        have h1 : L ^ 2 * ((a : ℝ) + k) * ((b : ℝ) + k) ≤ ((Ln : ℝ) / (Ld : ℝ)) ^ 2 * ((a : ℝ) + k) * ((b : ℝ) + k) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq' (by positivity)) (by positivity)
        exact hcut.trans h1
      rw [div_pow] at hmul
      have hLd2 : (0 : ℝ) < (Ld : ℝ) ^ 2 := sq_pos_of_pos hLd_posR
      have h2 := mul_le_mul_of_nonneg_right hmul hLd2.le
      have hrhs : (Ln : ℝ) ^ 2 / (Ld : ℝ) ^ 2 * (a + k) * (b + k) * (Ld : ℝ) ^ 2 =
          (Ln : ℝ) ^ 2 * (a + k) * (b + k) := by field_simp [hLd2.ne']
      linarith

end RangeCheckerSoundness

section RangeCheckerFinal

lemma upperAlphaUb_sound
    {q n α sq16 : ℕ} (_hq : q = n + 1) (hn7 : 7 ≤ n) (hαn : α ≤ n) (hsq : 256 * q ≤ sq16 * sq16)
    {ps : List ℕ} (hnd : ps.Nodup) (hset : ps.toFinset = n.primeFactors) (t : ℕ)
    (hUpper : ∀ (E : Finset ℕ), E ⊆ n.primeFactors →
      let Le : ℝ := ((2 : ℝ) ^ E.card - 1) * Real.sqrt q + 1
      ((Nat.totient n - 1 : ℕ) : ℝ) * n ≤ theta E * (n - α) * (n + Le)) :
    α ≤ upperAlphaUb n (Nat.totient n) sq16 (ps.take t) := by
  set e_ps := ps.take t
  have hnd_e : e_ps.Nodup := hnd.sublist (List.take_sublist t ps)
  let E := e_ps.toFinset
  have hE_sub : E ⊆ n.primeFactors := by
    rw [← hset]; intro x hx; exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hx))
  have he_pr : ∀ p ∈ e_ps, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (hE_sub (List.mem_toFinset.mpr hp))
  have hE_card : E.card = e_ps.length := List.toFinset_card_of_nodup hnd_e
  have hU := hUpper E hE_sub
  set P_e := listProd e_ps
  set phi_e := listPhiProd e_ps
  have hPe_pos : 0 < P_e := by
    have : (0 : ℝ) < P_e := by
      rw [listProd_eq_prod hnd_e]; exact Finset.prod_pos fun p hp => Nat.cast_pos.mpr (he_pr p (List.mem_toFinset.mp hp)).pos
    exact_mod_cast this
  have hphie_pos : 0 < phi_e := by
    have : (0 : ℝ) < phi_e := by
      rw [listPhiProd_eq_prod hnd_e (fun p hp => (he_pr p hp).one_le)]
      exact Finset.prod_pos fun p hp => by
        have : (2 : ℝ) ≤ p := by exact_mod_cast (he_pr p (List.mem_toFinset.mp hp)).two_le
        linarith
    exact_mod_cast this
  set Le_num := ((1 <<< e_ps.length) - 1) * sq16 + 16
  have hLe_le : ((2 : ℝ) ^ E.card - 1) * Real.sqrt q + 1 ≤ (Le_num : ℝ) / 16 := by
    have hsq_le : Real.sqrt (q : ℝ) ≤ (sq16 : ℝ) / 16 := by
      rw [Real.sqrt_le_iff]; refine ⟨by positivity, ?_⟩
      have hcast : (256 : ℝ) * q ≤ (sq16 : ℝ) * sq16 := by exact_mod_cast hsq
      nlinarith only [hcast]
    have hW1 : 1 ≤ 1 <<< e_ps.length := by rw [Nat.shiftLeft_eq, one_mul]; exact Nat.one_le_two_pow
    have hWe : ((1 <<< e_ps.length - 1 : ℕ) : ℝ) = (2 : ℝ) ^ E.card - 1 := by
      rw [Nat.cast_sub hW1, Nat.cast_one, hE_card]; simp [Nat.shiftLeft_eq]
    have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ E.card - 1 := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ E.card := one_le_pow₀ (by norm_num); linarith
    dsimp [Le_num]; push_cast; rw [hWe]
    have h1 := mul_le_mul_of_nonneg_left hsq_le hnn
    linarith
  have hθE : theta E = (phi_e : ℝ) / (P_e : ℝ) := theta_eq_listPhiProd_div hnd_e he_pr
  have hθ_pos : 0 < theta E := theta_pos fun p hp => Nat.prime_of_mem_primeFactors (hE_sub hp)
  have hsub_nn : (0 : ℝ) ≤ (n : ℝ) - α := by
    have h1 : (α : ℝ) ≤ n := by exact_mod_cast hαn
    linarith
  have h1 : ((Nat.totient n - 1 : ℕ) : ℝ) * n ≤ theta E * ((n : ℝ) - α) * ((n : ℝ) + (Le_num : ℝ) / 16) := by
    have := mul_le_mul_of_nonneg_left (add_le_add_left hLe_le (n : ℝ)) (mul_nonneg hθ_pos.le hsub_nn)
    linarith
  set lhs := (Nat.totient n - 1) * P_e * n * 16
  set den := phi_e * (n * 16 + Le_num)
  have hden_pos : 0 < den := Nat.mul_pos hphie_pos (by omega)
  have hnat_le : lhs ≤ (n - α) * den := by
    have hR : (lhs : ℝ) ≤ ((n - α : ℕ) : ℝ) * (den : ℝ) := by
      rw [Nat.cast_sub hαn]
      have hmul := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ (P_e : ℝ) * 16)
      rw [hθE] at hmul
      have hPe_ne : (P_e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hPe_pos.ne'
      dsimp [lhs, den]; push_cast
      have hl : ((Nat.totient n - 1 : ℕ) : ℝ) * n * (P_e * 16) = ((Nat.totient n - 1 : ℕ) : ℝ) * P_e * n * 16 := by ring
      have hr : (phi_e : ℝ) / P_e * ((n : ℝ) - α) * ((n : ℝ) + (Le_num : ℝ) / 16) * (P_e * 16) =
          ((n : ℝ) - α) * (phi_e * (n * 16 + Le_num)) := by field_simp [hPe_ne]
      linarith
    exact_mod_cast hR
  have hceil : (lhs + den - 1) / den ≤ n - α := by
    rw [Nat.div_le_iff_le_mul_add_pred hden_pos]
    have hadd : lhs + (den - 1) ≤ (n - α) * den + (den - 1) := Nat.add_le_add_right hnat_le (den - 1)
    have hsub : lhs + den - 1 = lhs + (den - 1) := by omega
    rw [hsub, mul_comm den]; exact hadd
  change α ≤ if den == 0 then n else if (lhs + den - 1) / den ≤ n then n - (lhs + den - 1) / den else 0
  have hden_ne : (den == 0) = false := beq_false_of_ne hden_pos.ne'
  rw [hden_ne]; dsimp
  split_ifs with hle <;> omega

lemma upperKillsA_sound
    {q n k a b sq16 k_max : ℕ} (_hq : q = n + 1) (_hn7 : 7 ≤ n) (hsq : 256 * q ≤ sq16 * sq16)
    (ha1 : 1 ≤ a) (hsum : a + b + k = n) (hk_le : k ≤ k_max) (hdeg : Nat.totient n ≤ a + k)
    {ps : List ℕ} (hnd : ps.Nodup) (hset : ps.toFinset = n.primeFactors) (t : ℕ)
    (hUpper : ∀ (E : Finset ℕ), E ⊆ n.primeFactors →
      let Le : ℝ := ((2 : ℝ) ^ E.card - 1) * Real.sqrt q + 1
      (a : ℝ) * ((Nat.totient n - 1 : ℕ) : ℝ) * n ≤
        theta E * a * (a + k) * n +
          theta E * Le * Real.sqrt ((a : ℝ) * b * (a + k) * (b + k)))
    (hkill : upperKillsA n (Nat.totient n) sq16 k_max a (ps.take t) = true) :
    False := by
  set e_ps := ps.take t
  have hnd_e : e_ps.Nodup := hnd.sublist (List.take_sublist t ps)
  let E := e_ps.toFinset
  have hE_sub : E ⊆ n.primeFactors := by
    rw [← hset]; intro x hx; exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hx))
  have he_pr : ∀ p ∈ e_ps, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (hE_sub (List.mem_toFinset.mpr hp))
  have hE_card : E.card = e_ps.length := List.toFinset_card_of_nodup hnd_e
  have hU := hUpper E hE_sub
  set P_e := listProd e_ps
  set phi_e := listPhiProd e_ps
  set Le_num := ((1 <<< e_ps.length) - 1) * sq16 + 16
  set M := a + k_max
  set lhs0 := n * P_e * (Nat.totient n - 1)
  set rhs0 := n * phi_e * M
  unfold upperKillsA at hkill
  dsimp only at hkill
  by_cases hle0 : lhs0 ≤ rhs0
  · simp [lhs0, rhs0, M, P_e, phi_e, hle0] at hkill
  · have hle0' : ¬ lhs0 ≤ rhs0 := hle0
    push Not at hle0
    change (if lhs0 ≤ rhs0 then false else decide (((lhs0 - rhs0) * 16) * ((lhs0 - rhs0) * 16) * a >
      (phi_e * Le_num) * (phi_e * Le_num) * (n - Nat.totient n) * M * (n - a))) = true at hkill
    rw [if_neg hle0'] at hkill
    simp only [decide_eq_true_eq] at hkill
    have hPe_pos : 0 < P_e := by
      have : (0 : ℝ) < P_e := by
        rw [listProd_eq_prod hnd_e]; exact Finset.prod_pos fun p hp => Nat.cast_pos.mpr (he_pr p (List.mem_toFinset.mp hp)).pos
      exact_mod_cast this
    have hθE : theta E = (phi_e : ℝ) / (P_e : ℝ) := theta_eq_listPhiProd_div hnd_e he_pr
    have hLe_le : ((2 : ℝ) ^ E.card - 1) * Real.sqrt q + 1 ≤ (Le_num : ℝ) / 16 := by
      have hsq_le : Real.sqrt (q : ℝ) ≤ (sq16 : ℝ) / 16 := by
        rw [Real.sqrt_le_iff]; refine ⟨by positivity, ?_⟩
        have hcast : (256 : ℝ) * q ≤ (sq16 : ℝ) * sq16 := by exact_mod_cast hsq
        nlinarith only [hcast]
      have hW1 : 1 ≤ 1 <<< e_ps.length := by rw [Nat.shiftLeft_eq, one_mul]; exact Nat.one_le_two_pow
      have hWe : ((1 <<< e_ps.length - 1 : ℕ) : ℝ) = (2 : ℝ) ^ E.card - 1 := by
        rw [Nat.cast_sub hW1, Nat.cast_one, hE_card]; simp [Nat.shiftLeft_eq]
      have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ E.card - 1 := by
        have : (1 : ℝ) ≤ (2 : ℝ) ^ E.card := one_le_pow₀ (by norm_num); linarith
      dsimp [Le_num]; push_cast; rw [hWe]
      have h1 := mul_le_mul_of_nonneg_left hsq_le hnn
      linarith
    have hb_le : b ≤ n - Nat.totient n := by omega
    have hbk_le : b + k ≤ n - a := by omega
    have hak_le : a + k ≤ M := by omega
    have hprod_le : (a : ℝ) * b * (a + k) * (b + k) ≤ (a : ℝ) * (n - Nat.totient n : ℕ) * M * (n - a : ℕ) := by
      have h1 : (b : ℝ) ≤ (n - Nat.totient n : ℕ) := by exact_mod_cast hb_le
      have h2 : (a + k : ℝ) ≤ M := by exact_mod_cast hak_le
      have h3 : (b + k : ℝ) ≤ (n - a : ℕ) := by exact_mod_cast hbk_le
      have ha_nn : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      have h12 : (a : ℝ) * b ≤ (a : ℝ) * (n - Nat.totient n : ℕ) := mul_le_mul_of_nonneg_left h1 ha_nn
      have h123 : (a : ℝ) * b * (a + k) ≤ (a : ℝ) * (n - Nat.totient n : ℕ) * M :=
        mul_le_mul h12 h2 (by positivity) (by positivity)
      exact mul_le_mul h123 h3 (by positivity) (by positivity)
    have hPe_ne : (P_e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hPe_pos.ne'
    have h16P_pos : (0 : ℝ) < 16 * P_e := by positivity
    have hU2 : (a : ℝ) * ((lhs0 - rhs0 : ℕ) : ℝ) * 16 ≤
        (phi_e : ℝ) * Le_num * Real.sqrt ((a : ℝ) * (n - Nat.totient n : ℕ) * M * (n - a : ℕ)) := by
      have hmul := mul_le_mul_of_nonneg_right hU h16P_pos.le
      rw [hθE] at hmul
      have hsub : ((lhs0 - rhs0 : ℕ) : ℝ) = (lhs0 : ℝ) - (rhs0 : ℝ) := Nat.cast_sub (le_of_lt hle0)
      rw [hsub]
      have hM_ge : (a : ℝ) * (a + k) * n ≤ (a : ℝ) * M * n := by
        have h2 : (a + k : ℝ) ≤ M := by exact_mod_cast hak_le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg a)) (Nat.cast_nonneg n)
      have hsqrt_le : Real.sqrt ((a : ℝ) * b * (a + k) * (b + k)) ≤
          Real.sqrt ((a : ℝ) * (n - Nat.totient n : ℕ) * M * (n - a : ℕ)) := Real.sqrt_le_sqrt hprod_le
      have hterm1 : (phi_e : ℝ) / P_e * a * (a + k) * n * (16 * P_e) ≤ (a : ℝ) * rhs0 * 16 := by
        have heq : (phi_e : ℝ) / P_e * a * (a + k) * n * (16 * P_e) = 16 * phi_e * (a * (a + k) * n) := by
          field_simp [hPe_ne]
        rw [heq]; dsimp [rhs0]; push_cast
        have h1 := mul_le_mul_of_nonneg_left hM_ge (by positivity : (0 : ℝ) ≤ 16 * phi_e)
        linarith [show 16 * (phi_e : ℝ) * ((a : ℝ) * M * n) = (a : ℝ) * ((n : ℝ) * phi_e * M) * 16 by ring]
      have hterm2 : (phi_e : ℝ) / P_e * (((2 : ℝ) ^ E.card - 1) * Real.sqrt q + 1) *
          Real.sqrt ((a : ℝ) * b * (a + k) * (b + k)) * (16 * P_e) ≤
          (phi_e : ℝ) * Le_num * Real.sqrt ((a : ℝ) * (n - Nat.totient n : ℕ) * M * (n - a : ℕ)) := by
        have hrew : (phi_e : ℝ) / P_e * (((2 : ℝ) ^ E.card - 1) * Real.sqrt q + 1) *
            Real.sqrt ((a : ℝ) * b * (a + k) * (b + k)) * (16 * P_e) =
            (phi_e : ℝ) * (16 * (((2 : ℝ) ^ E.card - 1) * Real.sqrt q + 1)) *
              Real.sqrt ((a : ℝ) * b * (a + k) * (b + k)) := by field_simp [hPe_ne]
        rw [hrew]
        have h16Le : 16 * (((2 : ℝ) ^ E.card - 1) * Real.sqrt q + 1) ≤ (Le_num : ℝ) := by linarith
        have h16Le_nn : 0 ≤ 16 * (((2 : ℝ) ^ E.card - 1) * Real.sqrt q + 1) := by
          have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ E.card := one_le_pow₀ (by norm_num)
          nlinarith only [h1, Real.sqrt_nonneg (q : ℝ)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left h16Le (Nat.cast_nonneg phi_e)) hsqrt_le
          (Real.sqrt_nonneg _) (by positivity)
      have hlhs_eq : (a : ℝ) * ((Nat.totient n - 1 : ℕ) : ℝ) * n * (16 * P_e) = (a : ℝ) * lhs0 * 16 := by
        dsimp [lhs0]; push_cast; ring
      linarith
    have hsq2 : ((a : ℝ) * ((lhs0 - rhs0 : ℕ) : ℝ) * 16) ^ 2 ≤
        ((phi_e : ℝ) * Le_num * Real.sqrt ((a : ℝ) * (n - Nat.totient n : ℕ) * M * (n - a : ℕ))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hU2 2
    rw [mul_pow ((phi_e : ℝ) * Le_num), Real.sq_sqrt (by positivity)] at hsq2
    have hkillR : ((phi_e : ℝ) * Le_num) ^ 2 * (n - Nat.totient n : ℕ) * M * (n - a : ℕ) <
        (((lhs0 - rhs0 : ℕ) : ℝ) * 16) ^ 2 * a := by
      have h1 : (((phi_e * Le_num) * (phi_e * Le_num) * (n - Nat.totient n) * M * (n - a) : ℕ) : ℝ) <
          ((((lhs0 - rhs0) * 16) * ((lhs0 - rhs0) * 16) * a : ℕ) : ℝ) := Nat.cast_lt.mpr hkill
      push_cast at h1
      simpa only [sq] using h1
    have ha_posR : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
    have hlt_a := mul_lt_mul_of_pos_left hkillR ha_posR
    linarith [show ((a : ℝ) * ((lhs0 - rhs0 : ℕ) : ℝ) * 16) ^ 2 = (a : ℝ) * ((((lhs0 - rhs0 : ℕ) : ℝ) * 16) ^ 2 * a) by ring,
      show ((phi_e : ℝ) * Le_num) ^ 2 * ((a : ℝ) * (n - Nat.totient n : ℕ) * M * (n - a : ℕ)) =
          (a : ℝ) * (((phi_e : ℝ) * Le_num) ^ 2 * (n - Nat.totient n : ℕ) * M * (n - a : ℕ)) by ring]

lemma lowerCutHolds_contradiction
    {n k a b Ln Ld k_max a_cut : ℕ}
    (_ha1 : 1 ≤ a) (hab : a ≤ b) (hsum : a + b + k = n) (hk_le : k ≤ k_max)
    (ha_ge : a_cut ≤ a) (_hLd : 0 < Ld)
    (hCut : Ln < n * Ld → (n : ℝ) ^ 2 * a * b * (Ld : ℝ) ^ 2 ≤ (Ln : ℝ) ^ 2 * (a + k) * (b + k))
    (hholds : lowerCutHolds n Ln Ld k_max a_cut = true) : False := by
  unfold lowerCutHolds at hholds
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hholds
  obtain ⟨hLn_lt, hineq⟩ := hholds
  have hCut' := hCut hLn_lt
  have hsumR : (a : ℝ) + b + k = n := by exact_mod_cast hsum
  have hcut2 : (a : ℝ) * b * ((n : ℝ) ^ 2 * (Ld : ℝ) ^ 2 - (Ln : ℝ) ^ 2) ≤ (k : ℝ) * n * (Ln : ℝ) ^ 2 := by
    have hid : ((a : ℝ) + k) * ((b : ℝ) + k) = a * b + k * n := by linear_combination k * hsumR
    have hCut'' : (n : ℝ) ^ 2 * a * b * (Ld : ℝ) ^ 2 ≤ (Ln : ℝ) ^ 2 * ((a : ℝ) * b + k * n) := by
      have : (Ln : ℝ) ^ 2 * ((a : ℝ) + k) * ((b : ℝ) + k) = (Ln : ℝ) ^ 2 * (((a : ℝ) + k) * ((b : ℝ) + k)) := by ring
      rw [← hid, ← this]; exact hCut'
    linarith [show (n : ℝ) ^ 2 * a * b * (Ld : ℝ) ^ 2 - (Ln : ℝ) ^ 2 * ((a : ℝ) * b + k * n) =
        (a : ℝ) * b * ((n : ℝ) ^ 2 * (Ld : ℝ) ^ 2 - (Ln : ℝ) ^ 2) - (k : ℝ) * n * (Ln : ℝ) ^ 2 by ring]
  have hpos_fac : (0 : ℝ) < (n : ℝ) ^ 2 * (Ld : ℝ) ^ 2 - (Ln : ℝ) ^ 2 := by
    have h1 : (Ln : ℝ) < (n : ℝ) * Ld := by exact_mod_cast hLn_lt
    have h2 : (0 : ℝ) ≤ Ln := Nat.cast_nonneg Ln
    nlinarith only [h1, h2]
  have hab_ge : (a_cut : ℝ) * ((n - k_max - a_cut : ℕ) : ℝ) ≤ (a : ℝ) * b := by
    have h1 : a_cut * (n - k_max - a_cut) ≤ a * b := by
      have h2 : (a - a_cut) * (b - a_cut) + a_cut * (n - k - a_cut) = a * b := by
        zify [ha_ge, le_trans ha_ge hab, show a_cut ≤ n - k by omega, show k ≤ n by omega]
        have hsumZ : (a : ℤ) + b + k = n := by exact_mod_cast hsum
        linear_combination -(a_cut : ℤ) * hsumZ
      have h3 : n - k_max - a_cut ≤ n - k - a_cut := by omega
      have h4 : a_cut * (n - k_max - a_cut) ≤ a_cut * (n - k - a_cut) := Nat.mul_le_mul_left _ h3
      omega
    exact_mod_cast h1
  have hineqR : (Ln : ℝ) ^ 2 * (a_cut + k_max) * ((n - k_max - a_cut : ℕ) + k_max) <
      (n : ℝ) ^ 2 * a_cut * ((n - k_max - a_cut : ℕ) : ℝ) * (Ld : ℝ) ^ 2 := by
    have : ((Ln * Ln * (a_cut + k_max) * ((n - k_max - a_cut) + k_max) : ℕ) : ℝ) <
        ((n * n * a_cut * (n - k_max - a_cut) * Ld * Ld : ℕ) : ℝ) := by exact_mod_cast hineq
    push_cast at this
    linarith [sq (Ln : ℝ), sq (n : ℝ), sq (Ld : ℝ),
      show (Ln : ℝ) * Ln * (a_cut + k_max) * ((n - k_max - a_cut : ℕ) + k_max) =
          (Ln : ℝ) ^ 2 * (a_cut + k_max) * ((n - k_max - a_cut : ℕ) + k_max) by ring,
      show (n : ℝ) * n * a_cut * ((n - k_max - a_cut : ℕ) : ℝ) * Ld * Ld =
          (n : ℝ) ^ 2 * a_cut * ((n - k_max - a_cut : ℕ) : ℝ) * (Ld : ℝ) ^ 2 by ring]
  have hkmax_le : k_max + a_cut ≤ n := by
    by_contra hgt
    have h0 : n - k_max - a_cut = 0 := by omega
    simp [h0] at hineq
  have hid2 : ((a_cut : ℝ) + k_max) * (((n - k_max - a_cut : ℕ) : ℝ) + k_max) =
      (a_cut : ℝ) * ((n - k_max - a_cut : ℕ) : ℝ) + (k_max : ℝ) * n := by
    have hsub : ((n - k_max - a_cut : ℕ) : ℝ) = (n : ℝ) - k_max - a_cut := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    rw [hsub]; ring
  have hineq2 : (k_max : ℝ) * n * (Ln : ℝ) ^ 2 <
      (a_cut : ℝ) * ((n - k_max - a_cut : ℕ) : ℝ) * ((n : ℝ) ^ 2 * (Ld : ℝ) ^ 2 - (Ln : ℝ) ^ 2) := by
    have : (Ln : ℝ) ^ 2 * ((a_cut : ℝ) + k_max) * (((n - k_max - a_cut : ℕ) : ℝ) + k_max) =
        (Ln : ℝ) ^ 2 * (((a_cut : ℝ) + k_max) * (((n - k_max - a_cut : ℕ) : ℝ) + k_max)) := by ring
    rw [this, hid2] at hineqR
    linarith [show (n : ℝ) ^ 2 * a_cut * ((n - k_max - a_cut : ℕ) : ℝ) * (Ld : ℝ) ^ 2 -
        (Ln : ℝ) ^ 2 * ((a_cut : ℝ) * ((n - k_max - a_cut : ℕ) : ℝ) + (k_max : ℝ) * n) =
        (a_cut : ℝ) * ((n - k_max - a_cut : ℕ) : ℝ) * ((n : ℝ) ^ 2 * (Ld : ℝ) ^ 2 - (Ln : ℝ) ^ 2) -
        (k_max : ℝ) * n * (Ln : ℝ) ^ 2 by ring]
  have hk_leR : (k : ℝ) ≤ k_max := by exact_mod_cast hk_le
  have h1 := mul_le_mul_of_nonneg_right hab_ge hpos_fac.le
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk_leR (Nat.cast_nonneg n)) (sq_nonneg (Ln : ℝ))
  linarith

lemma checkAnalyticQ_sound
    {q n α k a b : ℕ} (hq : q = n + 1) (hn7 : 7 ≤ n)
    (ha1 : 1 ≤ a) (hab : a ≤ b) (hsum : a + b + k = n) (hka : k < α) (hαn : α ≤ n)
    (hdeg : Nat.totient n ≤ a + k)
    (hLower : ∀ (E Sp : Finset ℕ), Disjoint E Sp → E ∪ Sp = n.primeFactors →
      ∀ (_hΔ : 0 < 1 - ∑ p ∈ Sp, (1 : ℝ) / p),
        let Δ : ℝ := 1 - ∑ p ∈ Sp, (1 : ℝ) / p
        let δ : ℝ := theta E * Δ
        let K : ℝ := if Sp = ∅ then (2 : ℝ) ^ E.card - 1
          else (2 : ℝ) ^ E.card * (((Sp.card : ℝ) - 1) / Δ + 2) - 1
        let L : ℝ := K * Real.sqrt q + 1
        (α : ℝ) * (n + L) ≤ n * (L + 1 / δ) ∧
        (n : ℝ) ^ 2 * a * b ≤ L ^ 2 * (a + k) * (b + k))
    (hUpper : ∀ (E : Finset ℕ), E ⊆ n.primeFactors →
      let Le : ℝ := ((2 : ℝ) ^ E.card - 1) * Real.sqrt q + 1
      ((Nat.totient n - 1 : ℕ) : ℝ) * n ≤ theta E * (n - α) * (n + Le) ∧
      (a : ℝ) * ((Nat.totient n - 1 : ℕ) : ℝ) * n ≤
        theta E * a * (a + k) * n +
          theta E * Le * Real.sqrt ((a : ℝ) * b * (a + k) * (b + k)))
    (hcheck : checkAnalyticQ q = true) : False := by
  unfold checkAnalyticQ at hcheck
  dsimp only at hcheck
  have hqsub : q - 1 = n := by omega
  rw [hqsub] at hcheck
  set ps := findPrimeFactors n
  by_cases hval : validPrimeFactors n ps = true
  · rw [hval] at hcheck; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hcheck
    obtain ⟨_, hnd, hset⟩ := validPrimeFactors_sound hval
    have hphi_eq : ps.foldl (fun acc p => acc / p * (p - 1)) n = Nat.totient n :=
      foldl_phi_eq_totient (by omega) hnd hset
    rw [hphi_eq] at hcheck
    set sq16 := Nat.sqrt (256 * q - 1) + 1
    by_cases hsq_bad : 256 * q > sq16 * sq16
    · rw [if_pos hsq_bad] at hcheck; simp at hcheck
    · rw [if_neg hsq_bad] at hcheck
      have hsq : 256 * q ≤ sq16 * sq16 := by omega
      have hloopL : ∀ rem bestA bestLn bestLd,
          rem ≤ ps.length + 1 →
          α ≤ bestA →
          0 < bestLd →
          (bestLn < n * bestLd → (n : ℝ) ^ 2 * a * b * (bestLd : ℝ) ^ 2 ≤ (bestLn : ℝ) ^ 2 * (a + k) * (b + k)) →
          let r := loopLowerAux n sq16 ps rem bestA bestLn bestLd
          α ≤ r.1 ∧ 0 < r.2.2 ∧
          (r.2.1 < n * r.2.2 → (n : ℝ) ^ 2 * a * b * (r.2.2 : ℝ) ^ 2 ≤ (r.2.1 : ℝ) ^ 2 * (a + k) * (b + k)) := by
        intro rem
        induction rem with
        | zero => intro bA bLn bLd _ h1 h2 h3; exact ⟨h1, h2, h3⟩
        | succ rem ih =>
          intro bA bLn bLd hrem h1 h2 h3
          unfold loopLowerAux
          set s := ps.length - rem
          have hs_le : s ≤ ps.length := Nat.sub_le _ _
          dsimp only
          generalize hres_eq : lowerSieveParams n sq16 (ps.take (ps.length - s)) (ps.drop (ps.length - s)) = res
          rcases res with ⟨ok, Ln, Ld, aub⟩
          dsimp only
          by_cases hok : ok = true
          · rw [if_pos hok]
            have hsound := lowerSieveParams_sound hq hn7 hαn hsq hnd hset hs_le hLower (by rw [hres_eq]; exact hok)
            rw [hres_eq] at hsound
            by_cases hcmp : Ln * bLd < bLn * Ld
            · rw [if_pos hcmp]; dsimp only
              exact ih _ _ _ (by omega) (le_min h1 hsound.2.1) hsound.1 (fun _ => hsound.2.2)
            · rw [if_neg hcmp]; dsimp only
              exact ih _ _ _ (by omega) (le_min h1 hsound.2.1) h2 h3
          · rw [if_neg hok]
            exact ih bA bLn bLd (by omega) h1 h2 h3
      have hL0 := hloopL (ps.length + 1) n (n + 1) 1 le_rfl hαn Nat.one_pos (fun h => by omega)
      set bestA0 := (loopLowerAux n sq16 ps (ps.length + 1) n (n + 1) 1).1
      set bestLn := (loopLowerAux n sq16 ps (ps.length + 1) n (n + 1) 1).2.1
      set bestLd := (loopLowerAux n sq16 ps (ps.length + 1) n (n + 1) 1).2.2
      have hloopU : ∀ t bA, α ≤ bA → α ≤ loopUpperAlphaAux n (Nat.totient n) sq16 ps t bA := by
        intro t
        induction t with
        | zero => intro bA h; exact h
        | succ t ih =>
          intro bA h
          unfold loopUpperAlphaAux
          exact ih _ (le_min h (upperAlphaUb_sound hq hn7 hαn hsq hnd hset (t + 1) (fun E hE => (hUpper E hE).1)))
      have hα_best : α ≤ loopUpperAlphaAux n (Nat.totient n) sq16 ps ps.length bestA0 := hloopU ps.length bestA0 hL0.1
      set bestA := loopUpperAlphaAux n (Nat.totient n) sq16 ps ps.length bestA0
      have hkill_range : ∀ k_max rem start, k ≤ k_max →
          checkRangeUpper n (Nat.totient n) sq16 k_max ps rem start = true →
          start ≤ a → a < start + rem → False := by
        intro k_max rem start hk_le hrange hge hlt
        have hkill_any : ∀ rem start, checkRangeUpper n (Nat.totient n) sq16 k_max ps rem start = true →
            start ≤ a → a < start + rem → upperKillsA_any n (Nat.totient n) sq16 k_max a ps ps.length = true := by
          intro r
          induction r with
          | zero => intro st _ h1 h2; omega
          | succ r ih =>
            intro st hr h1 h2
            unfold checkRangeUpper at hr
            simp only [Bool.and_eq_true] at hr
            by_cases heq : a = st
            · subst heq; exact hr.1
            · exact ih (st + 1) hr.2 (by omega) (by omega)
        have hka_true := hkill_any rem start hrange hge hlt
        have hkill_t : ∀ t, upperKillsA_any n (Nat.totient n) sq16 k_max a ps t = true →
            ∃ t', upperKillsA n (Nat.totient n) sq16 k_max a (ps.take t') = true := by
          intro t
          induction t with
          | zero => intro h; simp [upperKillsA_any] at h
          | succ t ih =>
            intro h; unfold upperKillsA_any at h
            simp only [Bool.or_eq_true] at h
            rcases h with h1 | h2
            · exact ⟨t + 1, h1⟩
            · exact ih h2
        obtain ⟨t', ht'⟩ := hkill_t ps.length hka_true
        exact upperKillsA_sound hq hn7 hsq ha1 hsum hk_le hdeg hnd hset t' (fun E hE => (hUpper E hE).2) ht'
      by_cases hA0 : bestA = 0
      · omega
      · have hA0b : (bestA == 0) = false := beq_false_of_ne hA0
        have hk_le : k ≤ bestA - 1 := by omega
        set k_max := bestA - 1
        by_cases hdirac : 2 * Nat.totient n > n + k_max
        · omega
        · set a_lo := if Nat.totient n > k_max then Nat.totient n - k_max else 1
          have ha_ge_lo : a_lo ≤ a := by dsimp [a_lo]; split_ifs <;> omega
          by_cases halo_gt : a_lo > n / 2
          · omega
          · by_cases hcut_lo : lowerCutHolds n bestLn bestLd k_max a_lo = true
            · exact lowerCutHolds_contradiction ha1 hab hsum hk_le ha_ge_lo hL0.2.1 hL0.2.2 hcut_lo
            · set a_lim := (n - k_max) / 2
              set a_cut := findACutAux n bestLn bestLd k_max a_lim (a_lim - a_lo + 1) a_lo
              have hcheck' : (if lowerCutHolds n bestLn bestLd k_max a_cut = true then
                  checkRangeUpper n (Nat.totient n) sq16 k_max ps (a_cut - a_lo) a_lo
                else checkRangeUpper n (Nat.totient n) sq16 k_max ps (n / 2 - a_lo + 1) a_lo) = true := by
                simpa only [hA0b, Bool.false_eq_true, ↓reduceIte, hdirac, halo_gt, hcut_lo] using hcheck
              by_cases hcut_c : lowerCutHolds n bestLn bestLd k_max a_cut = true
              · rw [if_pos hcut_c] at hcheck'
                by_cases ha_ge_cut : a_cut ≤ a
                · exact lowerCutHolds_contradiction ha1 hab hsum hk_le ha_ge_cut hL0.2.1 hL0.2.2 hcut_c
                · exact hkill_range k_max (a_cut - a_lo) a_lo hk_le hcheck' ha_ge_lo (by omega)
              · rw [if_neg hcut_c] at hcheck'
                exact hkill_range k_max (n / 2 - a_lo + 1) a_lo hk_le hcheck' ha_ge_lo (by omega)
  · have hvalf : validPrimeFactors n ps = false := Bool.eq_false_iff.mpr hval
    simp [hvalf] at hcheck

lemma checkAllBelow8100_sound : ∀ rem start q,
    checkAllBelow8100 rem start = true →
    start ≤ q → q < start + rem → q < 8100 →
    (∃ p e : ℕ, p.Prime ∧ 0 < e ∧ q = p ^ e) →
    q ∉ except44 →
    checkAnalyticQ q = true
  | 0, _, _, _, h1, h2, _, _, _ => by omega
  | rem + 1, start, q, hall, h1, h2, hlt8100, hpp, hnot => by
    unfold checkAllBelow8100 at hall
    simp only [Bool.and_eq_true] at hall
    by_cases heq : q = start
    · subst heq
      have h1q := hall.1
      unfold checkOneQ at h1q
      dsimp only at h1q
      split_ifs at h1q with hnotpp hinex
      · simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hnotpp
        exact absurd hpp (not_prime_pow_of_stripPow hlt8100 (isPrimeBool_sound hnotpp.1.1)
          (Nat.dvd_of_mod_eq_zero hnotpp.1.2) hnotpp.2)
      · exact absurd (List.contains_iff_mem.mp hinex) hnot
      · exact h1q
    · exact checkAllBelow8100_sound rem (start + 1) q hall.2 (by omega) (by omega) hlt8100 hpp hnot

theorem below8100_ok : checkAllBelow8100 8092 8 = true := by decide +kernel

end RangeCheckerFinal

section CycleVerifiers

/-- Transport existence of a primitive-product circular permutation along any ring equivalence `e : K ≃+* F`. -/
lemma exists_circ_perm_of_ringEquiv {K F : Type*} [Field K] [Fintype K] [Field F] [Fintype F]
    (hcard : Fintype.card K = Fintype.card F) (e : K ≃+* F) (a₀K : K) (a₀F : F) (ha₀ : e a₀K = a₀F)
    (hK : ∃ a : Fin (Fintype.card K - 1) ≃ Kˣ,
      ∀ i : Fin (Fintype.card K - 1),
        IsPrimitiveRoot ((a i : K) * (a ⟨(i.val + 1) % (Fintype.card K - 1),
          Nat.mod_lt _ (by have := Fintype.one_lt_card (α := K); omega)⟩ : K) + a₀K) (Fintype.card K - 1)) :
    ∃ a : Fin (Fintype.card F - 1) ≃ Fˣ,
      ∀ i : Fin (Fintype.card F - 1),
        IsPrimitiveRoot ((a i : F) * (a ⟨(i.val + 1) % (Fintype.card F - 1),
          Nat.mod_lt _ (by have := Fintype.one_lt_card (α := F); omega)⟩ : F) + a₀F) (Fintype.card F - 1) := by
  obtain ⟨a, ha⟩ := hK
  let eU : Kˣ ≃* Fˣ := Units.mapEquiv e.toMulEquiv
  let eFin : Fin (Fintype.card F - 1) ≃ Fin (Fintype.card K - 1) :=
    (Fin.castOrderIso (congrArg (· - 1) hcard.symm)).toEquiv
  refine ⟨(eFin.trans a).trans eU.toEquiv, fun i => ?_⟩
  have h1 := ha (eFin i)
  have hmap : IsPrimitiveRoot (e (((a (eFin i) : K) * (a ⟨((eFin i).val + 1) % (Fintype.card K - 1),
      Nat.mod_lt _ (by have := Fintype.one_lt_card (α := K); omega)⟩ : K) + a₀K))) (Fintype.card K - 1) :=
    h1.map_of_injective e.injective
  rw [map_add, map_mul, ha₀] at hmap
  have hidx : eFin ⟨(i.val + 1) % (Fintype.card F - 1), Nat.mod_lt _ (by have := Fintype.one_lt_card (α := F); omega)⟩ =
      ⟨((eFin i).val + 1) % (Fintype.card K - 1), Nat.mod_lt _ (by have := Fintype.one_lt_card (α := K); omega)⟩ := by
    ext; simp [eFin, hcard]
  have hcoe : ∀ u : Kˣ, ((eU.toEquiv u : Fˣ) : F) = e (u : K) := fun _ => rfl
  simp only [Equiv.trans_apply, hcoe]
  let xval : F := e (a (eFin i) : K) * e (a (eFin ⟨(i.val + 1) % (Fintype.card F - 1),
      Nat.mod_lt _ (by have := Fintype.one_lt_card (α := F); omega)⟩) : K) + a₀F
  have hmap' : IsPrimitiveRoot xval (Fintype.card K - 1) := by
    dsimp [xval]; rwa [hidx]
  have hord_eq : Fintype.card K - 1 = Fintype.card F - 1 := congrArg (· - 1) hcard
  change IsPrimitiveRoot xval (Fintype.card F - 1)
  rwa [← hord_eq]

/-- Transport between `a₀ = -1` and `a₀ = +1` when `q ≡ 1 (mod 4)` (using `i^2 = -1`, `b_k = i * a_k`)! -/
lemma exists_plus_one_of_minus_one_mod4 {F : Type*} [Field F] [Fintype F]
    (hF : 7 < Fintype.card F) (h4 : 4 ∣ Fintype.card F - 1)
    (hminus : ∃ a : Fin (Fintype.card F - 1) ≃ Fˣ,
      ∀ i : Fin (Fintype.card F - 1),
        IsPrimitiveRoot ((a i : F) * (a ⟨(i.val + 1) % (Fintype.card F - 1), Nat.mod_lt _ (by omega)⟩ : F) - 1)
          (Fintype.card F - 1)) :
    ∃ b : Fin (Fintype.card F - 1) ≃ Fˣ,
      ∀ i : Fin (Fintype.card F - 1),
        IsPrimitiveRoot ((b i : F) * (b ⟨(i.val + 1) % (Fintype.card F - 1), Nat.mod_lt _ (by omega)⟩ : F) + 1)
          (Fintype.card F - 1) := by
  classical
  let m := Fintype.card F - 1
  have hcard_u : Fintype.card Fˣ = m := Fintype.card_units (α := F)
  obtain ⟨k, hk⟩ := h4
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord_g : orderOf g = m := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcard_u]
  let s : Fˣ := g ^ k
  have hs4 : s ^ 4 = 1 := by
    dsimp [s]; rw [← pow_mul, mul_comm, ← hk, show Fintype.card F - 1 = m from rfl, ← hcard_u]; exact pow_card_eq_one
  have hs2_ne1 : s ^ 2 ≠ 1 := by
    intro h1
    dsimp [s] at h1
    rw [← pow_mul] at h1
    have hdvd : m ∣ k * 2 := hord_g ▸ orderOf_dvd_of_pow_eq_one h1
    have hpos : 0 < k * 2 := by omega
    have := Nat.le_of_dvd hpos hdvd
    omega
  have hs2_val : ((s : F) ^ 2) = -1 := by
    have hsq : ((s : F) ^ 2) ^ 2 = 1 := by
      have : ((s ^ 4 : Fˣ) : F) = 1 := by rw [hs4]; rfl
      simpa [← pow_mul] using this
    rcases sq_eq_one_iff.mp hsq with h1 | hm1
    · exfalso; apply hs2_ne1; exact Units.ext (by simpa using h1)
    · exact hm1
  have hneg_prim : ∀ x : F, IsPrimitiveRoot x m → IsPrimitiveRoot (-x) m := by
    intro x hx
    have hx2k_sq : (x ^ (2 * k)) ^ 2 = 1 := by
      rw [← pow_mul, show 2 * k * 2 = m by omega]; exact hx.pow_eq_one
    have hx2k_ne1 : x ^ (2 * k) ≠ 1 := by
      intro h1
      have hdvd := hx.dvd_of_pow_eq_one (2 * k) h1
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    have hx2k_eq : x ^ (2 * k) = -1 := (sq_eq_one_iff.mp hx2k_sq).resolve_left hx2k_ne1
    have hnegx : -x = x ^ (2 * k + 1) := by rw [pow_succ, hx2k_eq]; ring
    rw [hnegx]
    have hcop : Nat.Coprime (2 * k + 1) m := by
      rw [Nat.coprime_iff_gcd_eq_one]
      have hd1 : Nat.gcd (2 * k + 1) m ∣ 2 * (2 * k + 1) - m :=
        Nat.dvd_sub (dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) 2) (Nat.gcd_dvd_right _ _)
      have hsub : 2 * (2 * k + 1) - m = 2 := by omega
      rw [hsub] at hd1
      have hodd : ¬ 2 ∣ (2 * k + 1) := by omega
      rcases (Nat.dvd_prime Nat.prime_two).mp hd1 with h1 | h2
      · exact h1
      · have hd2 : 2 ∣ 2 * k + 1 := by
          have := Nat.gcd_dvd_left (2 * k + 1) m
          rwa [h2] at this
        exact absurd hd2 hodd
    exact hx.pow_of_coprime (2 * k + 1) hcop
  obtain ⟨a, ha⟩ := hminus
  refine ⟨a.trans (Equiv.mulLeft s), fun i => ?_⟩
  have hprod : ((s * a i : Fˣ) : F) * ((s * a ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩ : Fˣ) : F) + 1 =
      -(((a i : F) * (a ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩ : F)) - 1) := by
    simp only [Units.val_mul]
    have h1 : (s : F) * (a i : F) * ((s : F) * (a ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩ : F)) + 1 =
        (s : F) ^ 2 * ((a i : F) * (a ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩ : F)) + 1 := by ring
    rw [h1, hs2_val]
    ring
  have hprim := hneg_prim _ (ha i)
  change IsPrimitiveRoot (((s * a i : Fˣ) : F) * ((s * a ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩ : Fˣ) : F) + 1) m
  rwa [hprod]

/-- Transport between `a₀ = -1` and `a₀ = +1` when `char F = 2` (`q = 16`): `-1 = +1`! -/
lemma exists_plus_one_of_minus_one_even {F : Type*} [Field F] [Fintype F]
    (h2 : Even (Fintype.card F))
    (hminus : ∃ a : Fin (Fintype.card F - 1) ≃ Fˣ,
      ∀ i : Fin (Fintype.card F - 1),
        IsPrimitiveRoot ((a i : F) * (a ⟨(i.val + 1) % (Fintype.card F - 1),
          Nat.mod_lt _ (by have := Fintype.one_lt_card (α := F); omega)⟩ : F) - 1) (Fintype.card F - 1)) :
    ∃ b : Fin (Fintype.card F - 1) ≃ Fˣ,
      ∀ i : Fin (Fintype.card F - 1),
        IsPrimitiveRoot ((b i : F) * (b ⟨(i.val + 1) % (Fintype.card F - 1),
          Nat.mod_lt _ (by have := Fintype.one_lt_card (α := F); omega)⟩ : F) + 1) (Fintype.card F - 1) := by
  obtain ⟨p, hcp, n, hp, hcard⟩ := FiniteField.card' F
  have hp2 : p = 2 := by
    have hd2 : 2 ∣ p ^ (n : ℕ) := by rw [← hcard]; exact even_iff_two_dvd.mp h2
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.Prime.dvd_of_dvd_pow Nat.prime_two hd2)).symm
  subst hp2
  have hneg1 : (-1 : F) = 1 := by
    have h2z : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two, h2z]
    exact eq_of_sub_eq_zero (by linear_combination -this)
  obtain ⟨a, ha⟩ := hminus
  refine ⟨a, fun i => ?_⟩
  have := ha i
  rwa [sub_eq_add_neg, hneg1] at this

def powModAux : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _, acc => acc
  | fuel + 1, b, e, m, acc =>
    if e == 0 then acc
    else
      let acc' := if e % 2 == 1 then (acc * b) % m else acc
      powModAux fuel ((b * b) % m) (e / 2) m acc'

def powMod (b e m : ℕ) : ℕ := powModAux 16 (b % m) e m 1

lemma powModAux_eq : ∀ (fuel b e m acc : ℕ), e < 2 ^ fuel →
    powModAux fuel b e m acc % m = (acc * b ^ e) % m
  | 0, b, e, m, acc, he => by
    have : e = 0 := by omega
    subst this; simp [powModAux]
  | fuel + 1, b, e, m, acc, he => by
    unfold powModAux
    by_cases he0 : e = 0
    · subst he0; simp
    · simp only [beq_iff_eq, he0, ↓reduceIte]
      have hdiv : e / 2 < 2 ^ fuel := by
        rw [pow_succ'] at he; omega
      rw [powModAux_eq fuel ((b * b) % m) (e / 2) m _ hdiv]
      by_cases hodd : e % 2 = 1
      · simp only [hodd, ↓reduceIte]
        have hdecomp : e = 2 * (e / 2) + 1 := by omega
        calc ((acc * b) % m * ((b * b) % m) ^ (e / 2)) % m
            = ((acc * b) * (b * b) ^ (e / 2)) % m := by
                simp only [Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
          _ = (acc * b ^ e) % m := by
                congr 1; conv_rhs => rw [hdecomp, pow_succ, pow_mul, sq]
                ring
      · simp only [hodd, ↓reduceIte]
        have hdecomp : e = 2 * (e / 2) := by omega
        calc (acc * ((b * b) % m) ^ (e / 2)) % m
            = (acc * (b * b) ^ (e / 2)) % m := by
                simp only [Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
          _ = (acc * b ^ e) % m := by
                congr 1; conv_rhs => rw [hdecomp, pow_mul, sq]

lemma powMod_eq {b e m : ℕ} (he : e < 2 ^ 16) : powMod b e m % m = (b ^ e) % m := by
  unfold powMod
  rw [powModAux_eq 16 (b % m) e m 1 he, one_mul]
  simp only [Nat.pow_mod, Nat.mod_mod]

def buildPrimMaskAux (p g : ℕ) (ps : List ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, mask => mask
  | rem + 1, k, cur, mask =>
    let mask' := if ps.all (fun r => k % r != 0) then mask ||| (1 <<< cur) else mask
    buildPrimMaskAux p g ps rem (k + 1) ((cur * g) % p) mask'

def buildPrimMask (p g : ℕ) (ps : List ℕ) : ℕ :=
  buildPrimMaskAux p g ps (p - 1) 1 (g % p) 0

def unpackBlock : ℕ → ℕ → ℕ → List ℕ → List ℕ
  | 0, _, _, tail => tail
  | k + 1, q, acc, tail => (acc % q) :: unpackBlock k q (acc / q) tail

def unpackCycle (q : ℕ) : List (ℕ × ℕ) → List ℕ
  | [] => []
  | (k, acc) :: rest => unpackBlock k q acc (unpackCycle q rest)

def checkWalkPrime (p a0 primMask first : ℕ) : ℕ → ℕ → List ℕ → Bool
  | _, seen, [] => seen == (1 <<< p) - 2
  | cnt, seen, [x] =>
    let seen' := seen ||| (1 <<< x)
    (cnt == p - 2) && (seen' == (1 <<< p) - 2) && primMask.testBit ((x * first + a0) % p)
  | cnt, seen, x :: y :: rest =>
    primMask.testBit ((x * y + a0) % p) &&
    checkWalkPrime p a0 primMask first (cnt + 1) (seen ||| (1 <<< x)) (y :: rest)

def checkCyclePrime (p a0 g : ℕ) (ps : List ℕ) (packed : List (ℕ × ℕ)) : Bool :=
  let exps := ps.map (fun r => (p - 1) / r)
  let gOk := (g % p != 0) && exps.all (fun e => powMod g e p % p != 1)
  let pm := buildPrimMask p g ps
  let cyc := unpackCycle p packed
  match cyc with
  | [] => false
  | x :: _ => gOk && checkWalkPrime p a0 pm x 0 0 cyc

lemma testBit_one_shiftLeft_eq {x z : ℕ} (h : (1 <<< x).testBit z = true) : z = x := by
  rw [Nat.testBit_shiftLeft] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h0 : z - x = 0 := by
    cases hd : z - x with
    | zero => rfl
    | succ d =>
      have h1 := h.2
      rw [hd, Nat.testBit_succ] at h1
      simp at h1
  omega

lemma testBit_buildPrimMaskAux {p g : ℕ} {ps : List ℕ} :
    ∀ (rem k cur mask z : ℕ),
      (∀ w, mask.testBit w = true → ∃ t, (∀ r ∈ ps, ¬ r ∣ t) ∧ g ^ t % p = w) →
      cur = g ^ k % p →
      (buildPrimMaskAux p g ps rem k cur mask).testBit z = true →
      ∃ t, (∀ r ∈ ps, ¬ r ∣ t) ∧ g ^ t % p = z
  | 0, _, _, _, z, hmask, _, hz => hmask z hz
  | rem + 1, k, cur, mask, z, hmask, hcur, hz => by
    unfold buildPrimMaskAux at hz
    apply testBit_buildPrimMaskAux rem (k + 1) ((cur * g) % p) _ z _ _ hz
    · intro w hw
      split_ifs at hw with hcop
      · rw [Nat.testBit_or, Bool.or_eq_true] at hw
        rcases hw with hw1 | hw2
        · exact hmask w hw1
        · have hweq : w = cur := testBit_one_shiftLeft_eq hw2
          refine ⟨k, fun r hr hdiv => ?_, hcur.symm.trans hweq.symm⟩
          have hall := List.all_eq_true.mp hcop r hr
          simp [Nat.dvd_iff_mod_eq_zero.mp hdiv] at hall
      · exact hmask w hw
    · rw [hcur, pow_succ, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

def qMul (p d x y : ℕ) : ℕ :=
  let a := x % p; let b := x / p
  let c := y % p; let e := y / p
  ((a * c + ((d * b) % p) * e) % p) + (((a * e + b * c) % p) * p)

def qAdd (p x y : ℕ) : ℕ :=
  ((x % p + y % p) % p) + (((x / p + y / p) % p) * p)

def qPowAux (p d : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | fuel + 1, b, e, acc =>
    if e == 0 then acc
    else
      let acc' := if e % 2 == 1 then qMul p d acc b else acc
      qPowAux p d fuel (qMul p d b b) (e / 2) acc'

def qPow (p d b e : ℕ) : ℕ := qPowAux p d 16 b e 1

def buildQuadPrimMaskAux (p d g : ℕ) (ps : List ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, mask => mask
  | rem + 1, k, cur, mask =>
    let mask' := if ps.all (fun r => k % r != 0) then mask ||| (1 <<< cur) else mask
    buildQuadPrimMaskAux p d g ps rem (k + 1) (qMul p d cur g) mask'

def buildQuadPrimMask (p d g : ℕ) (ps : List ℕ) : ℕ :=
  buildQuadPrimMaskAux p d g ps (p * p - 1) 1 g 0

def checkWalkQuad (p d a0 primMask first : ℕ) : ℕ → ℕ → List ℕ → Bool
  | _, seen, [] => seen == (1 <<< (p * p)) - 2
  | cnt, seen, [x] =>
    let seen' := seen ||| (1 <<< x)
    (cnt == p * p - 2) && (seen' == (1 <<< (p * p)) - 2) &&
      primMask.testBit (qAdd p (qMul p d x first) a0)
  | cnt, seen, x :: y :: rest =>
    primMask.testBit (qAdd p (qMul p d x y) a0) &&
    checkWalkQuad p d a0 primMask first (cnt + 1) (seen ||| (1 <<< x)) (y :: rest)

def checkCycleQuad (p d a0 g : ℕ) (ps : List ℕ) (packed : List (ℕ × ℕ)) : Bool :=
  let exps := ps.map (fun r => (p * p - 1) / r)
  let gOk := (g != 0) && (g < p * p) && exps.all (fun e => qPow p d g e != 1)
  let pm := buildQuadPrimMask p d g ps
  let cyc := unpackCycle (p * p) packed
  match cyc with
  | [] => false
  | x :: _ => gOk && checkWalkQuad p d a0 pm x 0 0 cyc

end CycleVerifiers

section CycleSoundness

lemma testBit_mask_range {q z : ℕ} (hq : 1 ≤ q) :
    ((1 <<< q) - 2).testBit z = true ↔ 1 ≤ z ∧ z < q := by
  have h1 : (1 <<< q) - 2 = 2 * ((2 ^ (q - 1)) - 1) := by
    rw [Nat.shiftLeft_eq, one_mul]
    have hpow : 2 ^ q = 2 * 2 ^ (q - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hq, pow_succ']
    omega
  rw [h1]
  cases z with
  | zero => simp
  | succ k =>
    have htb : (2 * (2 ^ (q - 1) - 1)).testBit (k + 1) = (2 ^ (q - 1) - 1).testBit k := by
      rw [Nat.testBit_succ, Nat.mul_div_right _ (by norm_num)]
    rw [htb, Nat.testBit_two_pow_sub_one]
    simp only [decide_eq_true_eq]
    omega

lemma checkWalkPrime_sound {p a0 primMask first : ℕ} (hp : 2 ≤ p) :
    ∀ (l : List ℕ) (cnt seen : ℕ) (hne : l ≠ []),
      checkWalkPrime p a0 primMask first cnt seen l = true →
      cnt + l.length = p - 1 ∧
      (∀ z, (seen.testBit z = true ∨ z ∈ l) ↔ (1 ≤ z ∧ z < p)) ∧
      (∀ i (hi : i + 1 < l.length), primMask.testBit ((l[i] * l[i + 1] + a0) % p) = true) ∧
      primMask.testBit ((l.getLast hne * first + a0) % p) = true
  | [], _, _, hne, _ => absurd rfl hne
  | [x], cnt, seen, _, h => by
    unfold checkWalkPrime at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hcnt, hseen⟩, hlast⟩ := h
    refine ⟨by simp [hcnt]; omega, fun z => ?_, fun i hi => by simp at hi, by simpa using hlast⟩
    rw [← testBit_mask_range (by omega : 1 ≤ p), ← hseen, Nat.testBit_or, Bool.or_eq_true]
    constructor
    · rintro (h1 | h2)
      · exact Or.inl h1
      · simp only [List.mem_singleton] at h2; subst h2
        right; rw [Nat.testBit_shiftLeft]; simp
    · rintro (h1 | h2)
      · exact Or.inl h1
      · exact Or.inr (by simp [testBit_one_shiftLeft_eq h2])
  | x :: y :: rest, cnt, seen, _, h => by
    unfold checkWalkPrime at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hxy, hrec⟩ := h
    have ⟨hlen, hcov, hadj, hlast⟩ :=
      checkWalkPrime_sound hp (y :: rest) (cnt + 1) (seen ||| (1 <<< x)) (List.cons_ne_nil _ _) hrec
    refine ⟨by simp at hlen ⊢; omega, fun z => ?_, fun i hi => ?_, by simpa using hlast⟩
    · rw [← hcov z, Nat.testBit_or, Bool.or_eq_true]
      have hshift : (1 <<< x).testBit z = true ↔ z = x :=
        ⟨testBit_one_shiftLeft_eq, fun h => by subst h; rw [Nat.testBit_shiftLeft]; simp⟩
      rw [hshift]
      simp only [List.mem_cons]
      tauto
    · cases i with
      | zero => simpa using hxy
      | succ j => exact hadj j (by simp at hi ⊢; omega)

theorem exists_circ_perm_zmod_of_checkCyclePrime
    (p : ℕ) [Fact p.Prime] (hp7 : 7 < p) (a0 g : ℕ) (ps : List ℕ) (packed : List (ℕ × ℕ))
    (hps_cov : ∀ r, r.Prime → r ∣ (p - 1) → r ∈ ps)
    (hp_small : p - 1 < 2 ^ 16)
    (hcheck : checkCyclePrime p a0 g ps packed = true) :
    ∃ a : Fin (p - 1) ≃ (ZMod p)ˣ,
      ∀ i : Fin (p - 1),
        IsPrimitiveRoot ((a i : ZMod p) * (a ⟨(i.val + 1) % (p - 1), Nat.mod_lt _ (by omega)⟩ : ZMod p) + (a0 : ZMod p)) (p - 1) := by
  have hp : p.Prime := Fact.out
  unfold checkCyclePrime at hcheck
  set cyc := unpackCycle p packed
  cases hcyc : cyc with
  | nil => simp [hcyc] at hcheck
  | cons first rest =>
    rw [hcyc] at hcheck
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hcheck
    obtain ⟨⟨hg0, hg_exps⟩, hwalk⟩ := hcheck
    have hg_ne0 : (g : ZMod p) ≠ 0 := by
      intro h0
      rw [ZMod.natCast_eq_zero_iff] at h0
      exact hg0 (Nat.dvd_iff_mod_eq_zero.mp h0)
    have hg_prim : IsPrimitiveRoot (g : ZMod p) (p - 1) := by
      have hcard_u : Fintype.card (ZMod p)ˣ = p - 1 := by rw [Fintype.card_units, ZMod.card]
      let gu : (ZMod p)ˣ := Units.mk0 (g : ZMod p) hg_ne0
      have hpow1 : (g : ZMod p) ^ (p - 1) = 1 := by
        have : gu ^ (p - 1) = 1 := hcard_u ▸ pow_card_eq_one
        simpa [gu] using congrArg Units.val this
      rw [IsPrimitiveRoot.iff_def]
      refine ⟨hpow1, fun l hl => ?_⟩
      have hord_dvd : orderOf gu ∣ p - 1 := hcard_u ▸ orderOf_dvd_card
      have hord_eq : orderOf gu = p - 1 := by
        by_contra hne
        obtain ⟨q, hq⟩ := hord_dvd
        have hq_ne1 : q ≠ 1 := by intro h; subst h; rw [mul_one] at hq; exact hne hq.symm
        obtain ⟨r, hr_prime, hr_dvd_q⟩ := Nat.exists_prime_and_dvd hq_ne1
        have hr_dvd : r ∣ p - 1 := hr_dvd_q.trans ⟨orderOf gu, by linarith⟩
        have hr_mem : r ∈ ps := hps_cov r hr_prime hr_dvd
        have hord_dvd_div : orderOf gu ∣ (p - 1) / r := by
          obtain ⟨t, ht⟩ := hr_dvd_q
          refine ⟨t, ?_⟩
          have : (p - 1) / r = orderOf gu * t := by
            rw [hq, ht, show orderOf gu * (r * t) = r * (orderOf gu * t) by ring,
              Nat.mul_div_right _ hr_prime.pos]
          exact this
        have hgu_div : gu ^ ((p - 1) / r) = 1 := orderOf_dvd_iff_pow_eq_one.mp hord_dvd_div
        have hg_div : ((g ^ ((p - 1) / r) : ℕ) : ZMod p) = 1 := by
          have := congrArg Units.val hgu_div; simpa [gu] using this
        have hmod1 : g ^ ((p - 1) / r) % p = 1 := by
          have h1 : (((g ^ ((p - 1) / r) % p : ℕ) : ZMod p)) = (1 : ZMod p) := by
            rw [ZMod.natCast_mod]; exact hg_div
          have h2 := congrArg ZMod.val h1
          rw [ZMod.val_natCast_of_lt (Nat.mod_lt _ hp.pos), ZMod.val_one] at h2
          exact h2
        have hall := List.all_eq_true.mp hg_exps ((p - 1) / r) (List.mem_map.mpr ⟨r, hr_mem, rfl⟩)
        simp only [bne_iff_ne, ne_eq] at hall
        have hlt16 : (p - 1) / r < 2 ^ 16 := lt_of_le_of_lt (Nat.div_le_self _ _) hp_small
        rw [powMod_eq hlt16] at hall
        exact hall hmod1
      have hgu_l : gu ^ l = 1 := Units.ext (by simpa [gu] using hl)
      rw [← hord_eq]
      exact orderOf_dvd_of_pow_eq_one hgu_l
    have hpm_prim : ∀ z : ℕ, (buildPrimMask p g ps).testBit z = true → IsPrimitiveRoot (z : ZMod p) (p - 1) := by
      intro z hz
      obtain ⟨t, hcop_ps, ht⟩ := testBit_buildPrimMaskAux (p - 1) 1 (g % p) 0 z
        (fun _ h => by simp at h) (by simp) hz
      have hcop : Nat.Coprime t (p - 1) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hne
        exact hcop_ps r (hps_cov r hr_prime (hr_dvd.trans (Nat.gcd_dvd_right _ _)))
          (hr_dvd.trans (Nat.gcd_dvd_left _ _))
      have hz_eq : (z : ZMod p) = (g : ZMod p) ^ t := by
        rw [← ht, ZMod.natCast_mod, Nat.cast_pow]
      rw [hz_eq]
      exact hg_prim.pow_of_coprime t hcop
    have ⟨hlen, hcov, hadj, hlast⟩ :=
      checkWalkPrime_sound (by omega : 2 ≤ p) (first :: rest) 0 0 (List.cons_ne_nil _ _) hwalk
    simp only [zero_add, Nat.zero_testBit, Bool.false_eq_true, false_or] at hlen hcov
    let f : Fin (p - 1) → (ZMod p)ˣ := fun i =>
      let v := (first :: rest)[i.val]'(by omega)
      have hv_rng : 1 ≤ v ∧ v < p := (hcov v).mp (List.getElem_mem _)
      Units.mk0 (v : ZMod p) (by
        intro h0; rw [ZMod.natCast_eq_zero_iff] at h0
        have := Nat.le_of_dvd (by omega) h0; omega)
    have hf_surj : Function.Surjective f := by
      intro u
      have hu_lt : u.1.val < p := ZMod.val_lt u.1
      have hu_pos : 1 ≤ u.1.val := by
        by_contra h0
        have : u.1.val = 0 := by omega
        exact u.ne_zero ((ZMod.val_eq_zero u.1).mp this)
      have hmem : u.1.val ∈ first :: rest := (hcov u.1.val).mpr ⟨hu_pos, hu_lt⟩
      obtain ⟨idx, hidx, hget⟩ := List.getElem_of_mem hmem
      refine ⟨⟨idx, by omega⟩, Units.ext ?_⟩
      simp [f, hget]
    have hf_bij : Function.Bijective f :=
      (Fintype.bijective_iff_surjective_and_card f).mpr ⟨hf_surj, by rw [Fintype.card_fin, Fintype.card_units, ZMod.card]⟩
    refine ⟨Equiv.ofBijective f hf_bij, fun i => ?_⟩
    simp only [Equiv.ofBijective_apply]
    by_cases hi : i.val + 1 < p - 1
    · have hmod : (i.val + 1) % (p - 1) = i.val + 1 := Nat.mod_eq_of_lt hi
      have hbit := hadj i.val (by omega)
      have hprim := hpm_prim _ hbit
      simpa [f, hmod, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul] using hprim
    · have hieq : i.val = p - 2 := by omega
      have hmod : (i.val + 1) % (p - 1) = 0 := by
        rw [hieq, show p - 2 + 1 = p - 1 by omega, Nat.mod_self]
      have hprim := hpm_prim _ hlast
      have hget_last : (first :: rest)[i.val]'(by omega) = (first :: rest).getLast (List.cons_ne_nil _ _) := by
        rw [List.getLast_eq_getElem]; congr 1; omega
      have hget_zero : (first :: rest)[0]'(by omega) = first := rfl
      simpa [f, hmod, hget_last, hget_zero, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul] using hprim

end CycleSoundness

section QuadAndGF16GF27

/-- Exact `GF(16)` theorem for ANY finite field of cardinality 16 (zero `AdjoinRoot`!). -/
theorem exists_circ_perm_gf16 {F : Type*} [Field F] [Fintype F] (h16 : Fintype.card F = 16) :
    ∃ a : Fin 15 ≃ Fˣ,
      ∀ i : Fin 15,
        IsPrimitiveRoot ((a i : F) * (a ⟨(i.val + 1) % 15, Nat.mod_lt _ (by norm_num)⟩ : F) - 1) 15 := by
  classical
  have hchar2 : (2 : F) = 0 := by
    obtain ⟨p, hcp, n, hp, hcard⟩ := FiniteField.card' F
    have hd2 : 2 ∣ p ^ (n : ℕ) := by rw [← hcard, h16]; decide
    have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.Prime.dvd_of_dvd_pow Nat.prime_two hd2)).symm
    subst hp2; exact CharP.cast_eq_zero F 2
  have hadd_self : ∀ x : F, x + x = 0 := fun x => by
    have : x + x = (2 : F) * x := by ring
    rw [this, hchar2, zero_mul]
  have hsub_eq_add : ∀ x y : F, x - y = x + y := fun x y => by
    have : x - y - (x + y) = -(2 : F) * y := by ring
    rw [hchar2, neg_zero, zero_mul] at this
    exact eq_of_sub_eq_zero this
  have hcard_u : Fintype.card Fˣ = 15 := by rw [Fintype.card_units, h16]
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord0 : orderOf g₀ = 15 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg₀, Nat.card_eq_fintype_card, hcard_u]
  have hg0_prim : IsPrimitiveRoot (g₀ : F) 15 := by
    rw [IsPrimitiveRoot.iff_def]
    have hg0_pow : g₀ ^ 15 = 1 := by rw [← hcard_u]; exact pow_card_eq_one
    refine ⟨by simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hg0_pow, fun l hl => ?_⟩
    rw [← hord0]; exact orderOf_dvd_of_pow_eq_one (Units.ext (by simpa using hl))
  have hfac : ((g₀ : F) ^ 4 + g₀ + 1) * ((g₀ : F) ^ 4 + g₀ ^ 3 + 1) *
      ((g₀ : F) ^ 4 + g₀ ^ 3 + g₀ ^ 2 + g₀ + 1) * ((g₀ : F) ^ 2 + g₀ + 1) * ((g₀ : F) + 1) = 0 := by
    have h15 : (g₀ : F) ^ 15 = 1 := hg0_prim.pow_eq_one
    have hpoly : ((g₀ : F) ^ 4 + g₀ + 1) * ((g₀ : F) ^ 4 + g₀ ^ 3 + 1) *
        ((g₀ : F) ^ 4 + g₀ ^ 3 + g₀ ^ 2 + g₀ + 1) * ((g₀ : F) ^ 2 + g₀ + 1) * ((g₀ : F) + 1) =
        ((g₀ : F) ^ 15 + 1) + (2 : F) * (2 * (g₀ : F) ^ 14 + 4 * (g₀ : F) ^ 13 + 6 * (g₀ : F) ^ 12 +
          9 * (g₀ : F) ^ 11 + 13 * (g₀ : F) ^ 10 + 16 * (g₀ : F) ^ 9 + 17 * (g₀ : F) ^ 8 +
          17 * (g₀ : F) ^ 7 + 16 * (g₀ : F) ^ 6 + 13 * (g₀ : F) ^ 5 + 9 * (g₀ : F) ^ 4 +
          6 * (g₀ : F) ^ 3 + 4 * (g₀ : F) ^ 2 + 2 * (g₀ : F)) := by ring
    rw [hpoly, h15, hchar2, zero_mul, add_zero, hadd_self]
  have hne1 : (g₀ : F) + 1 ≠ 0 := by
    intro h
    have h1 : (g₀ : F) ^ 1 = 1 := by
      have : (g₀ : F) = 1 := by linear_combination h - hadd_self 1
      simpa using this
    have := hg0_prim.dvd_of_pow_eq_one 1 h1; omega
  have hne3 : (g₀ : F) ^ 2 + g₀ + 1 ≠ 0 := by
    intro h
    have h3 : (g₀ : F) ^ 3 = 1 := by
      have : (g₀ : F) ^ 3 - 1 = ((g₀ : F) - 1) * ((g₀ : F) ^ 2 + g₀ + 1) := by ring
      rw [h, mul_zero] at this; exact eq_of_sub_eq_zero this
    have := hg0_prim.dvd_of_pow_eq_one 3 h3; omega
  have hne5 : (g₀ : F) ^ 4 + g₀ ^ 3 + g₀ ^ 2 + g₀ + 1 ≠ 0 := by
    intro h
    have h5 : (g₀ : F) ^ 5 = 1 := by
      have : (g₀ : F) ^ 5 - 1 = ((g₀ : F) - 1) * ((g₀ : F) ^ 4 + g₀ ^ 3 + g₀ ^ 2 + g₀ + 1) := by ring
      rw [h, mul_zero] at this; exact eq_of_sub_eq_zero this
    have := hg0_prim.dvd_of_pow_eq_one 5 h5; omega
  obtain ⟨g, hg_prim, hg4⟩ : ∃ g : Fˣ, IsPrimitiveRoot (g : F) 15 ∧ (g : F) ^ 4 = (g : F) + 1 := by
    rcases mul_eq_zero.mp hfac with h1 | h0
    · rcases mul_eq_zero.mp h1 with h2 | h0
      · rcases mul_eq_zero.mp h2 with h3 | h0
        · rcases mul_eq_zero.mp h3 with h4a | h4b
          · refine ⟨g₀, hg0_prim, ?_⟩
            linear_combination h4a - hadd_self ((g₀ : F) + 1)
          · refine ⟨g₀⁻¹, ?_, ?_⟩
            · have : ((g₀⁻¹ : Fˣ) : F) = (g₀ : F) ^ 14 := by
                have h15 : (g₀ : F) ^ 15 = 1 := hg0_prim.pow_eq_one
                apply mul_left_cancel₀ g₀.ne_zero
                rw [Units.val_inv_eq_inv_val, mul_inv_cancel₀ g₀.ne_zero, ← pow_succ', h15]
              rw [this]; exact hg0_prim.pow_of_coprime 14 (by decide)
            · have hmul : (g₀ : F) ^ 4 * (((g₀⁻¹ : Fˣ) : F) ^ 4 - ((g₀⁻¹ : Fˣ) : F) - 1) =
                  1 - (g₀ : F) ^ 3 - (g₀ : F) ^ 4 := by
                rw [Units.val_inv_eq_inv_val]; field_simp [g₀.ne_zero]
              have hzero : 1 - (g₀ : F) ^ 3 - (g₀ : F) ^ 4 = 0 := by
                rw [hsub_eq_add, hsub_eq_add]; linear_combination h4b
              rw [hzero] at hmul
              have h0' := (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 4 g₀.ne_zero)
              have h1' := eq_of_sub_eq_zero h0'
              linear_combination h1'
        · exact absurd h0 hne5
      · exact absurd h0 hne3
    · exact absurd h0 hne1
  have hg15 : (g : F) ^ 15 = 1 := hg_prim.pow_eq_one
  have hg1 : (g : F) + 1 = (g : F) ^ 4 := hg4.symm
  have hg2 : (g : F) ^ 2 + 1 = (g : F) ^ 8 := by
    have : (g : F) ^ 8 = ((g : F) ^ 4) ^ 2 := by ring
    rw [this, hg4]; linear_combination -hadd_self (g : F)
  have hg3 : (g : F) ^ 3 + 1 = (g : F) ^ 14 := by
    apply mul_left_cancel₀ g.ne_zero
    linear_combination hg4 + (g : F) * hchar2 - hg15
  have hg4' : (g : F) ^ 4 + 1 = (g : F) ^ 1 := by
    rw [pow_one, hg4]; linear_combination hadd_self (1 : F)
  have hg6 : (g : F) ^ 6 + 1 = (g : F) ^ 13 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 g.ne_zero)
    linear_combination -hg2 + (g : F) ^ 2 * hchar2 - hg15
  have hg8 : (g : F) ^ 8 + 1 = (g : F) ^ 2 := by
    rw [← hg2]; linear_combination hadd_self (1 : F)
  have hg9 : (g : F) ^ 9 + 1 = (g : F) ^ 7 := by
    apply mul_left_cancel₀ (pow_ne_zero 8 g.ne_zero)
    have h17 : (g : F) ^ 17 = (g : F) ^ 2 := by rw [show (17 : ℕ) = 15 + 2 by rfl, pow_add, hg15, one_mul]
    linear_combination h17 - hg2 + (g : F) ^ 2 * hchar2 - hg15
  have hg12 : (g : F) ^ 12 + 1 = (g : F) ^ 11 := by
    apply mul_left_cancel₀ (pow_ne_zero 4 g.ne_zero)
    have h16' : (g : F) ^ 16 = (g : F) := by rw [show (16 : ℕ) = 15 + 1 by rfl, pow_add, hg15, one_mul, pow_one]
    linear_combination h16' + hg4 + (g : F) * hchar2 - hg15
  let exps : Fin 15 → Fin 15 :=
    ![0, 1, 2, 4, 5, 3, 6, 10, 7, 9, 14, 13, 8, 11, 12]
  have hexps_bij : Function.Bijective exps := by
    refine (Fintype.bijective_iff_injective_and_card exps).mpr ⟨?_, rfl⟩
    decide
  let f : Fin 15 → Fˣ := fun i => g ^ (exps i).val
  have hf_inj : Function.Injective f := by
    intro i j hij
    have hval : (g : F) ^ (exps i).val = (g : F) ^ (exps j).val := by
      simpa [f] using congrArg Units.val hij
    have heq : (exps i).val = (exps j).val :=
      hg_prim.injOn_pow (Finset.mem_coe.mpr (Finset.mem_range.mpr (exps i).isLt))
        (Finset.mem_coe.mpr (Finset.mem_range.mpr (exps j).isLt)) hval
    exact hexps_bij.1 (Fin.ext heq)
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, by rw [Fintype.card_fin, hcard_u]⟩
  refine ⟨Equiv.ofBijective f hf_bij, fun i => ?_⟩
  simp only [Equiv.ofBijective_apply, f, Units.val_pow_eq_pow_val, ← pow_add, hsub_eq_add]
  have hmod15 : ∀ k : ℕ, (g : F) ^ k = (g : F) ^ (k % 15) := fun k => by
    conv_lhs => rw [← Nat.div_add_mod k 15, pow_add, pow_mul, hg15, one_pow, one_mul]
  rw [hmod15]
  fin_cases i <;>
    first
    | (simp [exps]; rw [hg1]; exact hg_prim.pow_of_coprime 4 (by decide))
    | (simp [exps]; rw [hg2]; exact hg_prim.pow_of_coprime 8 (by decide))
    | (simp [exps]; rw [hg3]; exact hg_prim.pow_of_coprime 14 (by decide))
    | (simp [exps]; rw [hg4']; exact hg_prim.pow_of_coprime 1 (by decide))
    | (simp [exps]; rw [hg6]; exact hg_prim.pow_of_coprime 13 (by decide))
    | (simp [exps]; rw [hg8]; exact hg_prim.pow_of_coprime 2 (by decide))
    | (simp [exps]; rw [hg9]; exact hg_prim.pow_of_coprime 7 (by decide))
    | (simp [exps]; rw [hg12]; exact hg_prim.pow_of_coprime 11 (by decide))

/-- Helper for `GF(27)`: extract primitive root `g : Fˣ` satisfying `g^3 - g + 1 = 0`, `g^13 = -1`, `3 = 0`. -/
lemma exists_prim_root_gf27 {F : Type*} [Field F] [Fintype F] (h27 : Fintype.card F = 27) :
    ∃ g : Fˣ, IsPrimitiveRoot (g : F) 26 ∧ (g : F) ^ 3 - (g : F) + 1 = 0 ∧ (g : F) ^ 13 = -1 ∧ (3 : F) = 0 := by
  classical
  have hchar3 : (3 : F) = 0 := by
    obtain ⟨p, hcp, n, hp, hcard⟩ := FiniteField.card' F
    have hd3 : 3 ∣ p ^ (n : ℕ) := by rw [← hcard, h27]; decide
    have hp3 : p = 3 := ((Nat.prime_dvd_prime_iff_eq (by decide) hp).mp (Nat.Prime.dvd_of_dvd_pow (by decide) hd3)).symm
    subst hp3; exact CharP.cast_eq_zero F 3
  have hcard_u : Fintype.card Fˣ = 26 := by rw [Fintype.card_units, h27]
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord0 : orderOf g₀ = 26 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg₀, Nat.card_eq_fintype_card, hcard_u]
  have hg0_prim : IsPrimitiveRoot (g₀ : F) 26 := by
    rw [IsPrimitiveRoot.iff_def]
    have hg0_pow : g₀ ^ 26 = 1 := by rw [← hcard_u]; exact pow_card_eq_one
    refine ⟨by simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hg0_pow, fun l hl => ?_⟩
    rw [← hord0]; exact orderOf_dvd_of_pow_eq_one (Units.ext (by simpa using hl))
  have hg0_13 : (g₀ : F) ^ 13 = -1 := by
    have hsq : ((g₀ : F) ^ 13) ^ 2 = 1 := by rw [← pow_mul]; exact hg0_prim.pow_eq_one
    have hne1 : (g₀ : F) ^ 13 ≠ 1 := fun h => by have := hg0_prim.dvd_of_pow_eq_one 13 h; omega
    exact (sq_eq_one_iff.mp hsq).resolve_left hne1
  have hne_m1 : (g₀ : F) + 1 ≠ 0 := by
    intro h
    have h2 : (g₀ : F) ^ 2 = 1 := by
      have : (g₀ : F) = -1 := eq_neg_of_add_eq_zero_left h
      rw [this]; ring
    have := hg0_prim.dvd_of_pow_eq_one 2 h2; omega
  -- Exact factorization of x^13 + 1 over F_3 into (x + 1) and the 4 primitive cubics!
  let x : F := (g₀ : F)
  have hfac : (x ^ 3 - x + 1) * (x ^ 3 - x ^ 2 + x + 1) *
      (x ^ 3 + x ^ 2 - x + 1) * (x ^ 3 - x ^ 2 + 1) * (x + 1) = 0 := by
    have hpoly : (x ^ 3 - x + 1) * (x ^ 3 - x ^ 2 + x + 1) *
        (x ^ 3 + x ^ 2 - x + 1) * (x ^ 3 - x ^ 2 + 1) * (x + 1) =
        (x ^ 13 + 1) + (3 : F) * (-x ^ 11 + 2 * x ^ 10 + x ^ 9 - 4 * x ^ 8 +
          3 * x ^ 7 + 3 * x ^ 6 - 4 * x ^ 5 + x ^ 4 + 2 * x ^ 3 - x ^ 2) := by ring
    rw [hpoly, hchar3, zero_mul, add_zero]
    dsimp [x]; rw [hg0_13]; ring
  have h13_of_prim : ∀ g : Fˣ, IsPrimitiveRoot (g : F) 26 → (g : F) ^ 13 = -1 := fun g hg => by
    have hsq : ((g : F) ^ 13) ^ 2 = 1 := by rw [← pow_mul]; exact hg.pow_eq_one
    have hne1 : (g : F) ^ 13 ≠ 1 := fun h => by have := hg.dvd_of_pow_eq_one 13 h; omega
    exact (sq_eq_one_iff.mp hsq).resolve_left hne1
  rcases mul_eq_zero.mp hfac with h1 | h0
  · rcases mul_eq_zero.mp h1 with h2 | hc4
    · rcases mul_eq_zero.mp h2 with h3 | hc3
      · rcases mul_eq_zero.mp h3 with hc1 | hc2
        · exact ⟨g₀, hg0_prim, hc1, hg0_13, hchar3⟩
        · -- Root of x^3 - x^2 + x + 1: take g = g₀^7!
          have hp7 : IsPrimitiveRoot ((g₀ ^ 7 : Fˣ) : F) 26 := by
            rw [Units.val_pow_eq_pow_val]; exact hg0_prim.pow_of_coprime 7 (by decide)
          refine ⟨g₀ ^ 7, hp7, ?_, h13_of_prim _ hp7, hchar3⟩
          rw [Units.val_pow_eq_pow_val]
          change (x ^ 7) ^ 3 - x ^ 7 + 1 = 0
          linear_combination
            (x ^ 18 + x ^ 17 + x ^ 15 - x ^ 13 + x ^ 12 - x ^ 11 - x ^ 10 - x ^ 9 + x ^ 8 -
              x ^ 5 + x ^ 4 - x ^ 3 - x ^ 2 - x + 1) * hc2 +
            (-x ^ 18 - x ^ 15 + x ^ 14 + x ^ 10 - x ^ 7 + x ^ 6 + x ^ 2) * hchar3
      · -- Root of x^3 + x^2 - x + 1: take g = g₀^5!
        have hp5 : IsPrimitiveRoot ((g₀ ^ 5 : Fˣ) : F) 26 := by
          rw [Units.val_pow_eq_pow_val]; exact hg0_prim.pow_of_coprime 5 (by decide)
        refine ⟨g₀ ^ 5, hp5, ?_, h13_of_prim _ hp5, hchar3⟩
        rw [Units.val_pow_eq_pow_val]
        change (x ^ 5) ^ 3 - x ^ 5 + 1 = 0
        linear_combination
          (x ^ 12 - x ^ 11 - x ^ 10 - x ^ 9 + x ^ 8 - x ^ 7 + x ^ 5 + x ^ 3 + x + 1) * hc3 +
          (x ^ 13 + x ^ 9 - x ^ 8 - x ^ 5 - x ^ 3) * hchar3
    · -- Root of x^3 - x^2 + 1: take g = g₀⁻¹!
      have hp_inv : IsPrimitiveRoot ((g₀⁻¹ : Fˣ) : F) 26 := by
        have : ((g₀⁻¹ : Fˣ) : F) = (g₀ : F) ^ 25 := by
          have h26 : (g₀ : F) ^ 26 = 1 := hg0_prim.pow_eq_one
          apply mul_left_cancel₀ g₀.ne_zero
          rw [Units.val_inv_eq_inv_val, mul_inv_cancel₀ g₀.ne_zero, ← pow_succ', h26]
        rw [this]; exact hg0_prim.pow_of_coprime 25 (by decide)
      refine ⟨g₀⁻¹, hp_inv, ?_, h13_of_prim _ hp_inv, hchar3⟩
      have hmul : x ^ 3 * (((g₀⁻¹ : Fˣ) : F) ^ 3 - ((g₀⁻¹ : Fˣ) : F) + 1) = x ^ 3 - x ^ 2 + 1 := by
        dsimp [x]; rw [Units.val_inv_eq_inv_val]; field_simp [g₀.ne_zero]; ring
      rw [hc4] at hmul
      exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 3 g₀.ne_zero)
  · exact absurd h0 hne_m1

/-- Exact `GF(27)` theorem for `a₀ = -1` (ANY finite field of cardinality 27, zero `AdjoinRoot`!). -/
theorem exists_circ_perm_gf27_minus {F : Type*} [Field F] [Fintype F] (h27 : Fintype.card F = 27) :
    ∃ a : Fin 26 ≃ Fˣ,
      ∀ i : Fin 26,
        IsPrimitiveRoot ((a i : F) * (a ⟨(i.val + 1) % 26, Nat.mod_lt _ (by norm_num)⟩ : F) - 1) 26 := by
  classical
  have hcard_u : Fintype.card Fˣ = 26 := by rw [Fintype.card_units, h27]
  obtain ⟨g, hg_prim, hg3, hg13, hchar3⟩ := exists_prim_root_gf27 h27
  have hg26 : (g : F) ^ 26 = 1 := hg_prim.pow_eq_one
  have hred : ∀ k : ℕ, (g : F) ^ (k + 13) = -((g : F) ^ k) := fun k => by
    rw [pow_add, hg13]; ring
  set x : F := (g : F)
  have hm1_1 : x - 1 = x ^ 3 := by linear_combination -hg3
  have hm1_3 : x ^ 3 - 1 = x ^ 9 := by
    linear_combination (-x ^ 6 - x ^ 4 + x ^ 3 - x ^ 2 - x - 1) * hg3 + x ^ 4 * hchar3
  have hm1_4 : x ^ 4 - 1 = x ^ 7 := by
    linear_combination (-x ^ 4 - x ^ 2 - x - 1) * hg3 + x ^ 4 * hchar3
  have hm1_8 : x ^ 8 - 1 = x ^ 25 := by
    have h25 : x ^ 25 = -(x ^ 12) := hred 12
    rw [h25]
    linear_combination (x ^ 9 + x ^ 7 - x ^ 6 - x ^ 5 + x ^ 4 - x ^ 2 - x - 1) * hg3 + (x ^ 8 - x ^ 7 + x ^ 5) * hchar3
  have hm1_9 : x ^ 9 - 1 = x ^ 1 := by
    linear_combination (x ^ 6 + x ^ 4 - x ^ 3 + x ^ 2 + x - 1) * hg3 + (-x ^ 4 + x ^ 3 - x) * hchar3
  have hm1_10 : x ^ 10 - 1 = x ^ 11 := by
    linear_combination (-x ^ 8 + x ^ 7 - x ^ 6 - x ^ 5 + x ^ 4 - x ^ 2 - x - 1) * hg3 + (x ^ 8 - x ^ 7 + x ^ 5) * hchar3
  have hm1_12 : x ^ 12 - 1 = x ^ 21 := by
    have h21 : x ^ 21 = -(x ^ 8) := hred 8
    rw [h21]
    linear_combination (x ^ 9 + x ^ 7 - x ^ 6 - x ^ 5 + x ^ 4 - x ^ 2 - x - 1) * hg3 + (x ^ 8 - x ^ 7 + x ^ 5) * hchar3
  have hm1_20 : x ^ 20 - 1 = x ^ 17 := by
    have h20 : x ^ 20 = -(x ^ 7) := hred 7
    have h17 : x ^ 17 = -(x ^ 4) := hred 4
    rw [h20, h17]
    linear_combination (-x ^ 4 - x ^ 2 - x - 1) * hg3 + x ^ 4 * hchar3
  have hm1_23 : x ^ 23 - 1 = x ^ 19 := by
    have h23 : x ^ 23 = -(x ^ 10) := hred 10
    have h19 : x ^ 19 = -(x ^ 6) := hred 6
    rw [h23, h19]
    linear_combination (-x ^ 7 - x ^ 5 + x ^ 4 - x ^ 2 - x - 1) * hg3 + x ^ 5 * hchar3
  have hm1_24 : x ^ 24 - 1 = x ^ 23 := by
    have h24 : x ^ 24 = -(x ^ 11) := hred 11
    have h23 : x ^ 23 = -(x ^ 10) := hred 10
    rw [h24, h23]
    linear_combination (-x ^ 8 + x ^ 7 - x ^ 6 - x ^ 5 + x ^ 4 - x ^ 2 - x - 1) * hg3 + (x ^ 8 - x ^ 7 + x ^ 5) * hchar3
  have hm1_25 : x ^ 25 - 1 = x ^ 15 := by
    have h25 : x ^ 25 = -(x ^ 12) := hred 12
    have h15 : x ^ 15 = -(x ^ 2) := hred 2
    rw [h25, h15]
    linear_combination (-x ^ 9 - x ^ 7 + x ^ 6 - x ^ 5 - x ^ 4 + x ^ 3 - x - 1) * hg3 + (x ^ 7 - x ^ 6 + x ^ 4) * hchar3
  let exps : Fin 26 → Fin 26 :=
    ![0, 4, 23, 6, 2, 25, 10, 13, 17, 21, 8, 12, 15, 19, 5, 18, 7, 20, 3, 9, 1, 11, 16, 14, 22, 24]
  have hexps_bij : Function.Bijective exps := by
    refine (Fintype.bijective_iff_injective_and_card exps).mpr ⟨?_, rfl⟩
    decide
  let f : Fin 26 → Fˣ := fun i => g ^ (exps i).val
  have hf_inj : Function.Injective f := by
    intro i j hij
    have hval : (g : F) ^ (exps i).val = (g : F) ^ (exps j).val := by
      simpa [f] using congrArg Units.val hij
    exact hexps_bij.1 (Fin.ext (hg_prim.injOn_pow
      (Finset.mem_coe.mpr (Finset.mem_range.mpr (exps i).isLt))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr (exps j).isLt)) hval))
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, by rw [Fintype.card_fin, hcard_u]⟩
  refine ⟨Equiv.ofBijective f hf_bij, fun i => ?_⟩
  simp only [Equiv.ofBijective_apply, f, Units.val_pow_eq_pow_val, ← pow_add]
  have hmod26 : ∀ k : ℕ, (g : F) ^ k = x ^ (k % 26) := fun k => by
    conv_lhs => rw [← Nat.div_add_mod k 26, pow_add, pow_mul, hg26, one_pow, one_mul]
  rw [hmod26]
  fin_cases i <;>
    first
    | (simp [exps]; rw [hm1_1]; exact hg_prim.pow_of_coprime 3 (by decide))
    | (simp [exps]; rw [hm1_3]; exact hg_prim.pow_of_coprime 9 (by decide))
    | (simp [exps]; rw [hm1_4]; exact hg_prim.pow_of_coprime 7 (by decide))
    | (simp [exps]; rw [hm1_8]; exact hg_prim.pow_of_coprime 25 (by decide))
    | (simp [exps]; rw [hm1_9]; exact hg_prim.pow_of_coprime 1 (by decide))
    | (simp [exps]; rw [hm1_10]; exact hg_prim.pow_of_coprime 11 (by decide))
    | (simp [exps]; rw [hm1_12]; exact hg_prim.pow_of_coprime 21 (by decide))
    | (simp [exps]; rw [hm1_20]; exact hg_prim.pow_of_coprime 17 (by decide))
    | (simp [exps]; rw [hm1_23]; exact hg_prim.pow_of_coprime 19 (by decide))
    | (simp [exps]; rw [hm1_24]; exact hg_prim.pow_of_coprime 23 (by decide))
    | (simp [exps]; rw [hm1_25]; exact hg_prim.pow_of_coprime 15 (by decide))

/-- Exact `GF(27)` theorem for `a₀ = +1` (ANY finite field of cardinality 27, zero `AdjoinRoot`!). -/
theorem exists_circ_perm_gf27_plus {F : Type*} [Field F] [Fintype F] (h27 : Fintype.card F = 27) :
    ∃ a : Fin 26 ≃ Fˣ,
      ∀ i : Fin 26,
        IsPrimitiveRoot ((a i : F) * (a ⟨(i.val + 1) % 26, Nat.mod_lt _ (by norm_num)⟩ : F) + 1) 26 := by
  classical
  have hcard_u : Fintype.card Fˣ = 26 := by rw [Fintype.card_units, h27]
  obtain ⟨g, hg_prim, hg3, hg13, hchar3⟩ := exists_prim_root_gf27 h27
  have hg26 : (g : F) ^ 26 = 1 := hg_prim.pow_eq_one
  have hred : ∀ k : ℕ, (g : F) ^ (k + 13) = -((g : F) ^ k) := fun k => by
    rw [pow_add, hg13]; ring
  set x : F := (g : F)
  have hp1_1 : x + 1 = x ^ 9 := by
    linear_combination (-x ^ 6 - x ^ 4 + x ^ 3 - x ^ 2 - x + 1) * hg3 + (x ^ 4 - x ^ 3 + x) * hchar3
  have hp1_2 : x ^ 2 + 1 = x ^ 21 := by
    have h21 : x ^ 21 = -(x ^ 8) := hred 8
    rw [h21]
    linear_combination (x ^ 5 + x ^ 3 - x ^ 2 + x + 1) * hg3 + (-x ^ 3 + x ^ 2) * hchar3
  have hp1_3 : x ^ 3 + 1 = x ^ 1 := by linear_combination hg3
  have hp1_5 : x ^ 5 + 1 = x ^ 17 := by
    have h17 : x ^ 17 = -(x ^ 4) := hred 4
    rw [h17]
    linear_combination (x ^ 2 + x + 1) * hg3
  have hp1_6 : x ^ 6 + 1 = x ^ 11 := by
    linear_combination (-x ^ 8 - x ^ 6 + x ^ 5 - x ^ 4 + x ^ 2 + x + 1) * hg3 + (x ^ 6 - x ^ 5) * hchar3
  have hp1_9 : x ^ 9 + 1 = x ^ 3 := by
    linear_combination (x ^ 6 + x ^ 4 - x ^ 3 + x ^ 2 + x + 1) * hg3 + (-x ^ 4) * hchar3
  have hp1_15 : x ^ 15 + 1 = x ^ 25 := by
    have h15 : x ^ 15 = -(x ^ 2) := hred 2
    have h25 : x ^ 25 = -(x ^ 12) := hred 12
    rw [h15, h25]
    linear_combination (x ^ 9 + x ^ 7 - x ^ 6 + x ^ 5 + x ^ 4 - x ^ 3 + x + 1) * hg3 + (-x ^ 7 + x ^ 6 - x ^ 4) * hchar3
  have hp1_18 : x ^ 18 + 1 = x ^ 7 := by
    have h18 : x ^ 18 = -(x ^ 5) := hred 5
    rw [h18]
    linear_combination (-x ^ 4 + x ^ 2 + x + 1) * hg3 + (-x ^ 5) * hchar3
  have hp1_19 : x ^ 19 + 1 = x ^ 23 := by
    have h19 : x ^ 19 = -(x ^ 6) := hred 6
    have h23 : x ^ 23 = -(x ^ 10) := hred 10
    rw [h19, h23]
    linear_combination (x ^ 7 + x ^ 5 - x ^ 4 + x ^ 2 + x + 1) * hg3 + (-x ^ 5) * hchar3
  have hp1_20 : x ^ 20 + 1 = x ^ 5 := by
    have h20 : x ^ 20 = -(x ^ 7) := hred 7
    rw [h20]
    linear_combination (-x ^ 4 + x ^ 2 + x + 1) * hg3 + (-x ^ 5) * hchar3
  have hp1_24 : x ^ 24 + 1 = x ^ 19 := by
    have h24 : x ^ 24 = -(x ^ 11) := hred 11
    have h19 : x ^ 19 = -(x ^ 6) := hred 6
    rw [h24, h19]
    linear_combination (-x ^ 8 - x ^ 6 + x ^ 5 - x ^ 4 + x ^ 2 + x + 1) * hg3 + (x ^ 6 - x ^ 5) * hchar3
  let exps : Fin 26 → Fin 26 :=
    ![0, 1, 2, 3, 17, 18, 6, 14, 4, 5, 15, 13, 16, 12, 19, 22, 23, 9, 10, 25, 7, 8, 11, 20, 21, 24]
  have hexps_bij : Function.Bijective exps := by
    refine (Fintype.bijective_iff_injective_and_card exps).mpr ⟨?_, rfl⟩
    decide
  let f : Fin 26 → Fˣ := fun i => g ^ (exps i).val
  have hf_inj : Function.Injective f := by
    intro i j hij
    have hval : (g : F) ^ (exps i).val = (g : F) ^ (exps j).val := by
      simpa [f] using congrArg Units.val hij
    exact hexps_bij.1 (Fin.ext (hg_prim.injOn_pow
      (Finset.mem_coe.mpr (Finset.mem_range.mpr (exps i).isLt))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr (exps j).isLt)) hval))
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, by rw [Fintype.card_fin, hcard_u]⟩
  refine ⟨Equiv.ofBijective f hf_bij, fun i => ?_⟩
  simp only [Equiv.ofBijective_apply, f, Units.val_pow_eq_pow_val, ← pow_add]
  have hmod26 : ∀ k : ℕ, (g : F) ^ k = x ^ (k % 26) := fun k => by
    conv_lhs => rw [← Nat.div_add_mod k 26, pow_add, pow_mul, hg26, one_pow, one_mul]
  rw [hmod26]
  fin_cases i <;>
    first
    | (simp [exps]; rw [hp1_1]; exact hg_prim.pow_of_coprime 9 (by decide))
    | (simp [exps]; rw [hp1_2]; exact hg_prim.pow_of_coprime 21 (by decide))
    | (simp [exps]; rw [hp1_3]; exact hg_prim.pow_of_coprime 1 (by decide))
    | (simp [exps]; rw [hp1_5]; exact hg_prim.pow_of_coprime 17 (by decide))
    | (simp [exps]; rw [hp1_6]; exact hg_prim.pow_of_coprime 11 (by decide))
    | (simp [exps]; rw [hp1_9]; exact hg_prim.pow_of_coprime 3 (by decide))
    | (simp [exps]; rw [hp1_15]; exact hg_prim.pow_of_coprime 25 (by decide))
    | (simp [exps]; rw [hp1_18]; exact hg_prim.pow_of_coprime 7 (by decide))
    | (simp [exps]; rw [hp1_19]; exact hg_prim.pow_of_coprime 23 (by decide))
    | (simp [exps]; rw [hp1_20]; exact hg_prim.pow_of_coprime 5 (by decide))
    | (simp [exps]; rw [hp1_24]; exact hg_prim.pow_of_coprime 19 (by decide))

/-- Decode `x < p * p` as an element of `QuadraticAlgebra (ZMod p) (d : ZMod p) 0`. -/
def decodeQuad (p d : ℕ) (x : ℕ) : QuadraticAlgebra (ZMod p) (d : ZMod p) 0 :=
  ⟨(x % p : ZMod p), (x / p : ZMod p)⟩

lemma decodeQuad_mul {p : ℕ} (hp : 0 < p) (d x y : ℕ) :
    decodeQuad p d (qMul p d x y) = decodeQuad p d x * decodeQuad p d y := by
  ext
  · simp only [decodeQuad, qMul, QuadraticAlgebra.re_mul]
    rw [Nat.add_mul_mod_self_right, Nat.mod_mod]
    simp only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]
  · simp only [decodeQuad, qMul, QuadraticAlgebra.im_mul]
    have hlt : (x % p * (y % p) + d * (x / p) % p * (y / p)) % p < p := Nat.mod_lt _ hp
    rw [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hlt, zero_add]
    simp only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]
    ring

lemma decodeQuad_add' {p : ℕ} (hp : 0 < p) (d x y : ℕ) :
    decodeQuad p d (qAdd p x y) = decodeQuad p d x + decodeQuad p d y := by
  ext
  · simp only [decodeQuad, qAdd, QuadraticAlgebra.re_add]
    rw [Nat.add_mul_mod_self_right, Nat.mod_mod, ZMod.natCast_mod, Nat.cast_add]
  · simp only [decodeQuad, qAdd, QuadraticAlgebra.im_add]
    have hlt : (x % p + y % p) % p < p := Nat.mod_lt _ hp
    rw [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hlt, zero_add, ZMod.natCast_mod, Nat.cast_add]

lemma decodeQuad_one {p : ℕ} (hp : 1 < p) (d : ℕ) :
    decodeQuad p d 1 = 1 := by
  ext
  · simp only [decodeQuad, Nat.mod_eq_of_lt hp, Nat.cast_one]; rfl
  · simp only [decodeQuad, Nat.div_eq_of_lt hp, Nat.cast_zero]; rfl

lemma decodeQuad_qPowAux {p : ℕ} (hp : 1 < p) (d : ℕ) :
    ∀ (fuel b e acc : ℕ), e < 2 ^ fuel →
      decodeQuad p d (qPowAux p d fuel b e acc) = decodeQuad p d acc * (decodeQuad p d b) ^ e
  | 0, b, e, acc, he => by
    have : e = 0 := by omega
    subst this; simp [qPowAux]
  | fuel + 1, b, e, acc, he => by
    unfold qPowAux
    by_cases he0 : e = 0
    · subst he0; simp
    · simp only [beq_iff_eq, he0, ↓reduceIte]
      have hdiv : e / 2 < 2 ^ fuel := by rw [pow_succ'] at he; omega
      have hp0 : 0 < p := Nat.zero_lt_of_lt hp
      rw [decodeQuad_qPowAux hp d fuel (qMul p d b b) (e / 2) _ hdiv, decodeQuad_mul hp0]
      by_cases hodd : e % 2 = 1
      · simp only [hodd, ↓reduceIte, decodeQuad_mul hp0]
        have hdecomp : e = 2 * (e / 2) + 1 := by omega
        conv_rhs => rw [hdecomp, pow_succ, pow_mul, sq]
        ring
      · simp only [hodd, ↓reduceIte]
        have hdecomp : e = 2 * (e / 2) := by omega
        conv_rhs => rw [hdecomp, pow_mul, sq]

lemma decodeQuad_qPow {p : ℕ} (hp : 1 < p) (d b e : ℕ) (he : e < 2 ^ 16) :
    decodeQuad p d (qPow p d b e) = (decodeQuad p d b) ^ e := by
  unfold qPow
  rw [decodeQuad_qPowAux hp d 16 b e 1 he, decodeQuad_one hp, one_mul]

lemma testBit_buildQuadPrimMaskAux {p : ℕ} (hp : 0 < p) {d g : ℕ} {ps : List ℕ} :
    ∀ (rem k cur mask z : ℕ),
      (∀ w, mask.testBit w = true → ∃ t, (∀ r ∈ ps, ¬ r ∣ t) ∧ decodeQuad p d w = (decodeQuad p d g) ^ t) →
      decodeQuad p d cur = (decodeQuad p d g) ^ k →
      (buildQuadPrimMaskAux p d g ps rem k cur mask).testBit z = true →
      ∃ t, (∀ r ∈ ps, ¬ r ∣ t) ∧ decodeQuad p d z = (decodeQuad p d g) ^ t
  | 0, _, _, _, z, hmask, _, hz => hmask z hz
  | rem + 1, k, cur, mask, z, hmask, hcur, hz => by
    unfold buildQuadPrimMaskAux at hz
    apply testBit_buildQuadPrimMaskAux hp rem (k + 1) (qMul p d cur g) _ z _ _ hz
    · intro w hw
      split_ifs at hw with hcop
      · rw [Nat.testBit_or, Bool.or_eq_true] at hw
        rcases hw with hw1 | hw2
        · exact hmask w hw1
        · have hweq : w = cur := testBit_one_shiftLeft_eq hw2
          refine ⟨k, fun r hr hdiv => ?_, hweq ▸ hcur⟩
          have hall := List.all_eq_true.mp hcop r hr
          simp [Nat.dvd_iff_mod_eq_zero.mp hdiv] at hall
      · exact hmask w hw
    · rw [decodeQuad_mul hp, hcur, pow_succ]

lemma checkWalkQuad_sound {p d a0 primMask first : ℕ} (hp : 2 ≤ p) :
    ∀ (l : List ℕ) (cnt seen : ℕ) (hne : l ≠ []),
      checkWalkQuad p d a0 primMask first cnt seen l = true →
      cnt + l.length = p * p - 1 ∧
      (∀ z, (seen.testBit z = true ∨ z ∈ l) ↔ (1 ≤ z ∧ z < p * p)) ∧
      (∀ i (hi : i + 1 < l.length), primMask.testBit (qAdd p (qMul p d l[i] l[i + 1]) a0) = true) ∧
      primMask.testBit (qAdd p (qMul p d (l.getLast hne) first) a0) = true
  | [], _, _, hne, _ => absurd rfl hne
  | [x], cnt, seen, _, h => by
    unfold checkWalkQuad at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hcnt, hseen⟩, hlast⟩ := h
    have hp2 : 2 ≤ p * p := by nlinarith
    refine ⟨by simp [hcnt]; omega, fun z => ?_, fun i hi => by simp at hi, by simpa using hlast⟩
    rw [← testBit_mask_range (by omega : 1 ≤ p * p), ← hseen, Nat.testBit_or, Bool.or_eq_true]
    constructor
    · rintro (h1 | h2)
      · exact Or.inl h1
      · simp only [List.mem_singleton] at h2; subst h2
        right; rw [Nat.testBit_shiftLeft]; simp
    · rintro (h1 | h2)
      · exact Or.inl h1
      · exact Or.inr (by simp [testBit_one_shiftLeft_eq h2])
  | x :: y :: rest, cnt, seen, _, h => by
    unfold checkWalkQuad at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hxy, hrec⟩ := h
    have ⟨hlen, hcov, hadj, hlast⟩ :=
      checkWalkQuad_sound hp (y :: rest) (cnt + 1) (seen ||| (1 <<< x)) (List.cons_ne_nil _ _) hrec
    refine ⟨by simp at hlen ⊢; omega, fun z => ?_, fun i hi => ?_, by simpa using hlast⟩
    · rw [← hcov z, Nat.testBit_or, Bool.or_eq_true]
      have hshift : (1 <<< x).testBit z = true ↔ z = x :=
        ⟨testBit_one_shiftLeft_eq, fun h => by subst h; rw [Nat.testBit_shiftLeft]; simp⟩
      rw [hshift]; simp only [List.mem_cons]; tauto
    · cases i with
      | zero => simpa using hxy
      | succ j => exact hadj j (by simp at hi ⊢; omega)

theorem exists_circ_perm_quad_of_checkCycleQuad
    (p d : ℕ) [Fact p.Prime] [Fact (∀ r : ZMod p, r ^ 2 ≠ (d : ZMod p) + 0 * r)]
    (hp3 : 3 ≤ p) (g : ℕ) (ps : List ℕ) (packed : List (ℕ × ℕ))
    (hps_cov : ∀ r, r.Prime → r ∣ (p * p - 1) → r ∈ ps)
    (hp_small : p * p - 1 < 2 ^ 16)
    (hcheck : checkCycleQuad p d (p - 1) g ps packed = true) :
    let K := QuadraticAlgebra (ZMod p) (d : ZMod p) 0
    let _ : Fintype K := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd (d : ZMod p) 0).symm
    ∃ a : Fin (p * p - 1) ≃ Kˣ,
      ∀ i : Fin (p * p - 1),
        IsPrimitiveRoot ((a i : K) * (a ⟨(i.val + 1) % (p * p - 1),
          Nat.mod_lt _ (by have : 9 ≤ p * p := Nat.mul_le_mul hp3 hp3; omega)⟩ : K) - 1) (p * p - 1) := by
  intro K instF
  have hp : p.Prime := Fact.out
  have hp2_ge9 : 9 ≤ p * p := Nat.mul_le_mul hp3 hp3
  have hcardK : Fintype.card K = p * p := by
    rw [Fintype.card_congr (QuadraticAlgebra.equivProd (d : ZMod p) 0), Fintype.card_prod, ZMod.card]
  have hcardU : Fintype.card Kˣ = p * p - 1 := by rw [Fintype.card_units, hcardK]
  have hdec_inj : ∀ x y : ℕ, x < p * p → y < p * p → decodeQuad p d x = decodeQuad p d y → x = y := by
    intro x y hx hy heq
    have hre := congrArg ZMod.val (congrArg QuadraticAlgebra.re heq)
    have him := congrArg ZMod.val (congrArg QuadraticAlgebra.im heq)
    simp only [decodeQuad] at hre him
    rw [ZMod.val_natCast_of_lt (Nat.mod_lt _ hp.pos), ZMod.val_natCast_of_lt (Nat.mod_lt _ hp.pos)] at hre
    have hxdiv : x / p < p := Nat.div_lt_of_lt_mul hx
    have hydiv : y / p < p := Nat.div_lt_of_lt_mul hy
    rw [ZMod.val_natCast_of_lt hxdiv, ZMod.val_natCast_of_lt hydiv] at him
    rw [← Nat.div_add_mod x p, ← Nat.div_add_mod y p, hre, him]
  have hdec0 : decodeQuad p d 0 = 0 := by ext <;> simp [decodeQuad]
  have hdec_m1 : decodeQuad p d (p - 1) = (-1 : K) := by
    ext
    · change (((p - 1) % p : ℕ) : ZMod p) = -1
      rw [Nat.mod_eq_of_lt (show p - 1 < p by omega)]
      have h1 : ((p - 1 : ℕ) : ZMod p) + ((1 : ℕ) : ZMod p) = 0 := by
        rw [← Nat.cast_add, Nat.sub_add_cancel (by omega), ZMod.natCast_self]
      exact eq_neg_of_add_eq_zero_left (by simpa using h1)
    · show (((p - 1) / p : ℕ) : ZMod p) = -(0 : ZMod p)
      rw [Nat.div_eq_of_lt (show p - 1 < p by omega), Nat.cast_zero, neg_zero]
  unfold checkCycleQuad at hcheck
  set cyc := unpackCycle (p * p) packed
  cases hcyc : cyc with
  | nil => simp [hcyc] at hcheck
  | cons first rest =>
    rw [hcyc] at hcheck
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hcheck
    obtain ⟨⟨⟨hg0, hglt⟩, hg_exps⟩, hwalk⟩ := hcheck
    have hg_ne0 : decodeQuad p d g ≠ 0 := fun h0 =>
      hg0 (hdec_inj g 0 hglt (by omega) (h0.trans hdec0.symm))
    have hg_prim : IsPrimitiveRoot (decodeQuad p d g) (p * p - 1) := by
      let gu : Kˣ := Units.mk0 (decodeQuad p d g) hg_ne0
      have hpow1 : (decodeQuad p d g) ^ (p * p - 1) = 1 := by
        have : gu ^ (p * p - 1) = 1 := hcardU ▸ pow_card_eq_one
        simpa [gu] using congrArg Units.val this
      rw [IsPrimitiveRoot.iff_def]
      refine ⟨hpow1, fun l hl => ?_⟩
      have hord_dvd : orderOf gu ∣ p * p - 1 := hcardU ▸ orderOf_dvd_card
      have hord_eq : orderOf gu = p * p - 1 := by
        by_contra hne
        obtain ⟨q, hq⟩ := hord_dvd
        have hq_ne1 : q ≠ 1 := by intro h; subst h; rw [mul_one] at hq; exact hne hq.symm
        obtain ⟨r, hr_prime, hr_dvd_q⟩ := Nat.exists_prime_and_dvd hq_ne1
        have hr_dvd : r ∣ p * p - 1 := hr_dvd_q.trans ⟨orderOf gu, by linarith⟩
        have hr_mem : r ∈ ps := hps_cov r hr_prime hr_dvd
        have hord_dvd_div : orderOf gu ∣ (p * p - 1) / r := by
          obtain ⟨t, ht⟩ := hr_dvd_q
          refine ⟨t, ?_⟩
          rw [hq, ht, show orderOf gu * (r * t) = r * (orderOf gu * t) by ring,
            Nat.mul_div_right _ hr_prime.pos]
        have hgu_div : gu ^ ((p * p - 1) / r) = 1 := orderOf_dvd_iff_pow_eq_one.mp hord_dvd_div
        have hg_div : (decodeQuad p d g) ^ ((p * p - 1) / r) = 1 := by
          have := congrArg Units.val hgu_div; simpa [gu] using this
        have hlt16 : (p * p - 1) / r < 2 ^ 16 := lt_of_le_of_lt (Nat.div_le_self _ _) hp_small
        have hdec_eq : decodeQuad p d (qPow p d g ((p * p - 1) / r)) = decodeQuad p d 1 := by
          rw [decodeQuad_qPow (by omega) d g _ hlt16, hg_div, decodeQuad_one (by omega)]
        have hqpow_lt : qPow p d g ((p * p - 1) / r) < p * p := by
          have hmul_lt : ∀ a b, qMul p d a b < p * p := fun a b => by
            unfold qMul
            have h1 := Nat.mod_lt (a % p * (b % p) + d * (a / p) % p * (b / p)) hp.pos
            have h2 := Nat.mod_lt (a % p * (b / p) + a / p * (b % p)) hp.pos
            nlinarith
          have haux : ∀ fuel b e acc, acc < p * p → qPowAux p d fuel b e acc < p * p := by
            intro fuel
            induction fuel with
            | zero => intro _ _ acc h; exact h
            | succ f ih =>
              intro b e acc hacc; unfold qPowAux
              split_ifs
              · exact hacc
              · exact ih _ _ _ (hmul_lt _ _)
              · exact ih _ _ _ hacc
          exact haux 16 g _ 1 (by nlinarith)
        have hval1 : qPow p d g ((p * p - 1) / r) = 1 :=
          hdec_inj _ 1 hqpow_lt (by nlinarith) hdec_eq
        have hall := List.all_eq_true.mp hg_exps ((p * p - 1) / r) (List.mem_map.mpr ⟨r, hr_mem, rfl⟩)
        simp only [bne_iff_ne, ne_eq] at hall
        exact hall hval1
      rw [← hord_eq]; exact orderOf_dvd_of_pow_eq_one (Units.ext (by simpa [gu] using hl))
    have hpm_prim : ∀ z : ℕ, (buildQuadPrimMask p d g ps).testBit z = true →
        IsPrimitiveRoot (decodeQuad p d z) (p * p - 1) := by
      intro z hz
      obtain ⟨t, hcop_ps, ht⟩ := testBit_buildQuadPrimMaskAux hp.pos (p * p - 1) 1 g 0 z
        (fun _ h => by simp at h) (by simp) hz
      have hcop : Nat.Coprime t (p * p - 1) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hne
        exact hcop_ps r (hps_cov r hr_prime (hr_dvd.trans (Nat.gcd_dvd_right _ _)))
          (hr_dvd.trans (Nat.gcd_dvd_left _ _))
      rw [ht]; exact hg_prim.pow_of_coprime t hcop
    have ⟨hlen, hcov, hadj, hlast⟩ :=
      checkWalkQuad_sound (by omega : 2 ≤ p) (first :: rest) 0 0 (List.cons_ne_nil _ _) hwalk
    simp only [zero_add, Nat.zero_testBit, Bool.false_eq_true, false_or] at hlen hcov
    let f : Fin (p * p - 1) → Kˣ := fun i =>
      let v := (first :: rest)[i.val]'(by omega)
      have hv_rng : 1 ≤ v ∧ v < p * p := (hcov v).mp (List.getElem_mem _)
      Units.mk0 (decodeQuad p d v) (fun h0 => by
        have := hdec_inj v 0 hv_rng.2 (by nlinarith) (h0.trans hdec0.symm); omega)
    have hf_surj : Function.Surjective f := by
      intro u
      let code : ℕ := u.1.re.val + u.1.im.val * p
      have hcode_lt : code < p * p := by
        have h1 := ZMod.val_lt u.1.re; have h2 := ZMod.val_lt u.1.im; dsimp [code]; nlinarith
      have hcode_dec : decodeQuad p d code = u.1 := by
        ext
        · simp [decodeQuad, code, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (ZMod.val_lt u.1.re)]
        · simp [decodeQuad, code, Nat.add_mul_div_right _ _ hp.pos, Nat.div_eq_of_lt (ZMod.val_lt u.1.re)]
      have hcode_pos : 1 ≤ code := by
        by_contra h0; have hc0 : code = 0 := by omega
        exact u.ne_zero (hcode_dec.symm.trans (hc0 ▸ hdec0))
      have hmem : code ∈ first :: rest := (hcov code).mpr ⟨hcode_pos, hcode_lt⟩
      obtain ⟨idx, hidx, hget⟩ := List.getElem_of_mem hmem
      refine ⟨⟨idx, by omega⟩, Units.ext ?_⟩
      simp [f, hget, hcode_dec]
    have hf_bij : Function.Bijective f :=
      (Fintype.bijective_iff_surjective_and_card f).mpr ⟨hf_surj, by rw [Fintype.card_fin, hcardU]⟩
    refine ⟨Equiv.ofBijective f hf_bij, fun i => ?_⟩
    simp only [Equiv.ofBijective_apply]
    by_cases hi : i.val + 1 < p * p - 1
    · have hmod : (i.val + 1) % (p * p - 1) = i.val + 1 := Nat.mod_eq_of_lt hi
      have hprim := hpm_prim _ (hadj i.val (by omega))
      rw [decodeQuad_add' hp.pos, decodeQuad_mul hp.pos, hdec_m1, ← sub_eq_add_neg] at hprim
      simpa [f, hmod] using hprim
    · have hieq : i.val = p * p - 2 := by omega
      have hmod : (i.val + 1) % (p * p - 1) = 0 := by
        rw [hieq, show p * p - 2 + 1 = p * p - 1 by omega, Nat.mod_self]
      have hprim := hpm_prim _ hlast
      rw [decodeQuad_add' hp.pos, decodeQuad_mul hp.pos, hdec_m1, ← sub_eq_add_neg] at hprim
      have hget_last : (first :: rest)[i.val]'(by omega) = (first :: rest).getLast (List.cons_ne_nil _ _) := by
        rw [List.getLast_eq_getElem]; congr 1; omega
      have hget_zero : (first :: rest)[0]'(by omega) = first := rfl
      simpa [f, hmod, hget_last, hget_zero] using hprim

end QuadAndGF16GF27


section ExceptionBridge

lemma mem_of_validPrimeFactors {m : ℕ} {ps : List ℕ} (hm : m ≠ 0)
    (h : validPrimeFactors m ps = true) : ∀ r, r.Prime → r ∣ m → r ∈ ps := by
  have hset := (validPrimeFactors_sound h).2.2
  intro r hr hdvd
  exact List.mem_toFinset.mp (hset.symm ▸ Nat.mem_primeFactors.mpr ⟨hr, hdvd, hm⟩)

lemma exists_circ_perm_cast {K : Type*} [Field K] {m₁ m₂ : ℕ} (hm : m₁ = m₂) (hm1 : 0 < m₁) (a₀ : K)
    (h : ∃ a : Fin m₁ ≃ Kˣ, ∀ i : Fin m₁,
      IsPrimitiveRoot ((a i : K) * (a ⟨(i.val + 1) % m₁, Nat.mod_lt _ hm1⟩ : K) + a₀) m₁) :
    ∃ a : Fin m₂ ≃ Kˣ, ∀ i : Fin m₂,
      IsPrimitiveRoot ((a i : K) * (a ⟨(i.val + 1) % m₂, Nat.mod_lt _ (hm ▸ hm1)⟩ : K) + a₀) m₂ := by
  subst hm; exact h

lemma exists_circ_perm_cast_sub {K : Type*} [Field K] {m₁ m₂ : ℕ} (hm : m₁ = m₂) (hm1 : 0 < m₁)
    (h : ∃ a : Fin m₁ ≃ Kˣ, ∀ i : Fin m₁,
      IsPrimitiveRoot ((a i : K) * (a ⟨(i.val + 1) % m₁, Nat.mod_lt _ hm1⟩ : K) - 1) m₁) :
    ∃ a : Fin m₂ ≃ Kˣ, ∀ i : Fin m₂,
      IsPrimitiveRoot ((a i : K) * (a ⟨(i.val + 1) % m₂, Nat.mod_lt _ (hm ▸ hm1)⟩ : K) - 1) m₂ := by
  subst hm; exact h

lemma exists_circ_perm_prime_minus {F : Type*} [Field F] [Fintype F]
    (p : ℕ) [Fact p.Prime] (hp7 : 7 < p) (hF : Fintype.card F = p)
    (g : ℕ) (ps : List ℕ) (packed : List (ℕ × ℕ))
    (hval : validPrimeFactors (p - 1) ps = true)
    (hp_small : p - 1 < 2 ^ 16)
    (hcheck : checkCyclePrime p (p - 1) g ps packed = true) :
    ∃ a : Fin (Fintype.card F - 1) ≃ Fˣ,
      ∀ i : Fin (Fintype.card F - 1),
        IsPrimitiveRoot ((a i : F) * (a ⟨(i.val + 1) % (Fintype.card F - 1),
          Nat.mod_lt _ (by omega)⟩ : F) - 1) (Fintype.card F - 1) := by
  have hcard : Fintype.card (ZMod p) = Fintype.card F := by rw [ZMod.card, hF]
  let e : ZMod p ≃+* F := FiniteField.ringEquivOfCardEq hcard
  have hm1 : ((p - 1 : ℕ) : ZMod p) = (-1 : ZMod p) := by
    have h1 : ((p - 1 : ℕ) : ZMod p) + ((1 : ℕ) : ZMod p) = 0 := by
      rw [← Nat.cast_add, Nat.sub_add_cancel (by omega), ZMod.natCast_self]
    exact eq_neg_of_add_eq_zero_left (by simpa using h1)
  have hK := exists_circ_perm_zmod_of_checkCyclePrime p hp7 (p - 1) g ps packed
    (mem_of_validPrimeFactors (by omega) hval) hp_small hcheck
  rw [hm1] at hK
  have hK' := exists_circ_perm_cast (by rw [ZMod.card] : p - 1 = Fintype.card (ZMod p) - 1) (by omega) (-1 : ZMod p) hK
  have hres := exists_circ_perm_of_ringEquiv hcard e (-1 : ZMod p) (-1 : F) (by simp) hK'
  simpa [sub_eq_add_neg] using hres

lemma exists_circ_perm_prime_plus {F : Type*} [Field F] [Fintype F]
    (p : ℕ) [Fact p.Prime] (hp7 : 7 < p) (hF : Fintype.card F = p)
    (g : ℕ) (ps : List ℕ) (packed : List (ℕ × ℕ))
    (hval : validPrimeFactors (p - 1) ps = true)
    (hp_small : p - 1 < 2 ^ 16)
    (hcheck : checkCyclePrime p 1 g ps packed = true) :
    ∃ a : Fin (Fintype.card F - 1) ≃ Fˣ,
      ∀ i : Fin (Fintype.card F - 1),
        IsPrimitiveRoot ((a i : F) * (a ⟨(i.val + 1) % (Fintype.card F - 1),
          Nat.mod_lt _ (by omega)⟩ : F) + 1) (Fintype.card F - 1) := by
  have hcard : Fintype.card (ZMod p) = Fintype.card F := by rw [ZMod.card, hF]
  let e : ZMod p ≃+* F := FiniteField.ringEquivOfCardEq hcard
  have hK := exists_circ_perm_zmod_of_checkCyclePrime p hp7 1 g ps packed
    (mem_of_validPrimeFactors (by omega) hval) hp_small hcheck
  have hK' := exists_circ_perm_cast (by rw [ZMod.card] : p - 1 = Fintype.card (ZMod p) - 1) (by omega) (1 : ZMod p)
    (by simpa using hK)
  exact exists_circ_perm_of_ringEquiv hcard e (1 : ZMod p) (1 : F) (by simp) hK'

lemma exists_circ_perm_quad_minus {F : Type*} [Field F] [Fintype F]
    (p d : ℕ) [Fact p.Prime] [Fact (∀ r : ZMod p, r ^ 2 ≠ (d : ZMod p) + 0 * r)]
    (hp3 : 3 ≤ p) (hF : Fintype.card F = p * p)
    (g : ℕ) (ps : List ℕ) (packed : List (ℕ × ℕ))
    (hval : validPrimeFactors (p * p - 1) ps = true)
    (hp_small : p * p - 1 < 2 ^ 16)
    (hcheck : checkCycleQuad p d (p - 1) g ps packed = true) :
    ∃ a : Fin (Fintype.card F - 1) ≃ Fˣ,
      ∀ i : Fin (Fintype.card F - 1),
        IsPrimitiveRoot ((a i : F) * (a ⟨(i.val + 1) % (Fintype.card F - 1),
          Nat.mod_lt _ (by have : 9 ≤ p * p := Nat.mul_le_mul hp3 hp3; omega)⟩ : F) - 1) (Fintype.card F - 1) := by
  have hp2_ge9 : 9 ≤ p * p := Nat.mul_le_mul hp3 hp3
  let K := QuadraticAlgebra (ZMod p) (d : ZMod p) 0
  let _instK : Fintype K := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd (d : ZMod p) 0).symm
  have hcardK : Fintype.card K = p * p := by
    rw [Fintype.card_congr (QuadraticAlgebra.equivProd (d : ZMod p) 0), Fintype.card_prod, ZMod.card]
  have hcard : Fintype.card K = Fintype.card F := hcardK.trans hF.symm
  let e : K ≃+* F := FiniteField.ringEquivOfCardEq hcard
  have hK := exists_circ_perm_quad_of_checkCycleQuad p d hp3 g ps packed
    (mem_of_validPrimeFactors (by omega) hval) hp_small hcheck
  have hK_add : ∃ a : Fin (p * p - 1) ≃ Kˣ, ∀ i : Fin (p * p - 1),
      IsPrimitiveRoot ((a i : K) * (a ⟨(i.val + 1) % (p * p - 1),
        Nat.mod_lt _ (by omega)⟩ : K) + (-1 : K)) (p * p - 1) := by
    simpa [sub_eq_add_neg] using hK
  have hK' := exists_circ_perm_cast (by rw [hcardK] : p * p - 1 = Fintype.card K - 1) (by omega) (-1 : K) hK_add
  have hres := exists_circ_perm_of_ringEquiv hcard e (-1 : K) (-1 : F) (by simp) hK'
  simpa [sub_eq_add_neg] using hres

end ExceptionBridge


section ExceptionCycles
def cyc_9 : List (ℕ × ℕ) := [(8,39113268)]
lemma qnr_3 : ∀ r : ZMod 3, r ^ 2 ≠ (2 : ZMod 3) + 0 * r := by decide
lemma check_9 : checkCycleQuad 3 2 2 4 [2] cyc_9 = true := by decide +kernel
def cyc_11 : List (ℕ × ℕ) := [(10,24493053665)]
lemma check_11 : checkCyclePrime 11 10 2 [2, 5] cyc_11 = true := by decide +kernel
def cyc_13 : List (ℕ × ℕ) := [(12,11074039074966)]
lemma check_13 : checkCyclePrime 13 12 2 [2, 3] cyc_13 = true := by decide +kernel
def cyc_19 : List (ℕ × ℕ) := [(18,90140944403135180096343)]
lemma check_19 : checkCyclePrime 19 18 2 [2, 3] cyc_19 = true := by decide +kernel
def cyc_23 : List (ℕ × ℕ) := [(22,126478216800197879035306483937)]
lemma check_23 : checkCyclePrime 23 22 5 [2, 11] cyc_23 = true := by decide +kernel
def cyc_25 : List (ℕ × ℕ) := [(24,2596565486404295746050143219901228)]
lemma qnr_5 : ∀ r : ZMod 5, r ^ 2 ≠ (2 : ZMod 5) + 0 * r := by decide
lemma check_25 : checkCycleQuad 5 2 4 7 [2, 3] cyc_25 = true := by decide +kernel
def cyc_29 : List (ℕ × ℕ) := [(24,80129102644843536580286504738248053),(4,142589)]
lemma check_29 : checkCyclePrime 29 28 2 [2, 7] cyc_29 = true := by decide +kernel
def cyc_31 : List (ℕ × ℕ) := [(24,501268139341456642080258516575958732),(6,185269533)]
lemma check_31 : checkCyclePrime 31 30 3 [2, 3, 5] cyc_31 = true := by decide +kernel
def cyc_37 : List (ℕ × ℕ) := [(24,4081701165708542199634290212915307418),(12,4836301780520398688)]
lemma check_37 : checkCyclePrime 37 36 2 [2, 3] cyc_37 = true := by decide +kernel
def cyc_41 : List (ℕ × ℕ) := [(24,341442566320133606011580266928699987524),(16,51249571485475080958208576)]
lemma check_41 : checkCyclePrime 41 40 6 [2, 5] cyc_41 = true := by decide +kernel
def cyc_43 : List (ℕ × ℕ) := [(24,1232825684208875124463563077899511880073),(18,182496522153246989936836518326)]
lemma check_43 : checkCyclePrime 43 42 3 [2, 3, 7] cyc_43 = true := by decide +kernel
def cyc_49 : List (ℕ × ℕ) := [(24,18158636494389283488681854407771669935005),(24,13559026945775197296012315245508317614171)]
lemma qnr_7 : ∀ r : ZMod 7, r ^ 2 ≠ (3 : ZMod 7) + 0 * r := by decide
lemma check_49 : checkCycleQuad 7 3 6 8 [2, 3] cyc_49 = true := by decide +kernel
def cyc_61 : List (ℕ × ℕ) := [(24,1280646671262878290609748341072829237819580),(24,3693051036327356095987288220829484565000962),(12,268834366657185953228)]
lemma check_61 : checkCyclePrime 61 60 2 [2, 3, 5] cyc_61 = true := by decide +kernel
def cyc_67 : List (ℕ × ℕ) := [(24,23310512356578443695008022967637442921611064),(24,2845550531275657059614162778275515701300698),(18,421544879523704712458312958905559)]
lemma check_67 : checkCyclePrime 67 66 2 [2, 3, 11] cyc_67 = true := by decide +kernel
def cyc_71 : List (ℕ × ℕ) := [(24,252166615497916382882298429487165347247775381),(24,162815301821592087825838052809058533516188784),(22,24239872871155189020224586655561407918970)]
lemma check_71 : checkCyclePrime 71 70 7 [2, 5, 7] cyc_71 = true := by decide +kernel
def cyc_79 : List (ℕ × ℕ) := [(24,1865802148728952508658895460751855342369287233),(24,2527719124905579923764415968704479735491023549),(24,2667571417692161012954431565060162018843690959),(6,5192745586)]
lemma check_79 : checkCyclePrime 79 78 3 [2, 3, 13] cyc_79 = true := by decide +kernel
def cyc_103 : List (ℕ × ℕ) := List.flatten [
  [(24,459788802178980915675373040676341197453019100567),(24,767374359823833821317345193469196522115812663595),(24,1493619020595588056934092384523498129091937002914),(24,1694094392346786594431422180155977599159204100980)],
  [(6,508442528643)]
]
lemma check_103 : checkCyclePrime 103 102 5 [2, 3, 17] cyc_103 = true := by decide +kernel
def cyc_121 : List (ℕ × ℕ) := List.flatten [
  [(24,22656934867698051049592329853148927775182758969788),(24,3294321642300284368671511224674226491757022162271),(24,67704906399617044725893369623406019376391722768139),(24,6649593737654858534898481622722709461299209087729)],
  [(24,20440540590062486142373770015575881581247326986813)]
]
lemma qnr_11 : ∀ r : ZMod 11, r ^ 2 ≠ (2 : ZMod 11) + 0 * r := by decide
lemma check_121 : checkCycleQuad 11 2 10 13 [2, 3, 5] cyc_121 = true := by decide +kernel
def cyc_127 : List (ℕ × ℕ) := List.flatten [
  [(24,195028756708052522636698244646680556280574628064426),(24,224228766294182581620476865813899240607751926075943),(24,7490853972927340951659288387959530051792043898354),(24,70648805024161487892182163223883295240652597587510)],
  [(24,274699004590396310841567453679387669664735595974650),(6,3907137708060)]
]
lemma check_127 : checkCyclePrime 127 126 3 [2, 3, 7] cyc_127 = true := by decide +kernel
def cyc_151 : List (ℕ × ℕ) := List.flatten [
  [(24,18457645435476641852058317680102869735116174809569493),(24,13101419264661612583672302353535519457289904542240762),(24,6749658588183664546544461093882689515886550906791504),(24,17398651566829310637514633149159305717287213711158029)],
  [(24,5600397520197932941873189564292603731175444921872557),(24,3387593028410134117571776502001210173804392667787334),(6,9547159239546)]
]
lemma check_151 : checkCyclePrime 151 150 6 [2, 3, 5] cyc_151 = true := by decide +kernel
def cyc_169 : List (ℕ × ℕ) := List.flatten [
  [(24,54807049772100923237756553909801200976608331687248990),(24,93855081405660293975653235272664677301559554914501646),(24,287486799181876454899866318587279059917409862842473945),(24,174183035201243716181901948333635957265403425211069315)],
  [(24,58128595708422134604444490681613237973737172721452577),(24,179051261604026964977439196885028443434000311605081588),(24,23100283406918242947143309237355766786454622773021807)]
]
lemma qnr_13 : ∀ r : ZMod 13, r ^ 2 ≠ (2 : ZMod 13) + 0 * r := by decide
lemma check_169 : checkCycleQuad 13 2 12 15 [2, 3, 7] cyc_169 = true := by decide +kernel
def cyc_181 : List (ℕ × ℕ) := List.flatten [
  [(24,1371112079809343069848700583661062326078167601266390574),(24,1279308258402368227574968111220552104794720572012056843),(24,148933082953006657421714054362972952044771914555902991),(24,536952579362856991723721295961264952875807959565185773)],
  [(24,981864350876532057219528052520093742213389526867519207),(24,749127428624651299144787129696595761727418273627401567),(24,1237365284022378857119816402495063312404982482170302875),(12,1116200811637451828681277280)]
]
lemma check_181 : checkCyclePrime 181 180 2 [2, 3, 5] cyc_181 = true := by decide +kernel
def cyc_211 : List (ℕ × ℕ) := List.flatten [
  [(24,11244222101416300723150811523484144218481023675426915671),(24,14212090833705574841743602297984772022509152901459973359),(24,16809345621166694804644833096135849754434563552826747619),(24,4441574998561719400916045816827194863993236778568080295)],
  [(24,3088454505355482727397691923801453670929111373084543967),(24,34861468896456235544926858272770790530217352850240585730),(24,7099856822870091193156448271103366713188268020062649178),(24,36100538635998584409908454170361174295435362204980906686)],
  [(18,212066994929745968820855511568410398681180)]
]
lemma check_211 : checkCyclePrime 211 210 2 [2, 3, 5, 7] cyc_211 = true := by decide +kernel
def cyc_241 : List (ℕ × ℕ) := List.flatten [
  [(24,1185569241950650820311891016733323672524783830441901684657),(24,84301157589538966684404532134609490592317115344300917198),(24,349298837682116155796169105473535294100720302598646488353),(24,609929575724500952120783315637420513555602005884820365980)],
  [(24,800475679516627481900131621355918701928202074989002372821),(24,1177156256445453292040763455691885447928436641383935216020),(24,1173759283262914022181098219593849550587382184106709943631),(24,858066418093843454145487244445277686826217470510069467050)],
  [(24,752625741303438681893493918139599512908416701934282593370),(24,201122105847002558555543802243833043268870084776166762320)]
]
lemma check_241 : checkCyclePrime 241 240 7 [2, 3, 5] cyc_241 = true := by decide +kernel
def cyc_271 : List (ℕ × ℕ) := List.flatten [
  [(24,23828101572339634808339889828012777053303694106652994245564),(24,11254503537306029007398435269486048782146315391097264928220),(24,4808700366635280636715564351389060756503967873961792487006),(24,22002341817829097347298273154895043025155315492658873106807)],
  [(24,22842746085866655157137843320581288398694058330042170363046),(24,6247340340248329760608829643681420044929973026699756905738),(24,1546640758104222607761769021696712653214918834254363300529),(24,12255650930276924597080643946193115990405363675639844710751)],
  [(24,8499724841942709555423328672439066858687568520253328357437),(24,5913498185271122692511263736205008171168477982836513746123),(24,12884258084365526332690506631893405020662632747633493298634),(6,264138861491820)]
]
lemma check_271 : checkCyclePrime 271 270 6 [2, 3, 5] cyc_271 = true := by decide +kernel
def cyc_331 : List (ℕ × ℕ) := List.flatten [
  [(24,1251059162666259780354967850761655594472862670863912212053616),(24,1541612597296388625492317149990233171763919778589627986587123),(24,1762490197003663161098383091143621291965826426921813176677999),(24,760147655969222532342779377484071310498606251879182675787342)],
  [(24,2816072143153859704546909637164426361590946464103759825633758),(24,622402198821156669529590322839548790909086746303727184218666),(24,1836517958481811834081797177870127238908434946184614756406010),(24,2288292371718328878214869035716366346313717043050036013298624)],
  [(24,2140880308825456697947360505488287564345898651186869665589152),(24,356713871756765321434222049315640114912899506293326824589702),(24,2946025261598487121928892056583390246315770453358090096324478),(24,1056770324141490272207674954673720618239718613831149248772671)],
  [(24,2014300035331325197565309069696397934176734234591340996096329),(18,2180491551436817729851255986534047255237930115)]
]
lemma check_331 : checkCyclePrime 331 330 3 [2, 3, 5, 11] cyc_331 = true := by decide +kernel
def cyc_361 : List (ℕ × ℕ) := List.flatten [
  [(24,9940143131788999689925730601980800184901315268804784716240427),(24,18098986834961596328963199479786918518263110582765225624705876),(24,5147297934475644479591441106413923744582825409843885592812037),(24,16658894830988181243187004921306859838705663809696718309464791)],
  [(24,2510627273351598420998934187081682194071593330156634218389439),(24,4063462248869459884920196902787894391375668737665182917597006),(24,17782943444644561992419040139591528330736341283453770011539578),(24,20883688911564781321896377620947299579802097400536170452268630)],
  [(24,6681547759271745338451447698059502131807476246264599600362461),(24,3137034489930408332775075577464555841512636557417709981625691),(24,21224000389761297477731812653983175930734190982133517236997806),(24,22028017000053033938626882212905711951468406986043810340959654)],
  [(24,3649062102551513357027965927787440246432562454146253517090973),(24,10266189352523828006969222988640634783255168813900476381738709),(24,13524974895368469465309904727938781381990994400025626959441862)]
]
lemma qnr_19 : ∀ r : ZMod 19, r ^ 2 ≠ (2 : ZMod 19) + 0 * r := by decide
lemma check_361 : checkCycleQuad 19 2 18 21 [2, 3, 5] cyc_361 = true := by decide +kernel
def cyc_421 : List (ℕ × ℕ) := List.flatten [
  [(24,36924684626353910752492181925716466281030293401443688707896835),(24,842730848269642523744081236082356281197717475383015736005630624),(24,183048061076356769526519079579408272046148162699272939806945027),(24,486865959266624588997857916366208979544258715277323099573896287)],
  [(24,481222137588641130373518582636625036388381300028460919625479951),(24,905135927215777071167546995218233146386189783741009561495617564),(24,34468425677682665696699277878020223893290324046645022881025242),(24,671035998735462516612433480322603326951043945377708473770710259)],
  [(24,722610869197779304246401212149938670414268142061461954902061077),(24,187171205787186769867516737709071884867552949454569791306982252),(24,257305573854139334123757207382726599983549934084013935645008666),(24,369411619352910445202714073917907395524869799027740082464605683)],
  [(24,229809193271168428033786961732058886952906915062382481049772698),(24,660674653477189871581173165020501033164599110071051912412226863),(24,492116916330442734209488311156741916355156616549048644135422444),(24,638422145970439004864406371557058187424927952903953147585746601)],
  [(24,901634518917861636036241711133547069552500523301779256226857525),(12,1309374858298270319071568056932)]
]
lemma check_421 : checkCyclePrime 421 420 2 [2, 3, 5, 7] cyc_421 = true := by decide +kernel
def cyc_463 : List (ℕ × ℕ) := List.flatten [
  [(24,6133584104108270473801916249487304159677694566078657365705853282),(24,4993659602427324637749556268075988195175437109130372581907002101),(24,9361385999731859295812275701142160779973399742518448012863132365),(24,5329166854586219876287835875935692586077266926100007913255008629)],
  [(24,7572430612810814211539410438870235688280010265935347149904830478),(24,1698749895843981706583202483828826450636724425136876167236583954),(24,4838743706798918256850560323920003095679200485792892069735879393),(24,6553546087682952129337594496139996317109263722225526612018827811)],
  [(24,3994369649533797323455919554631225000963612601458434229712372827),(24,4880225905222565472566179333122244341444926601595788438705677590),(24,7129065734655902849727812246513663420046522956047065766228613919),(24,2553318438479284201587639150764005091830565878988818024058017245)],
  [(24,2078071561213784457859837753766191133877180713822652912064894365),(24,8850702212505583280303363708058495625136878633000974562428616406),(24,1478041065343310409709510445186896736391058582716682002856393209),(24,4202365993918576848859263985746458806274458358809961421215530879)],
  [(24,9052981386084395129640974948638232450778303642366472467328029133),(24,5851715901433937679778503851968298537448833102255287882420654442),(24,6982791987198951859083722589212737960008226241980254651266317138),(6,778611032670095)]
]
lemma check_463 : checkCyclePrime 463 462 3 [2, 3, 7, 11] cyc_463 = true := by decide +kernel
def cyc_547 : List (ℕ × ℕ) := List.flatten [
  [(24,112381551216434519658708514480286805303422655401761469160034605482),(24,271102040991123397316360618099552990786640023950579710302425345408),(24,213193094381470997932653210721975733017263347592925988938349001379),(24,282087063344608360606454255907008413279706304936813379162445549979)],
  [(24,329763868859527126321166575697673256440391629855210605017639827036),(24,372547081179876812352145547153524910884766991706874925999577874893),(24,201956697764849559547459795525496739257194046119148898448844225616),(24,52786068122340791900253825583910768668664688057147934361375136279)],
  [(24,57911959375108668471626596510856318009433899297712287061835846274),(24,45230770467508452467152994869021190399646796932461484191761640839),(24,452649579364765910720088045432399745050254220979454424540790216083),(24,265594429141156168150801611315241560577810153517439547873788289154)],
  [(24,318963544180113759115639800154218996016369101647378757137220265887),(24,73544178150338223560141234379676315708520720329543496536741075317),(24,510274636322953084495103566265329369189453963332563393457156512933),(24,398904617189552036519567038886795020191375294196589508296327102694)],
  [(24,92259461589433943716363753233065996142552744533877462438892159267),(24,154465750275896481612199805362936001561285205705711831517882110968),(24,182490433998859290198536814133505055551503562902782325547603890994),(24,512233036569303356067875467972156874182721844904869730798349714064)],
  [(24,313393943879814092192386479334866942961062167733013529200277842856),(24,211002092293312710005884863110177197200456094457396187706001920611),(18,6851104974750546140712029401318055142395374191782)]
]
lemma check_547 : checkCyclePrime 547 546 2 [2, 3, 7, 13] cyc_547 = true := by decide +kernel
def cyc_571 : List (ℕ × ℕ) := List.flatten [
  [(24,1052339899851175203475792549176552395978837162213611048021889000389),(24,805732433749202516376041398911546558210409548847540542744325860419),(24,959147147631667226485624589746661944481457974089275001403097409616),(24,550867515080538774218607930728126575981593964685668254306075553056)],
  [(24,932871291268337797665966197650809493690674233466271260944830739987),(24,625938640547982280311069638399298206536478735444352662614598317411),(24,691506942728077003495559448352268858973684006553037468477111468369),(24,862817465193318325645108277677030669359949813171232299096203855315)],
  [(24,1197039830606791282129050143862703424207258285193721552630115339528),(24,30891798736824106326528587097953938759792708918433915799245230668),(24,233010940429986608303801985509207877327612106442016756540777012484),(24,635162265147980847377571740743898275828868972673328479239359264905)],
  [(24,851956911247760610035617187255172749942868797494937543706008156341),(24,394497167967211504591479314298778568853009272757858228194712568431),(24,1372858833049580393684243591897940685345270461960096012264679344561),(24,383370102838740591057495905315850785538464616511199894059348576695)],
  [(24,1388578935442352765725725072605905928742798717475642921694616829180),(24,954909054721348188784939724542375248643718574564141638625462771237),(24,337290390572808684938729873822939809102869872682253533277162308187),(24,650063071370399063606487914724794829245350503721786052856180225576)],
  [(24,108956222877824969075711468190998482584451689582595621190569730670),(24,440387396644841212824548621557579587361979507857142282830727821312),(24,388918814361503553789500795122923617061501876703885299280968485541),(18,13140681562516921031611817451862922917521052342537)]
]
lemma check_571 : checkCyclePrime 571 570 3 [2, 3, 5, 19] cyc_571 = true := by decide +kernel
def cyc_631 : List (ℕ × ℕ) := List.flatten [
  [(24,1681654053014169510383904806636143852971349045337353764086956351808),(24,4473344446716278355305053240099717740483720304228576426935549967326),(24,130224470061906781371989938091752859926046312161977598283110374547),(24,13043277394037595082538919030743683117833486602623184729561581027222)],
  [(24,4436962732276228813834021765290713586647071701568144963044268125029),(24,11084435516983228633550472694868052968544720336462970455710822565370),(24,448187651962761763621417129327463558657236699157052463872091850048),(24,10344156610062308240125485135172150341655255966339564515554271018357)],
  [(24,11200677679535765681757889151250367218416386539030599525200575264377),(24,1571840142168177149490041411914504656610668669529357121602646689997),(24,7652304588386996980533497969417700718898489233304234140051583186420),(24,4110281197674782881723077991488681797958286253867803286689243581447)],
  [(24,13557496895724863125692437082809658282675654936872780779946302239031),(24,11034826805319875842064359363214866595867868206403281196956573763008),(24,12748700460501665863117841804286283668084204214222163606406976263903),(24,4912233175603661956502677952212368861457329741794343034516586067755)],
  [(24,11320786406924474379964318091370199483590111021824092145148620668143),(24,9286532368578605684332083778860516631724551599790970650077416855590),(24,5277154319405090394348830403795191428451011772449988949952447534847),(24,12346257792668151167038126607418831469672018011077596922473875950153)],
  [(24,11475655670515286286223172494498351964492303887611245780059886557582),(24,45449890290940641538187276430849420117794879840100240069219088005),(24,2947349882807019100768465869757606235210165634138666350491061944181),(24,13496965933520153836048499337648322039948774308065384335039843097864)],
  [(24,628710790847222728903563108023814779097664903400349795834863901573),(24,8967825693494726069813710945571397121435879684127782871240290151091),(6,16841204907594291)]
]
lemma check_631 : checkCyclePrime 631 630 3 [2, 3, 5, 7] cyc_631 = true := by decide +kernel
def cyc_661 : List (ℕ × ℕ) := List.flatten [
  [(24,11135240752619105311820890808783979922574818051522020144622190346694),(24,38252737474688919362129685778759135909689015046799012343634404139091),(24,12750738558705850030332488219509541268648226570425262858335683963526),(24,39937613363944984334551909019355851458612721104825731980099746427039)],
  [(24,29646088676950261462845656314802101509471084547001667216256957317488),(24,46971882374761742815685571342143089055733515201897542577655929113258),(24,42601527839825011987204539238480470386987142694227752921667164254950),(24,30871251164880341941326951948586990654282416853836119826955331465133)],
  [(24,45233095131011955472596001650233006659361598621112275508904689027617),(24,47366968692356696345898597664854090158364511350078831850525531247850),(24,8773422695857397918518161811829553577836841362096083766751534065567),(24,40396721358650146514721726713572961212573463791006169664111925089341)],
  [(24,23971477021769798188593218314125637855332169155599579123598510145996),(24,44373742843107333322211178695227999589527257014075213380297927470840),(24,34607281224611105527946893039600750872099956975624689071001893030383),(24,14359028250888905702772378770996372823756753467830167630822594543011)],
  [(24,12157165509807853826029303223206656652025248385074824276402034556646),(24,26310835824115441962558062363147090872995788716175422375503329675745),(24,17612093739242833330513656670673145168128686751068247612469979693672),(24,4071420057774622023483640229212052558270636780606357663413155963286)],
  [(24,22940932132493711538392505106984860856667577479015621554299760384795),(24,13375477132435056774509768235059656152052818887346328749286356830100),(24,40180461581696984912739082121749453573232925397397664139965111861016),(24,35257143119010223257430009905230833385898623051938181791276912654035)],
  [(24,8963280739355146603772261690598552596138053419653874492819030549165),(24,46713620734644598914783470411216548438372385456688834659452497955767),(24,35841231856132652735373647737240455262477976228751210702899304209475),(12,161381762623594860675771062461844)]
]
lemma check_661 : checkCyclePrime 661 660 2 [2, 3, 5, 11] cyc_661 = true := by decide +kernel
def cyc_841 : List (ℕ × ℕ) := List.flatten [
  [(24,5396412885223908819808027537628488104506716644166994329767107845508921),(24,173941148438228377062062919458485940689058168495880474417794335896919),(24,7669041846335110033740215729834902432424412093750848396597089654630249),(24,5848551235283654031317199901322318742307675976415580117768745798273466)],
  [(24,6615049515343028978957349851964907578785288039512979318371800099615491),(24,7068049454008319292078835853824296612806840838674071157929631033662222),(24,2532722455214389031588262003812749816761480128406893362615805142593148),(24,2759740959204200477345465360261460621553423845089683223267327420908654)],
  [(24,15441798012954210235564468534815014890918898882325162996976894183581077),(24,1571215577673888622596063236130186364205382384228758286310084242231583),(24,1609785359965616206775996499369749170898825631842166376376873364751264),(24,14678089045936951143466162348347397455591913755984657144093162901029672)],
  [(24,3041976157153107509026158785256803961197086011779767676583082908841358),(24,15196377117817797896782931693362395086584242643392346608946441357433350),(24,12304167325028780681735074469328580221637244471857557420317922431715556),(24,12713914861931501125104759254117219247159984243188748533834123782574549)],
  [(24,1698722575306339752506045090809109622745450687598382431072879411656619),(24,13883538581645738169327045143508124108164062791220547159408936808700662),(24,7925806580210859473026140455190149821158183754211782284535436578225087),(24,1279546582073586391893639469324316032521675424388400525658756300480575)],
  [(24,5619047422485110378497004039286410941992816028872955089896640276341232),(24,1084052668864999690704966762046444202403040519895757388360583186923602),(24,13419595372887322987955622928416175719342688371175404906758408427074029),(24,1950884819682434492721435514837259918649154365917742463714822762160559)],
  [(24,3165876029356840841255271374884954860054726366813764774374267142123451),(24,6019093696543799005841545721026954370535493261499019309224816804133719),(24,6266188494386503647745117435405340300789501460573064411334612018926354),(24,9571386333276617288940574882471342155860554634322882265611534589107265)],
  [(24,7496164079281107803469275576945436757634288168911241982845522003423681),(24,14086869136273256393985238347202513778082770879472289929170837097067641),(24,12852129190267386046437472352296019844143980466733467206725062200521123),(24,1489959772610132462368517065129206231187267567909891299425624032069879)],
  [(24,5200468513830380109218301933085824674873338981143709852994543013743494),(24,2600484831524172165648452687962415077488492372234103009251058128225880),(24,12739111725718112357699451305628502951135758224560931708670042966714889)]
]
lemma qnr_29 : ∀ r : ZMod 29, r ^ 2 ≠ (2 : ZMod 29) + 0 * r := by decide
lemma check_841 : checkCycleQuad 29 2 28 33 [2, 3, 5, 7] cyc_841 = true := by decide +kernel
def cyc_991 : List (ℕ × ℕ) := List.flatten [
  [(24,32864888431933604383123168088927012258050030783627207268186238644045948),(24,438438836459982183979299722789939446303588565308691183179689095673414145),(24,117758410390598620540086559099499755410764441840967673524093677942998945),(24,128146228964387509333559574649486004546614801227826818035391785161226800)],
  [(24,768886374222014993440342010034285769993961119021001552016751223549647170),(24,240153280416197817795752611134746166575430473273795590214603275300672337),(24,696360379844585973516427076573805599474578360023995628105261280316395273),(24,714401826055158045410803368240341436925735385712512507584980830639314841)],
  [(24,286199049764273260544626872673872600885406290571889855002153725866626407),(24,122276582426669157530128192690577615967833937362358282473480103538612984),(24,416913365877886444070921223377758880334074560492332696075252720254986698),(24,5621355212849570731374214545865164937996244904145617333239335942192780)],
  [(24,251863471381282095795175555058506023140426240214605415087052024198401003),(24,502669290603876163086220951826069995899148650948117335242060114834465281),(24,558292876916547673999440073700291501608567479351343149190559510351688332),(24,145578055175325976816346681817248411718005732263449372291285009211186149)],
  [(24,398441007014727524116736843603111141259117604151653972964212742069937471),(24,147841601348956429503607684953845505867306973329873368278239540320336981),(24,69359755764044855278864554869643945021518119732395164297417268850737490),(24,215433630691327074813315026782392104853763512220955252694044298811745240)],
  [(24,630822339968100714384477408851427644364392343068155780638955209515435194),(24,554054575382328820829802363436403351478180554664540063048083914078234901),(24,374835902655529329073577684347030438880808506942041680303988484026994672),(24,497889275536193398477411125924373777292262904830238309623421964365290929)],
  [(24,140147428728206949817717137201909011259272429761088382312607194521587558),(24,483676582224856280485395598654792441942420149789115513586885246386419622),(24,470127040071407858691069070059560394941802090417064658166737763424215436),(24,109351380005862358159674575005567431951827006250018507902540101084900193)],
  [(24,344076149259092579411805388546416966230090739759182920515227229953426777),(24,564353676645413678487031090180906891171541164602718102170426905164448519),(24,576303204720794464148531902735934626260249942373157160940570472559060987),(24,138253743427891222501463088985682501838741038485179530680670857878349140)],
  [(24,471780533481526665513269720420306618890465642879201701575153464844362134),(24,74588240787371816546775189186767432449559236964059773875784817022125336),(24,494482903971755934013766506166571083101952804495554079162568619677012453),(24,384465894395201977228914439861954796152563197085470457918190546303855182)],
  [(24,755351165395743945873494201102095119838256627331031144263264832185118957),(24,358270448565938869082022740570805680295327237752939020106646378025010095),(24,676322157820596581047314146740461536590951652596749706567306426062191479),(24,28375318030609034823594336538299207749457115992537552477078791734137856)],
  [(24,200491174342847449963040660613252994016086530795903043971195324041974720),(6,673254064110773410)]
]
lemma check_991 : checkCyclePrime 991 990 6 [2, 3, 5, 11] cyc_991 = true := by decide +kernel
def cyc_1051 : List (ℕ × ℕ) := List.flatten [
  [(24,1801665844144205272785129489632711862065902341462181555944252441498813761),(24,194829120995933540149792199684690779776035324528818513941134273189705220),(24,2879753479219025800861605066053677063052705952566963722496519240383360743),(24,1944441138736566702535430832608040130843282163362822585571356801549877434)],
  [(24,1868086722412003492578287508312091506128306771711273816426601551076217059),(24,538891254559203310421465134587284323652843679961699526038807019567069195),(24,2555955660027057350029970440937937972712018375021080364884963054667715980),(24,2418589520699133804531487948480411816072607901326726485186861346147451575)],
  [(24,261308660358255418593765767619011039044097447458291612866121856539543426),(24,1113954592650494769394391864949470499100254481380863223800004888398674536),(24,1537448885441716946508586727687509328988928626670439256173885109815299682),(24,3200610100327336711649318792671031323304040370330433412465362627769972806)],
  [(24,1018634350468557063823822879275983155601966908682442181514105999531427040),(24,1590513366290108622394113685035668046621680511982371937303101144968745280),(24,1161355171122826115509276524011597764618624233329914148461873098666342016),(24,661804764237010031287711754883032630560363307747639634808721054318487679)],
  [(24,817117675909468114706242857015546523898596382443037270063305114110673561),(24,1740919287082881849532786609057055026228151640253038699942248321116097274),(24,830940466367820715569232944482997954788572069391795888052623017774625685),(24,1521204128814901532683611444365076309534389039102477065752136607847352466)],
  [(24,461453625215279837798548329740859253814900478195961964886256640646761673),(24,2033527069184293839636654246579845214367063362889241432203185829612502951),(24,750446473600103988467061003493836037317037629404432101110148186930196857),(24,2768972729221441332826231422437817529662230002317542618909023794879676299)],
  [(24,1524102090247256051765880594141584041122957342668074992733889018736952769),(24,390165874988148870509079151993156836139947755396468218964024251948054031),(24,630254202046663886020529496531196186589837294303979235189017399666512421),(24,1417526627293731516992258492387053446166043344125054329506582385027111729)],
  [(24,1994728451909464207730721340114832549209232074873919125098419506573111208),(24,1241499627190373899348288442842828733140024054506943729496914697251521409),(24,651748837236926058632350131610750059857066607085427793087603502737932179),(24,934906655215937095930161303851429739355012545802968911482889508848811979)],
  [(24,1247128117924957947903804401436639318375000971332391383697795671111380364),(24,2868570216448561014875415348986157063104600864627203812517490116801649938),(24,2228084831120601291796491840726051271971245694741394296855463016134999661),(24,138171656383533894701764788428915527809002087390208500665370152423665375)],
  [(24,132549445363285951154836413913131607388060348947256794512647788562221675),(24,266921996821417269531108053478509608350932916077229830575982539369956625),(24,1021569653449282065212976014057045090590482436697689740066498968942367130),(24,3280755405034690653162539849529244623644544440073197104357588372075271002)],
  [(24,2975256083472668111774394994549597911752610990987347764662298665520745010),(24,2620357541677047199940623207501188527932163590583175603699490933648101244),(24,1691039632781080132115496305829488898597007483315365209109858209657303129),(18,72975865079914120014329970435333280873094958849435099)]
]
lemma check_1051 : checkCyclePrime 1051 1050 7 [2, 3, 5, 7] cyc_1051 = true := by decide +kernel
def cyc_1471 : List (ℕ × ℕ) := List.flatten [
  [(24,2137133707604805624875430750303708927700145721840303383311429966757330157570),(24,3318611189898440052372093068710130476993418840638773004631390066852243548609),(24,4133197045708360601755801141292630776272339145535481565757476549562012170656),(24,5531482558927845565259679713077853208763557225438405614035810434672330094090)],
  [(24,10217922365911286007104958169812202260612043591899883576343114157453278046856),(24,3811788483148054186037073676018545335513062067227617033082458912377281299487),(24,6361079004049357935870051542157181575696833065900242183758631854171228591919),(24,2175128261966010881269667417676390568057993541079409782736971579421275258051)],
  [(24,1971829499839782804057082990888013880888716641010389424955548622265764525911),(24,1857374189727714403449327724358861096023514719187296372638650782007208555734),(24,7695424824527462012157819704320600612664144470951318231705475952344375292489),(24,579594733878350377995098105366249833031392960332833052802573178589639367902)],
  [(24,3702201945303494812520589293636229194110863527611095129653377696991349094764),(24,3313949695535718075910184247650588095424490637061506117652448189191352621833),(24,2362783057439363562336944915187762042399437648306051045615133121053081974496),(24,3170697607481722623736851583055196639346727084701462985979057415057666709261)],
  [(24,1914029080597576387900827472448197039573437068618264994702846190715146092842),(24,7233623220869964212193219479742031224423430831936894756171802840277643338594),(24,5444417036786343507910873507322825170961915690134923138641886170565894404826),(24,3408919810547448608031286244202625815132764585166594998516136594363395881658)],
  [(24,10259246216669119878635373406134587406326293619741331045950032858444003143301),(24,6773889554102644320659309537924992891183055786308003693226079377583977371398),(24,8261810503094266663341944627618994693708083520687336488184154056011954136118),(24,4120673489968275541836099470299841660415244263586099000450311299754304538307)],
  [(24,4378139374039146069926284477712940738146122742928560934128226391958415418864),(24,1292208667408867660149476931645277423374391591146977569129198103555869448946),(24,10144587418621121215645292105358044185590064686890966802002495703221747480747),(24,1059465548727152405897955570101538753162244930466515578744502227711352725383)],
  [(24,2778240064287307539260167184977144915673584003918176115234650347505216692839),(24,9539511429268929955583749702324715698705219667383805977124420372049621419628),(24,6835662068169035435793074682043850869848123801473544341277528417720899230718),(24,3055386555974174015756955481366522305556906825766219939765588091764302432474)],
  [(24,1219137682362800455773652539551227072665066570114368161964299584953449625131),(24,5857934426696188147678426813348305829947943406189626794610593142565956511444),(24,5677929321522172746193369582577145594164113033103072410483062882954666837896),(24,3510333117380459830653316367118494485715120048182502325798196509200417125186)],
  [(24,169486100377651166323206343912886535008071000176601951642911657279216292648),(24,3863783617476027891380761864821041424891213616656691596016727270533143805919),(24,9646050294598308075030687414179520462161607420476853922662677449626746956463),(24,6374298069440690154330318387036573930657159571102063055455069102971411415924)],
  [(24,7537129308210735476477653818169803479821454306095809131467003409809939015691),(24,8898700094679732238376157263442831169160783723913777179110859264513302765543),(24,8413246555544512978452552514591073422356932205856833685548242815028746219627),(24,4228796535789281528387397507202435220361391171678066837665822093806875054467)],
  [(24,8233591251689622272622227579412684649626579755469901491033356054635699900112),(24,4789689162073563928132690593754247615702615154563549834639829772060711039382),(24,6652230336055832407088831920784733582193748974652637996498701703067594745893),(24,6794343353651672341159497341785067816675377302157546066060485326525646468165)],
  [(24,2533700368947409453130031010707556219621336706149779508742895298601210808864),(24,4584300696661017048115868563111155053289547380573389626809996093531360800420),(24,7854608217513798519881333483819741540216267198074028007409586970776521772850),(24,2649532377481275316119310574902801305801884983751680516206845277389619810945)],
  [(24,2460430141971311658106411101887587582911309834598043706812689259389815218303),(24,10010930847988628323551421940920226185345576723149035400948825440666293466910),(24,754463761487083932864560939470047544014040339373474845456148201723787342049),(24,8663078035198982205978915509302684046842621056133979934667255042676450464926)],
  [(24,5642337194389458853762254024064118092747644511579463183095750261228578364597),(24,6622620728732525480474813448241728422704212053132077693822785298307164484650),(24,8463607068541540065991071374057118801506448294509251942424592770821643959485),(24,8028105478545981160481382387225093220928289287143962043499077314589405374175)],
  [(24,9863296730642434597197423460858869445352169403574442190858634772003292591476),(6,3145693643392955683)]
]
lemma check_1471 : checkCyclePrime 1471 1470 6 [2, 3, 5, 7] cyc_1471 = true := by decide +kernel
def cyc_1681 : List (ℕ × ℕ) := List.flatten [
  [(24,36049565779564257770405202577206969459352124984633094302599329283419201801611),(24,139308579016879897445580955235975994064006008329814651687400169459156772276553),(24,57438515645681115010144187737299650066003540383596994592464051973753671932752),(24,157066315825032491014209894738300471770678374392774265860603954397493160385433)],
  [(24,161691504652951552147458791827386913291571656530010130543485930096848839288600),(24,56684674877945379372712054954404475733018916846909192290698505960871837695896),(24,77751079417783150744702554332089185606667331321627813574255823433349726182606),(24,184609037848143470348686335122343276674916600286077464504579762562362989367310)],
  [(24,160843513921388767916056149315846021477613737048290552716902933972136482271006),(24,248246421270495585468050767642482866342849270947810199327150339673529046604819),(24,213280013079274006341903330482198777527315262144387695643668639301595504919971),(24,28550937233396833841178877505664840853883759769680703166178777854031509742961)],
  [(24,37442004963823787625161200389436665521780448406545515532249347555386401358096),(24,199614417991441144232364341946159718711044292520083529614855798340821481592188),(24,30150718768688175407080145855475355187311784414718478635428817456717475884002),(24,244229968096326346411829281229643598749893784721827419016524911384527286262215)],
  [(24,100826195988105593766318425221233869407525864029543245636831545012085826247998),(24,67357039120659473832877301925479613945095874720129728493523157974398744873762),(24,176410517120871227037480131597581421196315023751665050603758065118824824524731),(24,240409418539885150311196820446927474408570229750333746185221991173644166601944)],
  [(24,167571378348796929926227744650448696510530984236126674704124052476564079174155),(24,141324547939600203794515136414806820722576001986845803522462057918955528515664),(24,54438829564704440151574517009140454260528566282126697398621126372204856314308),(24,63928708816496278176298862666037042683356727191969220390728758551634450972216)],
  [(24,190312482884464128495648934012112333104632658269156799778618921900068104699518),(24,88465445524526447070382605476641342687515386036943245101078235468308239761794),(24,13160247758980260205249398156871707871560907133048617347044571616222162841796),(24,117041227591207152541433252626721351725248056816548222749471721370662964845081)],
  [(24,123784606495288238456220317395939843099858871418523025931485157097100332298445),(24,229330149485527296375708093867009673967196644961489182629792567030613693530631),(24,158655113502819077859071272649565590963507633967265967408048108359549007896723),(24,47821477702630379186702277182944831451171578096664786396691860756863246072202)],
  [(24,4093237490255649116084808113964746105914696502922980512564882387611893974427),(24,166931068240463832848500472940243589856899790689656719366689770288230223548316),(24,40274124899207650703093848420162996484099859745981598023593768612470348010490),(24,223146913398951883224509557928388644860148299911741998600502146916999876562794)],
  [(24,81716688425125888290029516615730336153462311338759841348529362889068057131523),(24,83613367475925207613264718024391211278113667232240169431608820357748923945134),(24,198776266021761426409220630890827417740035138121389278861263604762903208198159),(24,164440077997403700283292888749054214234292874122518819567691446080235526735187)],
  [(24,188683302504402774817574549255909958720634748052482194487826477074153391182921),(24,86244410740978507729272189665595354368933708224196590376352427449682763012867),(24,62729418458646214014329486095314980329777421040944326381602691653605634191296),(24,40724292348930089168061529005256185150755443867212317360738077972793168303730)],
  [(24,150576854077467944100624643262523335966006093150115238473438626368401669222177),(24,24022896255339904339425315799196463170610806427026496944409849947365360468066),(24,80221962193370941316976594270743880017690775035031994762912739195019935486416),(24,17545490505243262451648526095519694739079710474618532909159923491746997402097)],
  [(24,211366886742676704606596937041046095285603702179112651065461520551281405425982),(24,153761127824257798708441466721786139031828001046292979164197532593757978398619),(24,138971452394628959043602130423952002359626635214747015710417627165828130165834),(24,103040209849025970878764115148109967309009410921261130114387557799369239922451)],
  [(24,34250565611345814256474907153057127213285577449112566105615961894347886605038),(24,6121498134459042926201380665502188609735536637998569330624522135817899341959),(24,127242884406121514083341104800721772986301306275857647632374556316666683970279),(24,132619359398447358330944545517038025199754759730489695833320892076807879855888)],
  [(24,20210554598633130452171550751292115510198114319167084615273356021205130178376),(24,257157477456774476927769054406939642142066595706191460568979980896624165867972),(24,244491916038598525353733755708984059264613860715435821150513521271584000926705),(24,142840747441502625265283174475767111850401129838894847209061563127622670869795)],
  [(24,258248121961394333692595561429356083870926418997900033383061242625743893858450),(24,174820635661178165768816415215429760938435141123468701549161130454017316434896),(24,19920329981309494976064192864430674527376196481986403585948245390342584318977),(24,169947513192767833559932146770886811751042290454643389034383705107824052756757)],
  [(24,165214736235227513082928119039825493742944639381072604379203224533377508854315),(24,203911347133257515660619193843148251298863387121297686004850758378336955671533),(24,222946417433247723668964331235870396120191126798423124006589141682722779527975),(24,214522988602977877979526119621620366279151539268050045772997312857221209261368)],
  [(24,132179575528379959431341352521295530488481735803542663228809474526503047459315),(24,217599855956409151228560530279412685368785082211419888420036710402532495461609)]
]
lemma qnr_41 : ∀ r : ZMod 41, r ^ 2 ≠ (3 : ZMod 41) + 0 * r := by decide
lemma check_1681 : checkCycleQuad 41 3 40 45 [2, 3, 5, 7] cyc_1681 = true := by decide +kernel
def cyc_2311 : List (ℕ × ℕ) := List.flatten [
  [(24,392802605263618393980376261167273869839440618100227474548762174792160352091827361),(24,535473992404291919837689190608096632144645270422685302698225358558844137197355655),(24,341658978999267011625887930402566130322590166910685288213524579625084715695275583),(24,230280337405303902599046651245600951187472270325652068748615268753911028027391944)],
  [(24,390993299229508702435633859359725845259521600229552003058523590916493007684448325),(24,178840038409450491716829347744834402406059796130762168992200543148225277390474926),(24,471511248291117215624776347961365827044632513362840245121227430134455233188080189),(24,475649149829372965762286850815534067243317172382924032778286149765676756488192386)],
  [(24,146334665690068140834704250233534275617129020297447455100824961661839238645716683),(24,25393635830054227771949872554662864824918438492856085865745526093606305783169791),(24,275906914570125660973612897449447956042342103359233442380346298015106040645462271),(24,262143728463013544644319491695079429280552163371798347524724337313432131883081266)],
  [(24,139619095797803608812205608031231560022073151642386941479613226825825835991669833),(24,394532716434038506185078323370823286931861312160767702368107293434099594980671034),(24,85396502823141753419839791816974997347145580357691186866723416063941970910033546),(24,505620330109806467272729194786268468736930637022691193243212983442722170309705408)],
  [(24,200612271338129684088072301820101093411283586583816703982005787040249746860932434),(24,459979561760083389745502575419129118333513901397809314554588558338271051084314032),(24,106150232909441625673407365486251152022846143917718572867475148027540947307793813),(24,255821201304129786662930840737624481651413278305012522706510509250944889527667488)],
  [(24,369639577957364816275574989440485902532018146538717206956738070048922213394857004),(24,138653226358216744674481915894685386353010217784929623368660319367261196753816869),(24,269386898201722448733498506756757655966629821262564647929245374144147090887830872),(24,483675149877220952062251777241307323409129045817217466852001114747780531584948654)],
  [(24,126110270862224762449318391137041208299783906284758415480237387567749149157670343),(24,321426137778181340194508423450531495376914487453631303536347686523374572995805307),(24,389754196524357144605372792285993293846537077674764080734697654086979994384105924),(24,329946339413504367534709429645385855571242702976202327305086040526983775345959046)],
  [(24,201750505722951831642510073755525365192665181438642418079210426393476221869387448),(24,294182160443095044976099182737651708881378940924474219582618778472729974684193961),(24,83690164619502409326928977179218809646728709898477320024075410056412852261784959),(24,326920627526826136929456385035550002150306602351999308803825204663520096474897077)],
  [(24,364119096280708266304798970457486732047385222562743430470626824306734061670126232),(24,6379426717107193747171977845225860758563508318131335302926770014156140257675666),(24,448231734116440861577792259190496886607532380971184715108747684139604637768328454),(24,376661245252816407888272958497284959180646250867550185503721289658470896196726539)],
  [(24,105955290908252585131103470679310104125483469006990571219177880404634752803426728),(24,177584740000865720645079246302413648131896710711358079217744857696738623420012243),(24,514123129813112476850028422854276442136420946102974757482351734339837477157465883),(24,374716367558759833038844956369326093531420017487735387429611463958553009981758437)],
  [(24,219225107369423778638986263239113831697333511678905586268751308352830991199963348),(24,108887185997124891418115059329278195676295595608785938433413488269542007002080461),(24,316626183093247737378829001875150659290146121227594806263232514273265911815590083),(24,354673102852874408602363151787501652246674513477996668169840808870951822995129055)],
  [(24,283294736802005646728035717023714310646699506072355494882487088318257560482106761),(24,200369779148156995716572789195170751077253865859229199504114245321073122670024452),(24,246511464614946374337931124825942577142298857778624100013420981394668178711078733),(24,262787166260651005477320863038116694494153358973104953069690339919228947520533185)],
  [(24,133574358626064557453618974084426509927896631898567118248446538772017669522576677),(24,492871694037579928886590664458589527477934321724720466633445663359296620022916549),(24,476826657079229806036685359896138173932260562067429242717486086620339287426548086),(24,209287865798148668765475133737702951961052734834881796448942481577491597899008529)],
  [(24,534100024778994417303027732568211843397697973664517256061782101333299674033759574),(24,310468462849669253186370606191708163097069517908721401988405109987306267456536703),(24,335209999692391056415045172863474353940670625984404322092067649317127747931290004),(24,432064350244024626347874820724416237639212747770271414705037063044619370670115438)],
  [(24,302012990298893870151242260238884882603123841392840413200334893891187713231401895),(24,218581535151924359122516956213703792181556745421280321347824064223618796348752679),(24,72960845150376741640356440526228354988518754533750693243826191449760450518070461),(24,252050443098772096157163822326490054495507189865898545246268979786327601222258275)],
  [(24,70976644189642184693104611171451190407273437869354957138409618307069996685084639),(24,11508203220537357314872046862356390693541934164360689147188010851849614012273135),(24,95679837545808635022230389062306097611710413074794090878624706397342074502667275),(24,51421804301277275008558051531379207749300032400785604981137490196352397595006913)],
  [(24,272493189407984788985933819137569817845494851607325870498701036653163190388565143),(24,188624175738821918050542768009331632070329206247254434339739192177117827091503663),(24,22060533179292230008530441542589137183022161743070915192443320806569157945211222),(24,368172150663374483056945977521208861798888837565545566518493953963873551397163331)],
  [(24,63455217250837155876291030208215777122232961394641875455207845149968057665304118),(24,25947818103092054526246585187136407556456895624790255472767992145854353007478351),(24,244477248053991577160228549483679891998981729007267188286840128036763685435140329),(24,483146226590734759778426554220998698178446745794453015799042518696811864961430826)],
  [(24,149052579908859399355717769895476212199207706831916558997101714978676402663023626),(24,142923751080770850320597261282615373853626564946358625690114248691173058533834895),(24,114335872825226036799660378958615071710856834988435020387726372224501682204254846),(24,292408103580816889985101094419689756584516262629941074696202293680858203969431917)],
  [(24,113083486162290058696432773717504655852025624483099262774657209387268508032128949),(24,490457930642221943215311691468004060692715738353263562381283116525363853695266758),(24,370794456414838868492121057441994247530818689443928916198152597292669050816657085),(24,436562266537071292798859792039915183382312739913224778851933337134094827633458234)],
  [(24,46817669993550683612111189615841004402156713423378406326635958285773115366504711),(24,237857698378854840468767337200246499411946371908166018364715889652241245374959400),(24,381674169870185684180148340539404302657235658411671194420579057429831038998133180),(24,7371971132935158491231125257427133679585425682911818200577918803934802410004249)],
  [(24,289687217681496457421902088368353766224418160780582706303528048921490468495310588),(24,239141451482523593106053055155423505384825500210563473095266681593492615269463768),(24,278060271762556725999214779351737136435116531773019889722290710619955979028841415),(24,452913378961954835553293869691768857949460242650259956497212164753029859936570903)],
  [(24,312361534133574008082735044270012618929050833354004937809091712686592099084199535),(24,111484024016585871576124784444127397336954579801042563991134064145444480986200670),(24,382833397046229788355854168388794624366554317174350502164970956166420671840269714),(24,515027298926855778606987966950558780120992879294275076722631907947079392451979115)],
  [(24,327519599282669107767117069981081122426393800297277000258773034661823495809595586),(24,14364479939561151794335418816106572578999991784076742900363905990243020289430971),(24,170501619714433179305534238646032406051434975251231425685962588520644419953871250),(24,177428185378591381928140424210782051499005230748490950013350433118890346933543001)],
  [(6,116890139746447313082)]
]
lemma check_2311 : checkCyclePrime 2311 2310 3 [2, 3, 5, 7, 11] cyc_2311 = true := by decide +kernel
def cyc_2731 : List (ℕ × ℕ) := List.flatten [
  [(24,18276422749914263842439921293607823018681488907747009940665574704645460494129779270),(24,12384591255794798582238882429449200198555420770613772974300776297704279554513968880),(24,19631124917849636277555453025046912881239651921245494598288790264330394748490237193),(24,15846031332856912169724916649941347234128711234767953609157047955597178163218668170)],
  [(24,10830708472215315294662516921867479656607012442209996910484013289261288900958607873),(24,7493325411922892169997563183983054241019300802492830262647609042685556993912368075),(24,23905356238574196677719799415239759656766941420334440965248905397799754677704189047),(24,20288659131706742586755237023739718768022093875939122406852432573634255954981326246)],
  [(24,27557590478429727404641421029608539442083903841980261505559474501715529700410796301),(24,6905090437728690808815313626526302813658596730141167213634106480102392683114213038),(24,24629122501365811739630321476716095461657652932592171817374615533933164432660234356),(24,4836315064936443685051730833270005735547472916734765831170756474341768659312644328)],
  [(24,26872936080887993517672347673459660634547122599142243500062375234676578877875006653),(24,25551141217764198888891396162302976563236056335192747232314229085370969778738094173),(24,4631401880339407123100499458132801180359099665440478937822683591114188576160551180),(24,18308082122431588659586305549939117765259298007810750560586421834607122534640139109)],
  [(24,12329699952181574159684542025033603174833809638190053068677570899812521393796865699),(24,26566485658653855622273723210110248183635248247403813224535523390351600713490143643),(24,25468438632803742478333166530322089663538299932256712533774951168773745326988298894),(24,162359266089313473421829873302514874222934950165336847924707979478362320767061149)],
  [(24,29375009808121440879955523702009227243841086328013664553511156747078744502839366748),(24,5995228350217755948556529562169515783668025363022880773177673787744432139737695240),(24,26728824662388868094065221161376501807554987688177838015648856031852217175467552658),(24,7547587746018138387104574990837603219129722734347247424329127904172075726950808513)],
  [(24,28373958191919641805380719281830331369126742031386968642229373454377840313309848080),(24,12042117174560995657648490563108595366852758798143461282200980037709425139918672479),(24,2267929487508938418344481834283240512001030664997433446160079479271224515302187900),(24,15259746947666181025876692195658387980190607610751883605536323926418886577999259)],
  [(24,3150164037522099602301938247746635917058524506100447837469477604835242514766289014),(24,21029169945318829919021060537892329657963005641993277266219669272151571203115472465),(24,5578444119908496550818754875351751422091399074633816721542408378225900998578592376),(24,6979507540179982726235879920995646908348901850443307149477297074089234290167375100)],
  [(24,26249853913210646231759839198176103531476540625017454866451760501594507626056920520),(24,13854363390340542487720460908429892318763950514367394955584323237587068347475371237),(24,23323385658027357955611579230453895480570553914302238941695082387938375855294793474),(24,29141993770546738612119510430892499204372927163326884276497017698686467663655920893)],
  [(24,4512926583619966966641741901625190532340335615379238833011420523628980284470756585),(24,9485579476253454628686098052105801445772696951446270179035275847905588612101158573),(24,11706202154254389580769350250942163428539117581989077482499331437441925937876735860),(24,467585645269864177385082699601726258077212304465845237565007668676897802959756241)],
  [(24,16043841715875689593715592676426283988318963975591246422356687644022840820730538239),(24,21152631665047630632669197830253205158963235256168702092737875989552825859512821243),(24,14220926451551550458414902286224131691432869078537457495068242728418010088100783543),(24,22689069332202529585533707776122176813182404490088721137487054074547094041301593215)],
  [(24,22089168226307479056594935599592145628356424997481971610294096012573828922431743786),(24,17866575404926746471289300402196451628140502908414049341085957699528958244467235077),(24,600773501771953757159212941581636962527535493088770128410372206889572170539236959),(24,22735151994079239288775129941759460342625691397425304122574991368998471559558764115)],
  [(24,18330247775567916736999185620416980415632164306274263714142990615254654818677994540),(24,25287558534118744881604284106534299885971564706439428448653018407184139971337768638),(24,27214339192701111386899156000567091093627926792314340496992370728288677066773152736),(24,17071198734454861980476062676805153899354622443394912413169032641008444379369867255)],
  [(24,29615139517139450378328743669560660937515863413803248066478957377762403350221942949),(24,15355487861478389254770707283501112977949186279128522063879528376839174023509787284),(24,8206377931646646001626046174493368417870946377926309011264894165137717226702636603),(24,13200463679853740765192401776807980229240508757885409703706169554078817355924655252)],
  [(24,8358956704528486570343242811396031313647902875127501109070970796717232998702195721),(24,4705377594968639458706838666243245861809115429875537056078149195518637531288456996),(24,28752831806411544933884489525807668153242003455488651252293997159059939611105253732),(24,5357472671633019679581537577321303006661779251859946883562215469085800657230499059)],
  [(24,2231186905572299030649066787684252594991752204083077377038709992545137169416390970),(24,27768353249575408065612778979133260344243334942826590094843018793356260155430098227),(24,1428664614415681288554218545447490778015481269680062637125946718048586776800249873),(24,12419010658703826161852590221045174570114953077200407642760381694495735914893426914)],
  [(24,20618715049474677006773336299433877875368303135711697166095584108157309273017421522),(24,150894110599966077989599724811354599605250508374848217645252614008796068235198087),(24,19760235538819425253792728680160051462612279301687122686506642772029826964718603116),(24,13666583539195470226080204867637161040738034311940990978660242198112233431656318204)],
  [(24,23858814732580067479666397836647519634337228068870778768932464900834345620546152035),(24,26022067910723467123776551183127058417939048709494770886879127882114543839132585814),(24,5155815643112938054366905651596718562831482705196709111539061959616069888591263123),(24,12867119547303661257900293587019724734672826838155283184512389950815685473799242605)],
  [(24,7382561094973969492867355639812982016175786076342458897930225102580721568772305173),(24,3911353544989777455597795825417265309976730132322561633292585868250676876561809273),(24,21593010244040475594960574429267746591442369028807754297937331201037144827809165127),(24,6491194226968347870759251243788552295167869843480148671333951798062166661590991682)],
  [(24,27255335051352363248188977957156290831528118805447108733888282809833056033265371435),(24,10855904142652272712825173398295968602855354991585883841704537232794236436703309395),(24,2132716619358419015441615317967490702584717460499104913381384278159254752290758408),(24,13518424308810969943282763170540051788367979469129813338648208105943348492773749902)],
  [(24,7729521892536437335280363316357051356076886714348360436688463136877149616987704886),(24,1356225216103353489492177548965210984797839412664151678952787514709621750118626048),(24,1566723834417345279068532716340025392413985640215666523067729597388771887844634717),(24,7835100099819549775271449961916539962719675292190646704010100329311373890650163333)],
  [(24,27154482234241634340106179779922969243933687103675993429873891011681250079861727541),(24,2697013499992865341578684138760482829772862754218016029551886058916204997582773932),(24,11661053133891125498750675373015669542826443385275122285278976392799058575530110813),(24,2364132693513453789216423036331752795773087053151785852185245060846643355027188828)],
  [(24,24208930571415247849597089107759277841765729311755962410424369910648408995563155583),(24,11320699505006113365335027124498198753679866512666131215130731273915151582784251888),(24,23956589020223765233274286862379513659996019581457889733020353090024037323077963567),(24,1869796265780510594265195785577919360199692739248050947060824568151832195992992290)],
  [(24,11962432991816682620906902530383372642964674162011748806412766227067425938830694395),(24,7275840864587972979148997573880574844465227560373272282389800567833077414622782094),(24,303379537083329028890740383928614383068957520693513662570227567019069088654801503),(24,5300787092561366699267129160359557914246679726444041219535596715297781717485478362)],
  [(24,24290339934766628748123151098057845939971049536418105716662867233111368107450854554),(24,7390276811174135640824520191493118266676081600394026573063508036158217967959295658),(24,8120898842400290336002949538082951030639667283406823954929456618004474016957379956),(24,362183889456230757854790828797180776904074775089892236987036147918338649703920807)],
  [(24,25356409197023217017245282986601899551066158045263568486637403374336569286529061057),(24,17319619562798265618261608786680252099772436579210652592784406812091027002326987852),(24,23598948162772507708370581330579696214378591553855528843568469215145157500778179470),(24,8940368942984236146883948734043943458906419757623602732652252938278595193699147994)],
  [(24,18967198274097127640177087583677798874049767534129630627349765528298570565060154002),(24,7640449791152673072447726894162895770078918223438322406115880021476088199940410075),(24,6593523062682160134143021218079267691633004882363822751763399716026879539118754537),(24,16798161809446003450699056352102660358301434713687465696592047277244442739858717532)],
  [(24,14989721361956412072480387582228150065974939014543720387403832779413111893165763047),(24,19493536747711145422524577680256998155705908267688015182797354569536006430288962824),(24,19650587431633051099672332880710709570896983480140220107928113509123361106343750672),(24,12921205174605535519443138963365348475561093535165625504287476841844739720289086817)],
  [(24,25920655482731865858509555502165214760794364302929450191167893805264002335014399015),(18,49068420841950968309641000394176034422252622440100828722344827)]
]
lemma check_2731 : checkCyclePrime 2731 2730 3 [2, 3, 5, 7, 13] cyc_2731 = true := by decide +kernel
def cyc_3571 : List (ℕ × ℕ) := List.flatten [
  [(24,8349566852108161176106516309831364926244156889148377613421805291336416763599817416692),(24,3630895048998803663648510153796494477394537295842253190815018769417586815825883038115),(24,15397300422489888930097064710698750449400779944699377437657804165246499242683200062621),(24,4855902430696080137256362201410207310691738129044176933492644800365560295506577711080)],
  [(24,8457031753769649815282236169151890402054342502256872466069322596456819889432488487289),(24,17312545331031004787245986108081525517492837601231856830978552994486912411184341203261),(24,10965631812908411762458741640706609443706640652555174710222761083079861014322967185726),(24,7555524961561006929256128533394125430484948990375498938767698497531798664683382644479)],
  [(24,8520208700562081779889909068731588076197654579296565438111187516470207384799054011382),(24,3185419435383592398107043654995219158335770332963688655797754943538814661613149840814),(24,397655061061291483341867335168116414754887947895523222864096753404957764285060625152),(24,5003188543081763438551045557178184610033600600076845213313639610542250203061459738138)],
  [(24,11953983035248687410300623093427223002053652527748319772594589895308194033364645587250),(24,4061399792117856908662282841695243286448762902433126692429347527506827477306221461194),(24,13289490208053070905076790870776880962133590607410092795760148112089692937483834608730),(24,6835043411642174869852133924910332089687244122579505367582390093220068172360645818790)],
  [(24,9649362323222342578676188030447771006126193515881087749748267360394654161179748180372),(24,13094128235589084980588419320075693810603017801898024053860918569673171670382509723377),(24,14191048279466361898303849245268276076270894389429815511359173393856387625098292552169),(24,7602490128348686591406715491277241834475985208697632135740017610836345109208093208613)],
  [(24,11533935514845531563542632252601665586170378656640470074928795553897418330558896258489),(24,13010549519879495195873819248174208516245530544393551356906568827881516477516189527297),(24,17902601044618023093092775241563941789009083776179471635430716418954944494157353006502),(24,9867747883866226755832432111680749875740369780955781300888096978673037647934814737474)],
  [(24,7979125188846076233414961096254943520941147111620628981032307292726177954038809078577),(24,16330122040799795273579237151048422185402365655025708551267343459212070831138884212248),(24,7263536918682722334033122284651354870999400967150402390036539638658707856375302097703),(24,7615677181508177423707446362964153308227495397886941735944618954484516110147722854180)],
  [(24,9299770689451477827879392072951054543424278969126796298206666655354381274460314637783),(24,17888736418264516013813308562388312695623050699263205119957955425663673762428401736450),(24,11848105771873538105833639441523148064141325646259155450069538382311782708518216471805),(24,8078870184545223196708837561919307269802157210483774633912037383019998892288725610375)],
  [(24,6047851517455914799587564698401252212191966275445037903203692756649182007791310793722),(24,7680362527106211227457169362460766924714492339658744883483535525906326099939183810664),(24,6655793925149837417522124026213226746656774246563945242536034904922261136253833858374),(24,10362928803363419713463457473899255099075727276350689751335276194555150966507685014864)],
  [(24,16581313019387058274803165459386995498737553389838793834561362875964612819294717163358),(24,9821727534192409188074050535070553973563179751439828715993618321151305325628021714852),(24,15000848425798279608904338584034627512031340668274837125823442943879604225874944031533),(24,16500122286178686597281835458811817494915832440377622197344973317308477511630827335547)],
  [(24,6361722906775488937053266286749382834123597863019367295453720160869764281877240838121),(24,2873144469338495944839860338636022724253747268461169994809110879778127997547207407056),(24,2044923122732102892790429796971440817482996161840839320519971130942922572188232018779),(24,12240251016535942635647062735272125195588737472362158931199659442554314861314734503465)],
  [(24,9629572871824011846077489108000740414819702958776809345054235098457709941527389417157),(24,4614066033006477620943733707540574220399589380930529181241779970366404362563555389194),(24,1234314836199474995511384336117953387471099762936650985253959776810285156809562119748),(24,11155793906419885667672833096328004271595238788451833563833257624210749932557490063335)],
  [(24,12671154222951160310941442964904336201374822039251856969951055351637790433394364505459),(24,4362969413889483028802865391261583642016565242555783948765188023078872380367707189316),(24,15329605700364331488027544178483423159220165390505075418947896037571612094540991279975),(24,1357685028311392005929344428239114620485087630748158507879559984908087885390511973506)],
  [(24,12309258794643907975037693804236013423158718510986796684749167597341873026825073755434),(24,13506054498655368491492916796424915770526747453559559789065530577855823772541736652914),(24,7424252206727764861485787731829567914878584567786221187953168092398083129436887879925),(24,5926585082326916109978495068829292515283627450661178892438055811782627361416379730986)],
  [(24,12969774931459044158477967759426422906919880589957315981847116041140636959257472858854),(24,10306561920558853887824825945357992304937711523825843683124273124633695695032826537265),(24,16198084481215890204193278250992381944625211496052768521568704556255450393148438704181),(24,8939886551053401898645425380506950159862125298556817456868747162736754506639010846066)],
  [(24,1101565016884002402057429369912773054536293565275420335016167074611326430118006124836),(24,7525751024239632345682580772034715165211014234723507979038852416945717161564144428381),(24,6555661954931881512651841178965580320269216192274683112846190397359182716712657325021),(24,11054712839435543291741407738740440473249400847585321614065221015539421832197229534084)],
  [(24,7249045794433534347694469687114886553323448282688121932137470330574166578522541138332),(24,10595395452585664424595354570602536420863307619676058265820549045185001800688241713872),(24,11645884779753544776108160354894769437347360015970552332393595527225052516502068082020),(24,13415339148627378086634962043737823135575657576738277515054347804098904645613752190465)],
  [(24,9901884390931728644820424757135710672651348076717184825819826290998909419597179686738),(24,11572358199286639056659313006322440564320085758347915587177314502627838762399382831046),(24,8188336796526081066086123594840916321295724531617153831531885588963568086643082091316),(24,17132443331021574232403580321039423246251613059131437178933935063010648115607110182058)],
  [(24,10544787171741753832880991159120625865838172450838246155266902350752909467467334939884),(24,12633589112802305058464231739971707208180624999154043701848017105637219468947478261612),(24,1273542561562886236598450472097927096985310851791951391085702740510896707620669657227),(24,11628227348077806356569478547039869461250721918297865788944916502158628926062823393863)],
  [(24,5244417803449032953181767241335523794513372608356915787734112455176328776562904353696),(24,15483583688651592729470038672664097385031821313170199564221584904456447670120168688791),(24,15573379650423866594832288528190905781789650532689959343385922060944103038242652331714),(24,10147184603598986305139289301012106153892623940172495845230454016203420591199731994291)],
  [(24,18281420993603270247470890702887669874764940066331441264388374965276501406445054660975),(24,13456595525113212303369300981658333663155546839447436671699539779497177190686936981794),(24,2952985157235448142995794830589713831473541697137611393543791659120879271545426432987),(24,5820570912095016430557133715131439141422705752833660917365214015683039628432186572278)],
  [(24,10799146363192889058113054089670202969458007073201899650781569296907223356755040127440),(24,3849010303829922438653919514222528489168028615541898730561894586836235888896963533908),(24,18156746292816935774600140023872303497334000708765862306263130253110672409088155112333),(24,15334397401026383821197527905991785678450655250360740407218286202581445961397126998239)],
  [(24,4177677134737196452359614403838308777293291254013528266962535730037133725474279595915),(24,14302334092275185864447903901578276004171820211273716523451660334083058190817866879341),(24,1246376881799156343836985844246412472341101485387108217267288025240140242571024134888),(24,18244473317156218083262486477138242199907871555852208693765094921823004376440394029293)],
  [(24,2443731798906397502481806670445986696531993661429079426004904427022360697810058534015),(24,13114775058999574512172561924392556472303944748832237789023743560209686451542731624567),(24,9948520106248072017508891264358308397921635050520307763411819636087913695304135616857),(24,5893891342185999986244089359492637042589391115293081533283175899910292028650567065227)],
  [(24,16518763710481153215322821857220432104118285333649998780716180648079155194592129042193),(24,12055278099948212213406386918221102036293483041987776574907976969004852562344747692302),(24,13255946647934356534200046868743149496893978224854928055357030282035687635890304929335),(24,11058983687170733325887170821787626212534349281497022415699533981611855345010018335040)],
  [(24,13944448721569069234189348467185902269919052657416536338410823734617680341931634258169),(24,290903979526923362696813523155027175154890247092390886162533247164371278327426831643),(24,8700058495531922221180916972261237091504122023529634889274499312343724395415383189942),(24,5671377893526544146662526182809923348085325935447918055253758752661059656742515422410)],
  [(24,6426494994996234356851916259229791908700978357159077302702477823954140523195234726255),(24,3141108206865032440664187045955968898489227606484759981583047117352656938731283852606),(24,12635164350354528537097373619893467392468148750072651723568297017726815269394835719534),(24,3484984725805124107292850774381847135379281664613155251639301136900935224744190046666)],
  [(24,16366902145355671184547700419750850226191150853195529431344551650431340655304374144101),(24,4281295102963888348877042550477216713653890287406086806956013655966893931744948826003),(24,5693459396029185639749568271606218933773002355731068515360118782366427638883581936992),(24,7297952663381629376290324889114734370041413648109364212643832481196416393428628166259)],
  [(24,18108676058268468479489532184218165103544967814286746963348568859008741212139393715242),(24,8301063930711857435748600350071636910811186780386029641019358064683805709452461714289),(24,13863800162091980456403707936072711393294920070293872696698691964052983110776095218752),(24,2555047857503743650208158563639012643203088842577448521332686040441569380196017754910)],
  [(24,6495969885640771613940713868637519484751670287738417481592288254130015652170977402137),(24,17835019164324995294926938979790411554949548466343755336036427445043272087939267849513),(24,10226647197538318315978357435337885139511643080927775622186390972478234470396176590455),(24,492393994393989162537921532769600321648697057862453091511464160726862691956294546846)],
  [(24,329141693151987655582730200172404446105532752260003744112821465012578700257812164309),(24,10291904658204511047222970946664330984296053076718606170050067871083428207372718563612),(24,913888640472327047615754400435629639909724863045522287140012018912468256393499466595),(24,16879834888552340221042830147856450833021460838673879773583971826497496819722607019316)],
  [(24,14285667348506675523281282434900868490033873240844439479527795913240105538492923243040),(24,4428506918460816725381942847755171398222270101194851608225982933100426559163689586542),(24,9961329011219133667495257602828517491627863447611932636253678348637959434195384685739),(24,14857639663109356051807388568680907370870710676573418555636991385688882890083314293051)],
  [(24,17021421872032380444223209453701907863892312319820634251489798752304431354630473055783),(24,8772357627664686043891582227913621351536689285057782482077360466481665581496961767748),(24,12927180549463347948401732463928888589697020758455596744629294123186055776481829968214),(24,5532048317538190723570960150871301307426859162708909995081799419013086727239815513998)],
  [(24,18336682939954410204011826504947882617888034612619984419519600395455841518557643894039),(24,15670533503578114465808475867656989499656408454102135805637752846845399692442701276412),(24,8771490159768686139784263685303164706966188330387173151127560630242838186798715795005),(24,10688039669324273167422100197904380043410619987489415334238094392700420157449180941025)],
  [(24,3278670027203040205709545720431213470255483884188399234137039735695220965858989017929),(24,13000137675045073519028488281776416637030149803754537370887415527853563798363887726893),(24,9017559630691620429124147746565880304796308140297066145157747667967060325573408591866),(24,1789440283625482947810218167489168117295161903724352846780848048732017564024959670525)],
  [(24,102858249380668160475996065592831602114765890533714557142605653875843171546232872087),(24,14545172281857032507070807078494859552651623847334623548575812454406966373214710215860),(24,14420009362849820246130235013779783200703446596066775706004839053351886824835868414861),(24,14594587789120084005343791514443039624857540772321951222797442948728715832209433263656)],
  [(24,2697578693112487461512303621012532538182333119250908715575051656973753297968739062057),(24,18009407692980883499718601574581409125882733247628395886648450779915655090037892653607),(24,16744674819891586357546178760522442647932337679197839959776794518994630298870794559597),(24,17798004612084496252487958597330514954580403914415691744655032905389939708923487558680)],
  [(18,2725566796695788209030480793518830385778874966486150364775983824)]
]
lemma check_3571 : checkCyclePrime 3571 3570 2 [2, 3, 5, 7, 17] cyc_3571 = true := by decide +kernel
def cyc_4621 : List (ℕ × ℕ) := List.flatten [
  [(24,3779769058679081894311158856084544264078254025738846607273088297172142066469870774143856),(24,4504013250302304222371254454632654557149641723236105420568618234937939501536527307248131),(24,6533539538512794497946326808853624710141856848073130023864352694729560497568900918027436),(24,2584786758457623924840365477998176920413689620798123804508928953192583113698617889741047)],
  [(24,6921507017634476416528025218923259109992402997712606224888553601556185595103902520167804),(24,1148416524221163686431071729633160275693101485503651613732658243659025368147351853496987),(24,5287378460121933215722586135632596879368199698642561880085401785326283861653895894598375),(24,7706677596673645586807355037132937726831036896147805649327438950204620602345368150566353)],
  [(24,938654584711933110438452208891616423681433415811638711949808411200018753843701375795982),(24,7805647223876360453196059914060674762920687159886798060099701213013761518472798056356974),(24,7245464793929735467059777228741183567963151313537510513110491489260855406881665219717594),(24,7173163798449925723301224098638622958131737094905449302395299534503933888693486612632524)],
  [(24,6644390192409125905905074995633513982853507969251504152944909815557125162444190027053423),(24,4765322794698634945661636243538828810878169973499296195735593160045819796644903958405482),(24,785477348981888877843605507507628986962541426046939242366733406437298707342782678519508),(24,8645302300671457100627049239763780242588813251162689133402531578659208883706358893991025)],
  [(24,28007729436789096310297563208065640655108236136960934877621403465186790855416094382784),(24,7392122318863280325852726283099506785243833696091852969546458756113586282459012808944190),(24,850808249089953804838863709616580516862493225962826999715291848419675522381805412256312),(24,6781540883133021096399060423250067168933837131569574103647353712828057829758501616883497)],
  [(24,5640006673335717329208896236059011797722425382053904583076918696533870707160416261738329),(24,5607083056219563988248967489448221733839184027187261780108611740703435267812509816116063),(24,3147018346262507200080820860473661463965785057405248939771606310270410103860036280797959),(24,5635461196826666556479393518755800285775515040683168807202496951061638691247130359336825)],
  [(24,8806591161636614115485043817917959019472172445945623568434127732416014529715033593251510),(24,3255749783195180884762213429226834563418856881653178308366238160884660031619284130180989),(24,3188050839963665903751451320128098939997917667836941317033402635003341365950728237065760),(24,762601781890597581220340294898025901102167130830735430716486130231326371681981309178240)],
  [(24,2125067099634590144472344051748266126401371316094160278622719866103748797444145721845833),(24,5389218784811753618982233745087048521882332667486605065166345985210236324606658734462848),(24,6331473886299944433969785139187578609426184993942280753121231288779641337376098789341449),(24,6309280299406028185224001424425969082817602427960031211705189340767315385001963000045614)],
  [(24,8941536619401060448892479673750334764748224943618781318070380327091012290474639378665745),(24,5898606360882408122653868313554127483446761442089821207571970320463674081269075016819741),(24,3938716278185580070369170006479904174977145094156958121966258943981407552776786308017),(24,3042307013836961268441772756103534122062350558701066761290476275136563126163161878981927)],
  [(24,700508653174026301511463080292547544284683742694163688032647077014314257229436800021146),(24,4041169361239384646727380362279454490896376155941125938969552564343233742348482072631886),(24,573008520536621018793600199247817685119703055408480709255916966414294762445699664070753),(24,4554073219680489799058150714209420458031099176670669819417978095447330515957370864050661)],
  [(24,4244650188247463036346104753955319488895211631100555611834190887784005867657551597700447),(24,7732118503170395215831732550589799467874867868617429462238144541152036290327185400219643),(24,8301996791110923334187064589577082318164793879360874468187928685662045699537776766940287),(24,4948111109739149755945003302412671054287006434161724645497794352598712465398549847854225)],
  [(24,2520573045062612525448877558386919364957188985291877194263946068025263669988517720105664),(24,4873543886229596146070140502966291117144099243740885827747346057889043696604001555459193),(24,7219217350909988282214447952394015023316468298520864830945695581373440354475099202272512),(24,2154843310642397935033242632221460924536730004990992555832693668164834565164285772817947)],
  [(24,6507988704170615607252805108655853765592795439743137791480502348034169241988204923073781),(24,1016769948026572820531580427621310059746428018994301695372442446202924423743725875056610),(24,6992351647287823004906647236978238615165537910932599446998100877749918048452952981832543),(24,3441743907222134661236083132999638470442614678673970271153499102390408185617972717322948)],
  [(24,2327422109543521741655920788406536942637826156879788791816042873629070524484980300638128),(24,676711714452037096516809840987005633291868846864360847329282926047544297347340057205369),(24,5317556141525557451424235495475884413421996575170505968777113078056877986138273105316481),(24,1292725290813599332474658205196083827052036220725964588727623079297641225694166351202649)],
  [(24,5186880614782089085392349171813616222901099144426340730932524615873936500187417451253695),(24,4202132400950250329055412133473583757190496433735411478474847372728208647172592185933577),(24,2106204358015811143582963076390277086034213085442262835866135800132585589389757733860480),(24,5878085369540999897603460801294965829964113711865222610145314654111935124234249193038210)],
  [(24,3601021956716308085167426317974380898135184669673431686833042897156054298796366859843071),(24,6307332721912543121072948449806643180823098992929140161198021621778387014815401215408384),(24,1401083582162603995875293087205897032338870284447038061278338233969991579579542812891014),(24,7577765885297940119950380918304345290274577915350242679217838392169735349294900124673642)],
  [(24,1517076034986195646092510729909296180522141833998712865836937131015286435476579503081772),(24,5477460587001467242085272337891980488922252645292532554708817743027451225804275720978034),(24,6466881711042295834422988863604298563154529940131110495143163894166362156783275377352752),(24,6743480069313224529560990007679731877780901198743279166239821278061217269039913935815922)],
  [(24,6023504275416619950729903645488438520831880693083361360061251483613400951772262543454557),(24,1756367805893864296204298560037430497113282036487576177289210888982173281730307429189845),(24,728004104433482061850844491489731429712838601323023638079651618562368475837123729753309),(24,6955829415484492438731232008466070206192706962210287642227911231991299442616725863721663)],
  [(24,4984225077801699726407099636326125666795202653849347940791241363024371619655104668939577),(24,5809362690353929819491111773650634001912187252076365546513485873091106166210010592455019),(24,5979329932068543643179420353807668700594370012123204481387329157249900260496597942382068),(24,7561534756159009856597986541330784462737143755303144986422954910679267497054951621648849)],
  [(24,1981256579363407366284155460720290508521191346584085142243485040926558494207515229707263),(24,5862068558746620014155143464243412544940890001118047639129567625313090113864466747608049),(24,53895857396762819597454383545635207152153439154343463041929515662384347840796515781871),(24,3968157699238472853599246765451073623108825364359441960227148264512546044817806281147748)],
  [(24,3971267030490035857582123018537735420691515188623323014473241035012280964647586036564747),(24,2800444183932601904879958081837659349795753624756208917004226795456212354294227526624977),(24,3627926173484868728737623661000733759426200172085533088364103698513982949095902612039372),(24,7355258472558221329127948023640884219218816475511137713543163810169611239692281621781494)],
  [(24,8107807854970939261126210065708378391201245571485091053447550878307574738302834898716166),(24,1808428963636626565239772409481099360076128624530788207138546606766729533605347851944833),(24,2965877096880042660732261246402338304188420954835378653709587495984246879177790244322803),(24,8528798623223308976499476897396880093127579251870030814727836619032907066161864792786578)],
  [(24,4029918289033738738377161132008274509872822014745636399169836243405817827154486872418438),(24,4994825049319778628264109918203528013397801482892017346259850801976079186567283167451772),(24,5355161711394695913370027724546585965217854109962689028676196529421250891364238258176598),(24,7801487213634235874192717961273868190191473136636348853528729343566346214226054130204461)],
  [(24,6025021409605815291524281488232696781432596124244078610381912705244515772412892077891161),(24,3446785529356068072725164058700633640838655754617190293480228696992838850141819616108670),(24,420899538439672513504448899885468178685913479901549702480104648470631696935634062465278),(24,3375304222217639822012331748382712274232333741811476608916224114035915820344667155162515)],
  [(24,2394158323741474925168541327670502535854757791906103262434111531442286420240976414452887),(24,5851083950342687818949295597439050249475182523870907199206987031091980516422218857567712),(24,3759316616933696168736014137150228654583410701984096128990762068824984761042111448625583),(24,3660810023314871413394488568834067869634053834714564119910845864262113382459695259114623)],
  [(24,3804923422957591557969519111580070670749301133098826503930825628181936715620841794735459),(24,106706356269701302196678766773654402603499892050003654511859137523951637185331364224002),(24,5922600198820549947367443039224594123486929324530242506546299059631517521986846330127302),(24,4919895785307079202535721521651766753070774198982406193168323922232494864680576766095703)],
  [(24,905695152792981164229707255716646371908263617028204495714969727100437115769220639912295),(24,7364421270052707393246299872002346914650328979184707228049301904094766784055676060104288),(24,6760890438766588680740590414698673027334988355709952777395397888178166222046863574941507),(24,4215590367955427964275448440552906246272266084727414699107863729682279584820814529914521)],
  [(24,4707327797202668058900135180733071235568543909883357604019422109586056889950719368672025),(24,1971363218763889152761788136952962181360156901424305518173045400259417485214722825072619),(24,1326929021989008970505042549186715172998062561895074318291646308830170610393963827693126),(24,8854600551230052452539832998048177690104184091573306362433071724060054137143906087149080)],
  [(24,6438403864019364345003983067831708907564667636339358191980422576348603040342092824696387),(24,3627226075925013522572263469974366655841142759354713421797708617902113800732769829352221),(24,5862733048589623679437425145563134854328051711693791672015942460483512458042584985131076),(24,4839590993257320711475669940540173215077682360375596920536334464823477713777887327928931)],
  [(24,6103017711605213331713836102415335905714807000580134464059433048138282768295063207738472),(24,4371094717472823510639085717827784589603644416626741149711019035228744250185208169386882),(24,7362808014835015911142168083736893446574708821166879623027946668646988743446046139866150),(24,6529012926049767489614447510058022853209214723611773724477731319906341979855481870095228)],
  [(24,2509579528019829527944904256677926530866928456499629390517410602788474873802663118277707),(24,4611040035904036396190205321396862708146580451089170839069561599504116978396503800145868),(24,2453162814874895186849094383117479621404628627764601624949645076276252464356988961851797),(24,711419238888811277902726964482051392547006057513253849463816583713048072951184159926448)],
  [(24,3844301404410976879826719760452132886448193882992478944285586476822777344427270387103248),(24,46601824179261477354860675379746453344467271080941127006450752806468209730452645649694),(24,3153150079949140334792532376594880681062996478765123844301405142654526640646631370196142),(24,5165551497365494684439522263484803508134752473451453142265398899778223557663290590919567)],
  [(24,3887528386317932022741117289308513857842433981513458932960750745326676434338962433107932),(24,4220561872263667496541004410053555243532133553783804391336804277068063579307583490571962),(24,3928301629580647490245265645117046923789108090611004532473579636955533415548387456615832),(24,2922606412856699387494641034804717939422960651587637782702445994950856024945400322175111)],
  [(24,309024491823751122590160548423322538483415793630699056243561301563915210897233493620286),(24,3222751911659790752118393171534588580507348880736662751584117958061960609099919945259914),(24,3197644124294186368376629823809417297956904839198385394381710554103802655162433190230800),(24,6194226723215266988442606757909140034626824432617443688633223478619523412159492420717689)],
  [(24,253090503777440833753297212209467697595665530670179686784812374167712021641237417461261),(24,8040830855313432037186355739772743284485836719913399312371765159686144897794761993881569),(24,2314416908102802655170641987081916592321259854484887201966112268180419448450725507928847),(24,4724464147473932035809449342010537824242240412489319900090126943805770226712719206918114)],
  [(24,6838169401367870862483950434499401028466692637608529106821408723340127833288336296125688),(24,8830943003949096542911714065651902935038277777228491324404437147729676469407262934178207),(24,277749173058883940803507110703095648270450390852038291335148145803884323562111432622789),(24,5125267105607985107093456827660460272796961543919781521880688107936974483144782559533955)],
  [(24,8423223932567190371785353462457970262378754705579166371222057238794264756711882475915473),(24,6062839733549580760424144900881234255954609731279551036463571097625393670501984218182405),(24,7787493710354103506277523179564332974628362138793679674125499181722397591947214957797055),(24,4836116431230753526066127752412307387063821036052506351017075110250384606278595878069606)],
  [(24,2942553140370242001765273801356508155286017077189135202452014858560276687391646381749159),(24,2681674251933191085934189517552313899865418301112679059808912253031597910786484515803040),(24,8292996334733167056567828680619181913012388978222929868569785617536432104183887268561269),(24,8312028927131104071910463823547575926726823106517589125122101670693506234834991430174124)],
  [(24,2215869649501002048045656929928824308932340884357728027824551326640261422860111415897203),(24,7020900250716646151255261225188504022945855873203545185547765105858050659573297295521042),(24,7571588593490715790414278726604288120722991047005427237401964072688707387188717163251677),(24,8625119746728252327182801373805663759795025763462956611522555718051288362491440853932037)],
  [(24,8081975351598774462594262839899851209116323092396686934672236519008271604292871709004777),(24,8724642959630390856629948607623051143044165027574210379820367324224449793699993682912515),(24,6004959343846132126450309055908822791389648952826018377308644364196061290412783794898760),(24,8097301093880770321141901213374755677782807725313717403229709195438567525619786855383266)],
  [(24,566708366805801381552623085393679986142751894686580052163312018063890518312224316054763),(24,4994981668046037629281275707782676595376286902532684928675649937207337487776716417293760),(24,1284549325978783194511935000191223359691752389759258844518532352858710480173721829617197),(24,7911621727759596252721632056475884725599178066524246036986388786989712922966701231993925)],
  [(24,7709196454239740751399008522816606672505892749552204068520547782317990380665308459051220),(24,4997019368991314370914831702468875627716302997497915262650642897284969167228548832713408),(24,8826956467026262783962018477485106559009290101156997918845461631651207056452629893120349),(24,1245002054356207166496077530726003801496238169328276500971167955469279662045475011218667)],
  [(24,2945807975418263992057144151962944374441921982796117003310763265177578098720906591723113),(24,6039347861807131731513296291091140084310023060341212134276568977622882707313514110826349),(24,4800750404662876754045517284989251995947918507202425121589443786678307818472555851360092),(24,8982542230857895052554228128815534406797146001242230680188145238333490564679289179561844)],
  [(24,8949222208889537294424949431335291435090697933674551415399561310749685509260903982141250),(24,769104814512896595852411583229622904033346966650686471270303799247490261624754432671605),(24,5796348369438573012278973704704441724835748383572965707924771405896909729980994225361730),(24,5068062350300994725510262154205944403349751850187085168228409717438549194515894466022813)],
  [(24,7345044922926810852453359167212522656952340710383378232404079614718224749062945846859901),(24,5339286499669596787811450432364584616475861969442404792895979465586607614318314827327919),(24,6297487891048272742984276297645628734207853269989650526762763829354375939496951181033902),(24,7167804149231045152683739056761259053438359570972512898269183163257208836192330288738204)],
  [(24,7861027056407057254459335435958720186847133870359656496733836255917689077380268234941777),(24,2836045446701369536081757263771851556928059895363082553193122024533046061837271166114803),(24,61030251778030852745935232758480650008532596882533236012862118377695669135127237157269),(24,2633029873751412122732751162555629738584856170463928056154329655113074249560255091935154)],
  [(24,1111648375473489428832764851373214312309383403875226223992666316016474681041508479949371),(24,6009790890401364065043433717294929965505808948457865927018110031729598657732199431115700),(24,2472866959753483346236864997081232144433777207603234816850693262587786894726152998694582),(24,5471582815692257706219294154512179110979494383204141836879089753795226823388637226216537)],
  [(24,629842746384086313039791542842448355707954058210954127801749696464730396718798124223799),(24,3082194502732314769925334210947256773286630011566381762024671613106819136030980534913902),(24,5604236105795954447813688274124725143671497713389465726743776740910605822187105946165055),(24,1924752162456067438097191286698719149403197969147734047528478490365160104880215344221210)],
  [(12,26117566236583158065350592291974386580818726)]
]
lemma check_4621 : checkCyclePrime 4621 4620 2 [2, 3, 5, 7, 11] cyc_4621 = true := by decide +kernel
end ExceptionCycles


lemma exists_circ_perm_of_mem_except44 {F : Type*} [Field F] [Fintype F]
    (hF : 7 < Fintype.card F) (hmem : Fintype.card F ∈ except44) :
    ∃ a : Fin (Fintype.card F - 1) ≃ Fˣ,
      ∀ i : Fin (Fintype.card F - 1),
        IsPrimitiveRoot ((a i : F) * (a ⟨(i.val + 1) % (Fintype.card F - 1), Nat.mod_lt _ (by omega)⟩ : F) - 1) (Fintype.card F - 1) := by
  simp only [except44, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq | hq_eq
  · have : Fact (Nat.Prime 3) := ⟨isPrimeBool_sound (by decide)⟩
    have : Fact (∀ r : ZMod 3, r ^ 2 ≠ (2 : ZMod 3) + 0 * r) := ⟨qnr_3⟩
    exact exists_circ_perm_quad_minus 3 2 (by omega) (by simpa using hq_eq) 4 [2] cyc_9 (by decide) (by omega) check_9
  · have : Fact (Nat.Prime 11) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 11 (by omega) hq_eq 2 [2, 5] cyc_11 (by decide) (by omega) check_11
  · have : Fact (Nat.Prime 13) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 13 (by omega) hq_eq 2 [2, 3] cyc_13 (by decide) (by omega) check_13
  · exact exists_circ_perm_cast_sub (by omega) (by decide) (exists_circ_perm_gf16 hq_eq)
  · have : Fact (Nat.Prime 19) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 19 (by omega) hq_eq 2 [2, 3] cyc_19 (by decide) (by omega) check_19
  · have : Fact (Nat.Prime 23) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 23 (by omega) hq_eq 5 [2, 11] cyc_23 (by decide) (by omega) check_23
  · have : Fact (Nat.Prime 5) := ⟨isPrimeBool_sound (by decide)⟩
    have : Fact (∀ r : ZMod 5, r ^ 2 ≠ (2 : ZMod 5) + 0 * r) := ⟨qnr_5⟩
    exact exists_circ_perm_quad_minus 5 2 (by omega) (by simpa using hq_eq) 7 [2, 3] cyc_25 (by decide) (by omega) check_25
  · exact exists_circ_perm_cast_sub (by omega) (by decide) (exists_circ_perm_gf27_minus hq_eq)
  · have : Fact (Nat.Prime 29) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 29 (by omega) hq_eq 2 [2, 7] cyc_29 (by decide) (by omega) check_29
  · have : Fact (Nat.Prime 31) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 31 (by omega) hq_eq 3 [2, 3, 5] cyc_31 (by decide) (by omega) check_31
  · have : Fact (Nat.Prime 37) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 37 (by omega) hq_eq 2 [2, 3] cyc_37 (by decide) (by omega) check_37
  · have : Fact (Nat.Prime 41) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 41 (by omega) hq_eq 6 [2, 5] cyc_41 (by decide) (by omega) check_41
  · have : Fact (Nat.Prime 43) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 43 (by omega) hq_eq 3 [2, 3, 7] cyc_43 (by decide) (by omega) check_43
  · have : Fact (Nat.Prime 7) := ⟨isPrimeBool_sound (by decide)⟩
    have : Fact (∀ r : ZMod 7, r ^ 2 ≠ (3 : ZMod 7) + 0 * r) := ⟨qnr_7⟩
    exact exists_circ_perm_quad_minus 7 3 (by omega) (by simpa using hq_eq) 8 [2, 3] cyc_49 (by decide) (by omega) check_49
  · have : Fact (Nat.Prime 61) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 61 (by omega) hq_eq 2 [2, 3, 5] cyc_61 (by decide) (by omega) check_61
  · have : Fact (Nat.Prime 67) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 67 (by omega) hq_eq 2 [2, 3, 11] cyc_67 (by decide) (by omega) check_67
  · have : Fact (Nat.Prime 71) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 71 (by omega) hq_eq 7 [2, 5, 7] cyc_71 (by decide) (by omega) check_71
  · have : Fact (Nat.Prime 79) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 79 (by omega) hq_eq 3 [2, 3, 13] cyc_79 (by decide) (by omega) check_79
  · have : Fact (Nat.Prime 103) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 103 (by omega) hq_eq 5 [2, 3, 17] cyc_103 (by decide) (by omega) check_103
  · have : Fact (Nat.Prime 11) := ⟨isPrimeBool_sound (by decide)⟩
    have : Fact (∀ r : ZMod 11, r ^ 2 ≠ (2 : ZMod 11) + 0 * r) := ⟨qnr_11⟩
    exact exists_circ_perm_quad_minus 11 2 (by omega) (by simpa using hq_eq) 13 [2, 3, 5] cyc_121 (by decide) (by omega) check_121
  · have : Fact (Nat.Prime 127) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 127 (by omega) hq_eq 3 [2, 3, 7] cyc_127 (by decide) (by omega) check_127
  · have : Fact (Nat.Prime 151) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 151 (by omega) hq_eq 6 [2, 3, 5] cyc_151 (by decide) (by omega) check_151
  · have : Fact (Nat.Prime 13) := ⟨isPrimeBool_sound (by decide)⟩
    have : Fact (∀ r : ZMod 13, r ^ 2 ≠ (2 : ZMod 13) + 0 * r) := ⟨qnr_13⟩
    exact exists_circ_perm_quad_minus 13 2 (by omega) (by simpa using hq_eq) 15 [2, 3, 7] cyc_169 (by decide) (by omega) check_169
  · have : Fact (Nat.Prime 181) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 181 (by omega) hq_eq 2 [2, 3, 5] cyc_181 (by decide) (by omega) check_181
  · have : Fact (Nat.Prime 211) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 211 (by omega) hq_eq 2 [2, 3, 5, 7] cyc_211 (by decide) (by omega) check_211
  · have : Fact (Nat.Prime 241) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 241 (by omega) hq_eq 7 [2, 3, 5] cyc_241 (by decide) (by omega) check_241
  · have : Fact (Nat.Prime 271) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 271 (by omega) hq_eq 6 [2, 3, 5] cyc_271 (by decide) (by omega) check_271
  · have : Fact (Nat.Prime 331) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 331 (by omega) hq_eq 3 [2, 3, 5, 11] cyc_331 (by decide) (by omega) check_331
  · have : Fact (Nat.Prime 19) := ⟨isPrimeBool_sound (by decide)⟩
    have : Fact (∀ r : ZMod 19, r ^ 2 ≠ (2 : ZMod 19) + 0 * r) := ⟨qnr_19⟩
    exact exists_circ_perm_quad_minus 19 2 (by omega) (by simpa using hq_eq) 21 [2, 3, 5] cyc_361 (by decide) (by omega) check_361
  · have : Fact (Nat.Prime 421) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 421 (by omega) hq_eq 2 [2, 3, 5, 7] cyc_421 (by decide) (by omega) check_421
  · have : Fact (Nat.Prime 463) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 463 (by omega) hq_eq 3 [2, 3, 7, 11] cyc_463 (by decide) (by omega) check_463
  · have : Fact (Nat.Prime 547) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 547 (by omega) hq_eq 2 [2, 3, 7, 13] cyc_547 (by decide) (by omega) check_547
  · have : Fact (Nat.Prime 571) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 571 (by omega) hq_eq 3 [2, 3, 5, 19] cyc_571 (by decide) (by omega) check_571
  · have : Fact (Nat.Prime 631) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 631 (by omega) hq_eq 3 [2, 3, 5, 7] cyc_631 (by decide) (by omega) check_631
  · have : Fact (Nat.Prime 661) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 661 (by omega) hq_eq 2 [2, 3, 5, 11] cyc_661 (by decide) (by omega) check_661
  · have : Fact (Nat.Prime 29) := ⟨isPrimeBool_sound (by decide)⟩
    have : Fact (∀ r : ZMod 29, r ^ 2 ≠ (2 : ZMod 29) + 0 * r) := ⟨qnr_29⟩
    exact exists_circ_perm_quad_minus 29 2 (by omega) (by simpa using hq_eq) 33 [2, 3, 5, 7] cyc_841 (by decide) (by omega) check_841
  · have : Fact (Nat.Prime 991) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 991 (by omega) hq_eq 6 [2, 3, 5, 11] cyc_991 (by decide) (by omega) check_991
  · have : Fact (Nat.Prime 1051) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 1051 (by omega) hq_eq 7 [2, 3, 5, 7] cyc_1051 (by decide) (by omega) check_1051
  · have : Fact (Nat.Prime 1471) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 1471 (by omega) hq_eq 6 [2, 3, 5, 7] cyc_1471 (by decide) (by omega) check_1471
  · have : Fact (Nat.Prime 41) := ⟨isPrimeBool_sound (by decide)⟩
    have : Fact (∀ r : ZMod 41, r ^ 2 ≠ (3 : ZMod 41) + 0 * r) := ⟨qnr_41⟩
    exact exists_circ_perm_quad_minus 41 3 (by omega) (by simpa using hq_eq) 45 [2, 3, 5, 7] cyc_1681 (by decide) (by omega) check_1681
  · have : Fact (Nat.Prime 2311) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 2311 (by omega) hq_eq 3 [2, 3, 5, 7, 11] cyc_2311 (by decide) (by omega) check_2311
  · have : Fact (Nat.Prime 2731) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 2731 (by omega) hq_eq 3 [2, 3, 5, 7, 13] cyc_2731 (by decide) (by omega) check_2731
  · have : Fact (Nat.Prime 3571) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 3571 (by omega) hq_eq 2 [2, 3, 5, 7, 17] cyc_3571 (by decide) (by omega) check_3571
  · have : Fact (Nat.Prime 4621) := ⟨isPrimeBool_sound (by decide)⟩
    exact exists_circ_perm_prime_minus 4621 (by omega) hq_eq 2 [2, 3, 5, 7, 11] cyc_4621 (by decide) (by omega) check_4621

end Solver3

theorem OMA.solution : type_of% @OeisA229232.conjecture_4 := by
  intro F _ _ hF
  classical
  by_cases hmem : Fintype.card F ∈ Solver3.except44
  · exact Solver3.exists_circ_perm_of_mem_except44 hF hmem
  · have hm1_ne : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have hnprim : ¬ IsPrimitiveRoot (-1 : F) (Fintype.card F - 1) := by
      intro hp
      have h2 : (-1 : F) ^ 2 = 1 := by ring
      have hdvd := hp.dvd_of_pow_eq_one 2 h2
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have hres := Solver3.exists_circ_perm_of_analytic
      (fun adj hsym hirr h3 hCE => Solver3.chvatal_erdos adj hsym hirr h3 hCE)
      hF (-1 : F) hm1_ne hnprim (fun α k a b ha1 hab hsum hka hαn hdeg hLower hUpper => by
        by_cases hbig : 8100 ≤ Fintype.card F
        · exact Solver3.analytic_ge_8100 (by omega) hbig ha1 hab hsum hka hdeg hLower
        · obtain ⟨p, _, e, hp, hcard⟩ := FiniteField.card' F
          have hchk := Solver3.checkAllBelow8100_sound 8092 8 (Fintype.card F)
            Solver3.below8100_ok (by omega) (by omega) (by omega) ⟨p, e, hp, e.pos, hcard⟩ hmem
          exact Solver3.checkAnalyticQ_sound (by omega) (by omega) ha1 hab hsum hka hαn hdeg hLower hUpper hchk)
    simpa [sub_eq_add_neg] using hres
