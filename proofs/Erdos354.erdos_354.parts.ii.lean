import FormalConjectures.ErdosProblems.«354»

/-!
# Proof of Erdős Problem 354(ii)

We prove `Erdos354.erdos_354.parts.ii` with witness `γ = √φ ∈ (1, 2)`, where
`φ = Real.goldenRatio = (1 + √5) / 2`. Even the even-indexed subsequence
`u n = ⌊γ ^ n * α⌋` of `FloorMultiples.interleave α β γ` is additively complete for every `α > 0`:
1. The even terms `c n = u (2 * n) = ⌊φ ^ n * α⌋` satisfy `c (n + 2) = c (n + 1) + c n + 1`
   for infinitely many `n` (otherwise the fractional parts satisfy the Fibonacci recurrence,
   forcing them to vanish eventually and contradicting `Irrational φ`).
2. Selecting `M` disjoint carry-one triples on even indices produces a finite set `E` of even
   indices whose subset sums cover a contiguous interval `[S, S + M]`.
3. The odd terms `d k = u (2 * k + 1) = ⌊φ ^ k * (γ * α)⌋` eventually satisfy `1 ≤ d k` and
   `d (k + 1) ≤ 2 * d k` since `1 < φ < 2`, so Brown's greedy induction extends `[S, S + d K₀]`
   to all integers `x ≥ S`.
-/

namespace Erdos354Proof

open Real
open scoped goldenRatio

private lemma floor_golden_cases (α : ℝ) (n : ℕ) :
    ⌊φ ^ (n + 2) * α⌋ = ⌊φ ^ (n + 1) * α⌋ + ⌊φ ^ n * α⌋ ∨
      ⌊φ ^ (n + 2) * α⌋ = ⌊φ ^ (n + 1) * α⌋ + ⌊φ ^ n * α⌋ + 1 := by
  have hrec : φ ^ (n + 2) * α = φ ^ (n + 1) * α + φ ^ n * α := by
    have h := Real.goldenRatio_pow_sub_goldenRatio_pow n
    linarith [mul_sub (φ ^ (n + 2)) (φ ^ (n + 1)) α, congrArg (· * α) h]
  have h0_le : (⌊φ ^ n * α⌋ : ℝ) ≤ φ ^ n * α := Int.floor_le _
  have h0_lt : φ ^ n * α < (⌊φ ^ n * α⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have h1_le : (⌊φ ^ (n + 1) * α⌋ : ℝ) ≤ φ ^ (n + 1) * α := Int.floor_le _
  have h1_lt : φ ^ (n + 1) * α < (⌊φ ^ (n + 1) * α⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have h2_le : (⌊φ ^ (n + 2) * α⌋ : ℝ) ≤ φ ^ (n + 2) * α := Int.floor_le _
  have h2_lt : φ ^ (n + 2) * α < (⌊φ ^ (n + 2) * α⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hlow : ((⌊φ ^ (n + 1) * α⌋ + ⌊φ ^ n * α⌋ : ℤ) : ℝ) - 1 < (⌊φ ^ (n + 2) * α⌋ : ℝ) := by
    push_cast; linarith
  have hhigh : (⌊φ ^ (n + 2) * α⌋ : ℝ) < ((⌊φ ^ (n + 1) * α⌋ + ⌊φ ^ n * α⌋ : ℤ) : ℝ) + 2 := by
    push_cast; linarith
  have hlowZ : ⌊φ ^ (n + 1) * α⌋ + ⌊φ ^ n * α⌋ - 1 < ⌊φ ^ (n + 2) * α⌋ := by
    exact_mod_cast hlow
  have hhighZ : ⌊φ ^ (n + 2) * α⌋ < ⌊φ ^ (n + 1) * α⌋ + ⌊φ ^ n * α⌋ + 2 := by
    exact_mod_cast hhigh
  omega

private lemma carry_one_frequently {α : ℝ} (hα : 0 < α) (N : ℕ) :
    ∃ n ≥ N, ⌊φ ^ (n + 2) * α⌋ = ⌊φ ^ (n + 1) * α⌋ + ⌊φ ^ n * α⌋ + 1 := by
  by_contra hno
  push Not at hno
  have hadd : ∀ n ≥ N, ⌊φ ^ (n + 2) * α⌋ = ⌊φ ^ (n + 1) * α⌋ + ⌊φ ^ n * α⌋ := by
    intro n hn
    rcases floor_golden_cases α n with h | h
    · exact h
    · exact False.elim (hno n hn h)
  let f : ℕ → ℝ := fun n => φ ^ n * α - (⌊φ ^ n * α⌋ : ℝ)
  have hf_nonneg : ∀ n, 0 ≤ f n := fun n => sub_nonneg.mpr (Int.floor_le _)
  have hf_lt_one : ∀ n, f n < 1 := fun n => by
    dsimp only [f]
    linarith [Int.lt_floor_add_one (φ ^ n * α)]
  have hf_rec : ∀ n ≥ N, f (n + 2) = f (n + 1) + f n := by
    intro n hn
    have hpow : φ ^ (n + 2) * α = φ ^ (n + 1) * α + φ ^ n * α := by
      have h := Real.goldenRatio_pow_sub_goldenRatio_pow n
      have h' : (φ ^ (n + 2) - φ ^ (n + 1)) * α = φ ^ n * α := congrArg (· * α) h
      linarith
    have hc : (⌊φ ^ (n + 2) * α⌋ : ℝ) = (⌊φ ^ (n + 1) * α⌋ : ℝ) + (⌊φ ^ n * α⌋ : ℝ) := by
      exact_mod_cast hadd n hn
    dsimp only [f]
    linarith
  have hf2_zero : f (N + 2) = 0 := by
    by_contra hne
    have hpos : 0 < f (N + 2) := lt_of_le_of_ne (hf_nonneg _) (Ne.symm hne)
    set ε : ℝ := f (N + 2)
    have hge_all : ∀ k : ℕ, ε ≤ f (N + 2 + k) ∧ ε ≤ f (N + 3 + k) := by
      intro k
      induction k with
      | zero =>
        refine ⟨le_rfl, ?_⟩
        have h3 := hf_rec (N + 1) (by omega)
        have : N + 1 + 2 = N + 3 := by omega
        have : N + 1 + 1 = N + 2 := by omega
        linarith [hf_nonneg (N + 1)]
      | succ k ih =>
        refine ⟨by simpa [show N + 2 + (k + 1) = N + 3 + k by omega] using ih.2, ?_⟩
        have hstep := hf_rec (N + 2 + k) (by omega)
        have h1 : N + 2 + k + 2 = N + 3 + (k + 1) := by omega
        have h2 : N + 2 + k + 1 = N + 3 + k := by omega
        rw [h1, h2] at hstep
        linarith [ih.1, ih.2]
    have hgrow : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) * ε ≤ f (N + 2 + 2 * k) := by
      intro k
      induction k with
      | zero => simp [ε]
      | succ k ih =>
        have hstep := hf_rec (N + 2 + 2 * k) (by omega)
        have h1 : N + 2 + 2 * k + 2 = N + 2 + 2 * (k + 1) := by omega
        have h2 : N + 2 + 2 * k + 1 = N + 3 + 2 * k := by omega
        rw [h1, h2] at hstep
        have hmid : ε ≤ f (N + 3 + 2 * k) := (hge_all (2 * k)).2
        push_cast at ih ⊢
        linarith
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
    have h1 : 1 < ((k + 1 : ℕ) : ℝ) * ε := by
      have hk' : 1 < (k : ℝ) * ε := (div_lt_iff₀ hpos).mp hk
      push_cast
      linarith
    have h2 := hgrow k
    have h3 := hf_lt_one (N + 2 + 2 * k)
    linarith
  have hf0_zero : f N = 0 := by
    have h := hf_rec N le_rfl
    linarith [hf_nonneg N, hf_nonneg (N + 1)]
  have hf1_zero : f (N + 1) = 0 := by
    have h := hf_rec N le_rfl
    linarith [hf_nonneg N, hf_nonneg (N + 1)]
  have hN_eq : φ ^ N * α = (⌊φ ^ N * α⌋ : ℝ) := sub_eq_zero.mp hf0_zero
  have hN1_eq : φ ^ (N + 1) * α = (⌊φ ^ (N + 1) * α⌋ : ℝ) := sub_eq_zero.mp hf1_zero
  have hN_pos : 0 < φ ^ N * α := mul_pos (pow_pos Real.goldenRatio_pos N) hα
  have hfloor_ne : (⌊φ ^ N * α⌋ : ℝ) ≠ 0 := by linarith
  have hphi_rat : (((⌊φ ^ (N + 1) * α⌋ : ℚ) / (⌊φ ^ N * α⌋ : ℚ) : ℚ) : ℝ) = φ := by
    push_cast
    rw [div_eq_iff hfloor_ne, ← hN_eq, ← hN1_eq, pow_succ]
    ring
  exact Real.goldenRatio_irrational ⟨(⌊φ ^ (N + 1) * α⌋ : ℚ) / (⌊φ ^ N * α⌋ : ℚ), hphi_rat⟩

private lemma even_block {α : ℝ} (hα : 0 < α) :
    ∀ M : ℕ, ∃ (S : ℤ) (E : Finset ℕ),
      (∀ i ∈ E, Even i) ∧
      ∀ r : ℕ, r ≤ M → ∃ B ⊆ E, ∑ i ∈ B, ⌊(√φ) ^ i * α⌋ = S + r := by
  have hsq : √φ ^ 2 = φ := Real.sq_sqrt Real.goldenRatio_pos.le
  have hu_even : ∀ m : ℕ, ⌊(√φ) ^ (2 * m) * α⌋ = ⌊φ ^ m * α⌋ := by
    intro m
    rw [pow_mul, hsq]
  intro M
  induction M with
  | zero =>
    refine ⟨0, ∅, by simp, fun r hr => ⟨∅, Finset.empty_subset _, ?_⟩⟩
    have : r = 0 := by omega
    subst this
    simp
  | succ M ih =>
    obtain ⟨S, E, hEven, hRep⟩ := ih
    let K : ℕ := E.sup id + 1
    obtain ⟨n, hnK, hcarry⟩ := carry_one_frequently hα K
    have hnot_mem : ∀ m : ℕ, m ≥ K → 2 * m ∉ E := by
      intro m hm hmem
      have hle : 2 * m ≤ E.sup id := Finset.le_sup (f := id) hmem
      omega
    have h0_not : 2 * n ∉ E := hnot_mem n hnK
    have h1_not : 2 * (n + 1) ∉ E := hnot_mem (n + 1) (by omega)
    have h2_not : 2 * (n + 2) ∉ E := hnot_mem (n + 2) (by omega)
    let S' : ℤ := S + ⌊φ ^ n * α⌋ + ⌊φ ^ (n + 1) * α⌋
    let E' : Finset ℕ := E ∪ {2 * n, 2 * (n + 1), 2 * (n + 2)}
    refine ⟨S', E', ?_, ?_⟩
    · intro i hi
      simp only [E', Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with hE | rfl | rfl | rfl
      · exact hEven i hE
      · exact ⟨n, by omega⟩
      · exact ⟨n + 1, by omega⟩
      · exact ⟨n + 2, by omega⟩
    · intro r hr
      by_cases hrM : r ≤ M
      · obtain ⟨B, hBE, hBsum⟩ := hRep r hrM
        have hB0 : 2 * n ∉ B := fun h => h0_not (hBE h)
        have hB1 : 2 * (n + 1) ∉ B := fun h => h1_not (hBE h)
        refine ⟨insert (2 * n) (insert (2 * (n + 1)) B), ?_, ?_⟩
        · intro i hi
          simp only [Finset.mem_insert] at hi
          simp only [E', Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          rcases hi with rfl | rfl | hB
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inl (hBE hB)
        · have hne : 2 * n ≠ 2 * (n + 1) := by omega
          rw [Finset.sum_insert (by simp [hne, hB0]), Finset.sum_insert hB1,
            hu_even, hu_even, hBsum]
          dsimp only [S']
          omega
      · have hr_eq : r = M + 1 := by omega
        subst hr_eq
        obtain ⟨B, hBE, hBsum⟩ := hRep M le_rfl
        have hB2 : 2 * (n + 2) ∉ B := fun h => h2_not (hBE h)
        refine ⟨insert (2 * (n + 2)) B, ?_, ?_⟩
        · intro i hi
          simp only [Finset.mem_insert] at hi
          simp only [E', Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          rcases hi with rfl | hB
          · exact Or.inr (Or.inr (Or.inr rfl))
          · exact Or.inl (hBE hB)
        · rw [Finset.sum_insert hB2, hu_even, hBsum, hcarry]
          dsimp only [S']
          push_cast
          omega

private lemma odd_growth {α : ℝ} (hα : 0 < α) :
    ∃ K₀ : ℕ, ∀ k ≥ K₀,
      1 ≤ ⌊(√φ) ^ (2 * k + 1) * α⌋ ∧
        ⌊(√φ) ^ (2 * (k + 1) + 1) * α⌋ ≤ 2 * ⌊(√φ) ^ (2 * k + 1) * α⌋ := by
  have hsq : √φ ^ 2 = φ := Real.sq_sqrt Real.goldenRatio_pos.le
  have hγ_pos : 0 < √φ := Real.sqrt_pos.mpr Real.goldenRatio_pos
  have hβ_pos : 0 < √φ * α := mul_pos hγ_pos hα
  have h2sub_pos : 0 < 2 - φ := sub_pos.mpr Real.goldenRatio_lt_two
  have h2sub_lt : 2 - φ < 1 := by linarith [Real.one_lt_goldenRatio]
  have htend := tendsto_pow_atTop_atTop_of_one_lt Real.one_lt_goldenRatio
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.mp
    ((Filter.tendsto_atTop.mp htend) (2 / ((2 - φ) * (√φ * α))))
  refine ⟨K₀, fun k hk => ?_⟩
  have hpow : 2 / ((2 - φ) * (√φ * α)) ≤ φ ^ k := hK₀ k hk
  have hmul : 2 ≤ (2 - φ) * (φ ^ k * (√φ * α)) := by
    have h1 := (div_le_iff₀ (mul_pos h2sub_pos hβ_pos)).mp hpow
    linarith
  have hodd : ∀ m : ℕ, (√φ) ^ (2 * m + 1) * α = φ ^ m * (√φ * α) := by
    intro m
    rw [pow_succ, pow_mul, hsq]
    ring
  rw [hodd k, hodd (k + 1)]
  have hpos_term : 0 < φ ^ k * (√φ * α) := mul_pos (pow_pos Real.goldenRatio_pos k) hβ_pos
  have hge1 : 1 ≤ φ ^ k * (√φ * α) := by nlinarith
  constructor
  · exact Int.le_floor.mpr (by exact_mod_cast hge1)
  · have hlt_next : φ ^ (k + 1) * (√φ * α) < 2 * (⌊φ ^ k * (√φ * α)⌋ : ℝ) := by
      have hfl : φ ^ k * (√φ * α) < (⌊φ ^ k * (√φ * α)⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      rw [pow_succ]
      nlinarith
    have hfl_le : (⌊φ ^ (k + 1) * (√φ * α)⌋ : ℝ) ≤ φ ^ (k + 1) * (√φ * α) := Int.floor_le _
    have hlt_real : (⌊φ ^ (k + 1) * (√φ * α)⌋ : ℝ) < ((2 * ⌊φ ^ k * (√φ * α)⌋ : ℤ) : ℝ) := by
      push_cast
      linarith
    have hltZ : ⌊φ ^ (k + 1) * (√φ * α)⌋ < 2 * ⌊φ ^ k * (√φ * α)⌋ := by
      exact_mod_cast hlt_real
    omega

end Erdos354Proof

theorem OMA.solution : type_of% @Erdos354.erdos_354.parts.ii := by
  refine ⟨√Real.goldenRatio, ?_, ?_⟩
  · constructor
    · rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt zero_le_one Real.one_lt_goldenRatio
    · rw [show (2 : ℝ) = √4 by norm_num]
      exact Real.sqrt_lt_sqrt Real.goldenRatio_pos.le (by linarith [Real.goldenRatio_lt_two])
  · intro α hα β _ _
    let γ : ℝ := √Real.goldenRatio
    let u : ℕ → ℤ := fun n => ⌊γ ^ n * α⌋
    let d : ℕ → ℤ := fun k => u (2 * k + 1)
    obtain ⟨K₀, hK₀⟩ := Erdos354Proof.odd_growth hα
    have hdK₀_pos : 1 ≤ d K₀ := (hK₀ K₀ le_rfl).1
    let M : ℕ := (d K₀).toNat
    have hM_eq : (M : ℤ) = d K₀ := Int.toNat_of_nonneg (by omega)
    obtain ⟨S, E, hEven, hRep⟩ := Erdos354Proof.even_block hα M
    let T : ℕ → ℤ := fun m => d K₀ + ∑ j ∈ Finset.range m, d (K₀ + j)
    have hInd : ∀ m : ℕ,
        d (K₀ + m) ≤ T m ∧
          ∀ x : ℤ, S ≤ x → x ≤ S + T m →
            ∃ B ⊆ E ∪ (Finset.range m).image (fun j => 2 * (K₀ + j) + 1),
              ∑ i ∈ B, u i = x := by
      intro m
      induction m with
      | zero =>
        refine ⟨by simp [T], fun x hx1 hx2 => ?_⟩
        simp only [T, Finset.range_zero, Finset.sum_empty, add_zero] at hx2
        let r : ℕ := (x - S).toNat
        have hr_le : r ≤ M := by omega
        obtain ⟨B, hBE, hBsum⟩ := hRep r hr_le
        refine ⟨B, hBE.trans (by simp), ?_⟩
        rw [hBsum]
        omega
      | succ m ih =>
        obtain ⟨ih_le, ih_rep⟩ := ih
        have hT_succ : T (m + 1) = T m + d (K₀ + m) := by
          simp only [T, Finset.sum_range_succ]
          omega
        have hstep_le : d (K₀ + (m + 1)) ≤ T (m + 1) := by
          have h2 : d (K₀ + m + 1) ≤ 2 * d (K₀ + m) := (hK₀ (K₀ + m) (by omega)).2
          have : K₀ + (m + 1) = K₀ + m + 1 := by omega
          rw [this]
          omega
        refine ⟨hstep_le, fun x hx1 hx2 => ?_⟩
        by_cases hxm : x ≤ S + T m
        · obtain ⟨B, hBsub, hBsum⟩ := ih_rep x hx1 hxm
          refine ⟨B, hBsub.trans ?_, hBsum⟩
          apply Finset.union_subset_union_right
          exact Finset.image_subset_image (Finset.range_mono (Nat.le_succ m))
        · have hx_sub_ge : S ≤ x - d (K₀ + m) := by omega
          have hx_sub_le : x - d (K₀ + m) ≤ S + T m := by omega
          obtain ⟨B, hBsub, hBsum⟩ := ih_rep (x - d (K₀ + m)) hx_sub_ge hx_sub_le
          let idx : ℕ := 2 * (K₀ + m) + 1
          have hidx_not : idx ∉ B := by
            intro hmem
            have hmem' := hBsub hmem
            simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range] at hmem'
            rcases hmem' with hE | ⟨j, hj, hjeq⟩
            · obtain ⟨t, ht⟩ := hEven idx hE
              dsimp only [idx] at ht
              omega
            · dsimp only [idx] at hjeq
              omega
          refine ⟨insert idx B, ?_, ?_⟩
          · intro i hi
            simp only [Finset.mem_insert] at hi
            rcases hi with rfl | hiB
            · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨m, ?_, rfl⟩)
              exact Finset.mem_range.mpr (Nat.lt_succ_self m)
            · have hi' := hBsub hiB
              simp only [Finset.mem_union] at hi' ⊢
              rcases hi' with hE | hI
              · exact Or.inl hE
              · exact Or.inr (Finset.image_subset_image (Finset.range_mono (Nat.le_succ m)) hI)
          · rw [Finset.sum_insert hidx_not, hBsum]
            dsimp only [idx, d]
            omega
    have hT_ge : ∀ m : ℕ, (m : ℤ) ≤ T m := by
      intro m
      induction m with
      | zero => simp [T]; omega
      | succ m ih =>
        have hT_succ : T (m + 1) = T m + d (K₀ + m) := by
          simp only [T, Finset.sum_range_succ]
          omega
        have hpos : 1 ≤ d (K₀ + m) := (hK₀ (K₀ + m) (by omega)).1
        rw [hT_succ]
        push_cast
        omega
    rw [IsAddCompleteNatSeq', Filter.eventually_atTop]
    refine ⟨S, fun x hx => ?_⟩
    let m : ℕ := (x - S).toNat
    have hx_le : x ≤ S + T m := by
      have hm_eq : (m : ℤ) = x - S := Int.toNat_of_nonneg (by omega)
      have := hT_ge m
      omega
    obtain ⟨B, _, hBsum⟩ := (hInd m).2 x hx hx_le
    refine ⟨B.image (2 * ·), ?_⟩
    have hinj : Function.Injective (fun i : ℕ => 2 * i) := fun a b hab => by
      dsimp only at hab
      omega
    rw [Finset.sum_image (fun a _ b _ hab => hinj hab)]
    have hcongr : ∀ i ∈ B, Erdos354.FloorMultiples.interleave α β γ (2 * i) = u i := by
      intro i _
      simp [Erdos354.FloorMultiples.interleave, Erdos354.FloorMultiples, u]
    rw [Finset.sum_congr rfl hcongr, hBsum]
