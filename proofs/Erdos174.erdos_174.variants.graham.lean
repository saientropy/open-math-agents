import FormalConjectures.ErdosProblems.«174»

/-!
# Disproof of Graham's Conjecture (Erdős Problem 174)

We refute `Erdos174.erdos_174.variants.graham` by constructing a 7-point cyclic heptagon
`A ⊆ EuclideanSpace ℝ (Fin 2)` on the circle of center `(r, 0)` and radius `r`, where
`r > 2` is transcendental over `ℚ`, and proving `¬ IsRamsey A` via a 31-coloring of `ℝᵈ`
built from a `ℚ`-derivation `D : ℝ → ℝ` with `D r = 1`.

1. Using countability of algebraic reals over `ℚ` and uncountability of `ℝ`, we pick
   `r > 2` with `Transcendental ℚ r`.
2. Since `ℝ` is formally smooth over `ℚ(r)` (by taking a transcendence basis of `ℝ / ℚ(r)`
   and char-0 separability), lifting `ℚ(r) → TrivSqZeroExt ℝ ℝ` (`r ↦ (r, 1)`) yields a
   derivation `D : ℝ → ℝ` with `D r = 1`.
3. With `v₀ = (0, 0)` and `v_{j,±} = (j, ±√(j(2r - j)))` for `j ∈ {1, 3, 4}` and weights
   `w = (2, -2, -2, 2, 2, -1, -1)`, any congruent copy `q : Fin 7 → ℝᵈ` is affine-isometric
   `q i = t + (v i 0) • e₀ + (v i 1) • e₁` with orthonormal `e₀, e₁`.
4. All lower-order weighted sums vanish, leaving
   `∑ i, w i * (R * ∑ m, (D (q i m)) ^ 2) = -24` where `R = (2r - 1)(2r - 3)(2r - 4)`.
5. Coloring `x ∈ ℝᵈ` by `⌊R * ∑ m, (D (x m)) ^ 2⌋ mod 31` forbids any monochromatic copy
   because `-24` lies at distance `7 > 6` from `31ℤ`.
-/

namespace Erdos174Disproof

private lemma exists_transcendental_gt_two : ∃ r : ℝ, 2 < r ∧ Transcendental ℚ r := by
  have hcount : Set.Countable {x : ℝ | IsAlgebraic ℚ x} := by
    have hsub :
        {x : ℝ | IsAlgebraic ℚ x} ⊆
          ⋃ p ∈ ({p : Polynomial ℚ | p ≠ 0} : Set (Polynomial ℚ)),
            ((p.map (algebraMap ℚ ℝ)).roots.toFinset : Set ℝ) := by
      intro x hx
      rcases hx with ⟨p, hp0, hpx⟩
      refine Set.mem_iUnion₂.mpr ⟨p, hp0, ?_⟩
      have hmap0 : p.map (algebraMap ℚ ℝ) ≠ 0 :=
        (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr hp0
      have hroot : (p.map (algebraMap ℚ ℝ)).IsRoot x := by
        rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
        exact hpx
      exact Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hmap0).mpr hroot))
    refine Set.Countable.mono hsub ?_
    have : Countable (Polynomial ℚ) :=
      Function.Injective.countable
        (f := fun p : Polynomial ℚ => List.ofFn fun i : Fin (p.natDegree + 1) => p.coeff i)
        fun p q h => by
          have hlen : p.natDegree + 1 = q.natDegree + 1 := by
            simpa [List.length_ofFn] using congrArg List.length h
          ext n
          by_cases hn : n < p.natDegree + 1
          · have hq : n < q.natDegree + 1 := by omega
            have hget := congrArg (fun l : List ℚ => l[n]?) h
            simp only [List.getElem?_ofFn, dif_pos hn, dif_pos hq, Option.some.injEq] at hget
            exact hget
          · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
              Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact (Set.to_countable _).biUnion fun p _ => (Finset.finite_toSet _).countable
  have hne : ({x : ℝ | IsAlgebraic ℚ x}ᶜ).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hemp
    have huniv : Set.Countable (Set.univ : Set ℝ) := hemp ▸ hcount
    have hcr : Countable ℝ := Set.countable_univ_iff.mp huniv
    exact not_countable hcr
  obtain ⟨x, hx⟩ := hne
  have htr : Transcendental ℚ x := hx
  let n : ℕ := Nat.ceil |x| + 3
  refine ⟨x + (n : ℝ), ?_, ?_⟩
  · have hle : |x| ≤ (Nat.ceil |x| : ℝ) := Nat.le_ceil |x|
    have hneg : -|x| ≤ x := neg_abs_le x
    dsimp only [n]
    push_cast
    linarith
  · intro halg
    rcases halg with ⟨p, hp0, hpr⟩
    let q : Polynomial ℚ := p.comp (Polynomial.X + Polynomial.C (n : ℚ))
    have hq0 : q ≠ 0 := by
      intro hqz
      have hpz : p = 0 := by
        calc
          p = p.comp Polynomial.X := p.comp_X.symm
          _ = p.comp ((Polynomial.X + Polynomial.C (n : ℚ)).comp
                (Polynomial.X - Polynomial.C (n : ℚ))) := by
                simp [Polynomial.add_comp, Polynomial.X_comp]
          _ = q.comp (Polynomial.X - Polynomial.C (n : ℚ)) := (Polynomial.comp_assoc _ _ _).symm
          _ = 0 := by rw [hqz, Polynomial.zero_comp]
      exact hp0 hpz
    have hqx : Polynomial.aeval x q = 0 := by
      dsimp only [q]
      rw [Polynomial.aeval_comp]
      simpa [map_add, Polynomial.aeval_X, Polynomial.aeval_C] using hpr
    exact htr ⟨q, hq0, hqx⟩

private def DualR : Type := TrivSqZeroExt ℝ ℝ

private local instance : CommRing DualR :=
  inferInstanceAs (CommRing (TrivSqZeroExt ℝ ℝ))

private def DualR.toTsze : DualR ≃+* TrivSqZeroExt ℝ ℝ :=
  RingEquiv.refl _

private lemma exists_derivation (r : ℝ) (hr : Transcendental ℚ r) :
    ∃ D : ℝ → ℝ,
      (∀ x y, D (x + y) = D x + D y) ∧
      (∀ x y, D (x * y) = x * D y + y * D x) ∧
      D r = 1 := by
  let v : Unit → ℝ := fun _ => r
  have hv : AlgebraicIndependent ℚ v := by
    rw [algebraicIndependent_unique_type_iff]
    exact hr
  open scoped IntermediateField.algebraAdjoinAdjoin in
  let A := Algebra.adjoin ℚ (Set.range v)
  open scoped IntermediateField.algebraAdjoinAdjoin in
  let K₀ := IntermediateField.adjoin ℚ (Set.range v)
  let φ : MvPolynomial Unit ℚ →ₐ[ℚ] TrivSqZeroExt ℝ ℝ :=
    MvPolynomial.aeval (fun _ => TrivSqZeroExt.inl r + TrivSqZeroExt.inr 1)
  let g : A →ₐ[ℚ] TrivSqZeroExt ℝ ℝ := φ.comp hv.aevalEquiv.symm.toAlgHom
  have hcomp_fst : (TrivSqZeroExt.fstHom ℚ ℝ ℝ).comp φ = MvPolynomial.aeval v := by
    ext i
    simp [φ, v]
  have hg_fst : ∀ x : A, (g x).fst = (x : ℝ) := by
    intro x
    let p := hv.aevalEquiv.symm x
    have h1 : (g x).fst = ((TrivSqZeroExt.fstHom ℚ ℝ ℝ).comp φ) p := rfl
    rw [h1, hcomp_fst]
    have h2 : (hv.aevalEquiv p : ℝ) = MvPolynomial.aeval v p := rfl
    rw [← h2]
    exact congrArg Subtype.val (hv.aevalEquiv.apply_symm_apply x)
  have hg_unit : ∀ y : nonZeroDivisors A, IsUnit (g y.1) := by
    intro y
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hg_fst]
    have hy0 : (y.1 : A) ≠ 0 := nonZeroDivisors.ne_zero y.2
    have hyR : ((y.1 : A) : ℝ) ≠ 0 := fun h => hy0 (Subtype.ext h)
    exact isUnit_iff_ne_zero.mpr hyR
  open scoped IntermediateField.algebraAdjoinAdjoin in
  let f₀ : K₀ →ₐ[ℚ] TrivSqZeroExt ℝ ℝ := IsLocalization.liftAlgHom (M := nonZeroDivisors A) hg_unit
  have hf₀_fst : ∀ x : K₀, (f₀ x).fst = (x : ℝ) := by
    open scoped IntermediateField.algebraAdjoinAdjoin in
    have heq : (TrivSqZeroExt.fstHom ℚ ℝ ℝ).comp f₀ = K₀.val := by
      apply IsLocalization.algHom_ext (nonZeroDivisors A)
      ext a
      change (f₀ (algebraMap A K₀ a)).fst = (a : ℝ)
      rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
      exact hg_fst a
    intro x
    exact AlgHom.congr_fun heq x
  have hr_memA : r ∈ A := Algebra.subset_adjoin ⟨(), rfl⟩
  have hr_memK : r ∈ K₀ := IntermediateField.subset_adjoin ℚ _ ⟨(), rfl⟩
  have hf₀_r : f₀ ⟨r, hr_memK⟩ = TrivSqZeroExt.inl r + TrivSqZeroExt.inr 1 := by
    open scoped IntermediateField.algebraAdjoinAdjoin in
    have hmap : (⟨r, hr_memK⟩ : K₀) = algebraMap A K₀ ⟨r, hr_memA⟩ := rfl
    rw [hmap, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    have hX : hv.aevalEquiv (MvPolynomial.X ()) = ⟨r, hr_memA⟩ := by
      ext
      simp [v]
    have hsymm : hv.aevalEquiv.symm ⟨r, hr_memA⟩ = MvPolynomial.X () := by
      rw [← hX, AlgEquiv.symm_apply_apply]
    change φ (hv.aevalEquiv.symm ⟨r, hr_memA⟩) = _
    rw [hsymm]
    simp [φ]
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K₀ ℝ
  have hAlg : Algebra.IsAlgebraic (IntermediateField.adjoin K₀ (Set.range ((↑) : s → ℝ))) ℝ :=
    hs.isAlgebraic_field
  have hSep : Algebra.IsSeparable (IntermediateField.adjoin K₀ (Set.range ((↑) : s → ℝ))) ℝ :=
    inferInstance
  have hSmooth : Algebra.FormallySmooth K₀ ℝ :=
    Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1
  let _ : Algebra K₀ DualR := (DualR.toTsze.symm.toRingHom.comp f₀.toRingHom).toAlgebra
  let fstK : DualR →ₐ[K₀] ℝ :=
    { toFun := fun x => (DualR.toTsze x).fst
      map_one' := by change (1 : TrivSqZeroExt ℝ ℝ).fst = 1; simp
      map_mul' := fun x y => by
        change (DualR.toTsze x * DualR.toTsze y).fst = _
        simp
      map_zero' := by change (0 : TrivSqZeroExt ℝ ℝ).fst = 0; simp
      map_add' := fun x y => by
        change (DualR.toTsze x + DualR.toTsze y).fst = _
        simp
      commutes' := fun x => by
        change (f₀ x).fst = (x : ℝ)
        exact hf₀_fst x }
  let I : Ideal DualR := RingHom.ker fstK.toRingHom
  have hI : I ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro a ha b hb
    rw [Ideal.mem_bot]
    apply DualR.toTsze.injective
    rw [map_mul, map_zero]
    ext
    · simp [show (DualR.toTsze a).fst = 0 from ha, show (DualR.toTsze b).fst = 0 from hb]
    · simp [show (DualR.toTsze a).fst = 0 from ha, show (DualR.toTsze b).fst = 0 from hb]
  have hsurj : Function.Surjective fstK := fun x =>
    ⟨DualR.toTsze.symm (TrivSqZeroExt.inl x : TrivSqZeroExt ℝ ℝ),
      by change (TrivSqZeroExt.inl x : TrivSqZeroExt ℝ ℝ).fst = x; simp⟩
  let eQ : (DualR ⧸ I) ≃ₐ[K₀] ℝ := Ideal.quotientKerAlgEquivOfSurjective hsurj
  obtain ⟨F, hF⟩ := Algebra.FormallySmooth.comp_surjective K₀ ℝ I hI eQ.symm.toAlgHom
  have hF_fst : ∀ x : ℝ, (DualR.toTsze (F x)).fst = x := by
    intro x
    have hq : Ideal.Quotient.mk I (F x) = eQ.symm x := AlgHom.congr_fun hF x
    have h2 : eQ (Ideal.Quotient.mk I (F x)) = x := by
      rw [hq, AlgEquiv.apply_symm_apply]
    exact h2
  let D : ℝ → ℝ := fun x => (DualR.toTsze (F x)).snd
  refine ⟨D, ?_, ?_, ?_⟩
  · intro x y
    dsimp only [D]
    rw [map_add, map_add]
    simp
  · intro x y
    dsimp only [D]
    rw [map_mul, map_mul, TrivSqZeroExt.snd_mul, hF_fst x, hF_fst y]
    simp only [smul_eq_mul, op_smul_eq_mul]
    ring
  · dsimp only [D]
    have hFr : F (algebraMap K₀ ℝ ⟨r, hr_memK⟩) = algebraMap K₀ DualR ⟨r, hr_memK⟩ :=
      F.commutes ⟨r, hr_memK⟩
    have hval : (algebraMap K₀ ℝ ⟨r, hr_memK⟩) = r := rfl
    rw [← hval, hFr]
    change (f₀ ⟨r, hr_memK⟩).snd = 1
    rw [hf₀_r]
    simp

private lemma deriv_helpers {D : ℝ → ℝ}
    (hadd : ∀ x y, D (x + y) = D x + D y)
    (hmul : ∀ x y, D (x * y) = x * D y + y * D x) :
    D 0 = 0 ∧ D 1 = 0 ∧ (∀ x, D (-x) = -D x) ∧
      (∀ x y, D (x - y) = D x - D y) ∧
      (∀ n : ℕ, D (n : ℝ) = 0) ∧
      (∀ x, D (x ^ 2) = 2 * x * D x) := by
  have h0 : D 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    linarith
  have h1 : D 1 = 0 := by
    have := hmul 1 1
    rw [mul_one, one_mul] at this
    linarith
  have hneg : ∀ x, D (-x) = -D x := fun x => by
    have := hadd x (-x)
    rw [add_neg_cancel, h0] at this
    linarith
  have hsub : ∀ x y, D (x - y) = D x - D y := fun x y => by
    rw [sub_eq_add_neg, hadd, hneg]
    ring
  have hnat : ∀ n : ℕ, D (n : ℝ) = 0 := fun n => by
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      push_cast
      rw [hadd, ih, h1, add_zero]
  have hsq : ∀ x, D (x ^ 2) = 2 * x * D x := fun x => by
    rw [sq, hmul]
    ring
  exact ⟨h0, h1, hneg, hsub, hnat, hsq⟩

end Erdos174Disproof

theorem OMA.disproof : ¬ (type_of% @Erdos174.erdos_174.variants.graham) := by
  intro hgraham
  obtain ⟨r, hr2, hrtr⟩ := Erdos174Disproof.exists_transcendental_gt_two
  obtain ⟨D, hD_add, hD_mul, hD_r⟩ := Erdos174Disproof.exists_derivation r hrtr
  obtain ⟨hD0, hD1, hDneg, hDsub, hDnat, hDsq⟩ := Erdos174Disproof.deriv_helpers hD_add hD_mul
  have hr_pos : 0 < r := by linarith
  have h2r1 : 0 < 2 * r - 1 := by linarith
  have h2r3 : 0 < 2 * r - 3 := by linarith
  have h2r4 : 0 < 2 * r - 4 := by linarith
  let y1 : ℝ := √(2 * r - 1)
  let y3 : ℝ := √(3 * (2 * r - 3))
  let y4 : ℝ := √(4 * (2 * r - 4))
  have hy1_pos : 0 < y1 := Real.sqrt_pos.mpr h2r1
  have hy3_pos : 0 < y3 := Real.sqrt_pos.mpr (by linarith)
  have hy4_pos : 0 < y4 := Real.sqrt_pos.mpr (by linarith)
  have hy1_sq : y1 ^ 2 = 2 * r - 1 := Real.sq_sqrt h2r1.le
  have hy3_sq : y3 ^ 2 = 3 * (2 * r - 3) := Real.sq_sqrt (by linarith)
  have hy4_sq : y4 ^ 2 = 4 * (2 * r - 4) := Real.sq_sqrt (by linarith)
  have hD2 : D 2 = 0 := by simpa using hDnat 2
  have hD6 : D 6 = 0 := by simpa using hDnat 6
  have hD8 : D 8 = 0 := by simpa using hDnat 8
  have hD9 : D 9 = 0 := by simpa using hDnat 9
  have hD16 : D 16 = 0 := by simpa using hDnat 16
  have hDy1 : y1 * D y1 = 1 := by
    have h := congrArg D hy1_sq
    rw [hDsq, hDsub, hD_mul, hD2, hD1, hD_r] at h
    linarith
  have hDy3 : y3 * D y3 = 3 := by
    have h : y3 ^ 2 = 6 * r - 9 := by linarith [hy3_sq]
    have h' := congrArg D h
    rw [hDsq, hDsub, hD_mul, hD6, hD9, hD_r] at h'
    linarith
  have hDy4 : y4 * D y4 = 4 := by
    have h : y4 ^ 2 = 8 * r - 16 := by linarith [hy4_sq]
    have h' := congrArg D h
    rw [hDsq, hDsub, hD_mul, hD8, hD16, hD_r] at h'
    linarith
  have hDy1_sq : (D y1) ^ 2 = 1 / (2 * r - 1) := by
    have : (y1 * D y1) ^ 2 = 1 := by rw [hDy1]; norm_num
    rw [mul_pow, hy1_sq] at this
    exact (eq_div_iff h2r1.ne').mpr (by linarith)
  have hDy3_sq : (D y3) ^ 2 = 3 / (2 * r - 3) := by
    have : (y3 * D y3) ^ 2 = 9 := by rw [hDy3]; norm_num
    rw [mul_pow, hy3_sq] at this
    exact (eq_div_iff h2r3.ne').mpr (by linarith)
  have hDy4_sq : (D y4) ^ 2 = 4 / (2 * r - 4) := by
    have : (y4 * D y4) ^ 2 = 16 := by rw [hDy4]; norm_num
    rw [mul_pow, hy4_sq] at this
    exact (eq_div_iff h2r4.ne').mpr (by linarith)
  let v : Fin 7 → EuclideanSpace ℝ (Fin 2) :=
    ![!₂[0, 0], !₂[1, y1], !₂[1, -y1], !₂[3, y3], !₂[3, -y3], !₂[4, y4], !₂[4, -y4]]
  let A : Set (EuclideanSpace ℝ (Fin 2)) := Set.range v
  have hA_fin : A.Finite := Set.finite_range v
  have hA_cosph : EuclideanGeometry.Cospherical A := by
    refine ⟨!₂[r, 0], r, ?_⟩
    rintro _ ⟨i, rfl⟩
    rw [EuclideanSpace.dist_eq, Real.sqrt_eq_iff_eq_sq (by positivity) hr_pos.le]
    rw [Fin.sum_univ_two]
    fin_cases i <;>
      simp [v, Real.dist_eq, sq_abs] <;>
      linarith [hy1_sq, hy3_sq, hy4_sq]
  have hRamsey : Erdos174.IsRamsey A := hgraham A hA_fin hA_cosph
  obtain ⟨d, hd⟩ := hRamsey.2 31 (by norm_num)
  let R : ℝ := (2 * r - 1) * (2 * r - 3) * (2 * r - 4)
  let Φ : EuclideanSpace ℝ (Fin d) → ℝ := fun x => R * ∑ m : Fin d, (D (x m)) ^ 2
  let col : EuclideanSpace ℝ (Fin d) → Fin 31 := fun x =>
    ⟨(⌊Φ x⌋ % 31).toNat, by
      have h1 : 0 ≤ ⌊Φ x⌋ % 31 := Int.emod_nonneg _ (by norm_num)
      have h2 : ⌊Φ x⌋ % 31 < 31 := Int.emod_lt_of_pos _ (by norm_num)
      omega⟩
  obtain ⟨p, hcong, c₀, hmono⟩ := hd col
  let q : Fin 7 → EuclideanSpace ℝ (Fin d) := fun i => p ⟨v i, ⟨i, rfl⟩⟩
  have hdist : ∀ i j : Fin 7, dist (q i) (q j) = dist (v i) (v j) := fun i j =>
    (hcong.dist_eq ⟨v i, ⟨i, rfl⟩⟩ ⟨v j, ⟨j, rfl⟩⟩).symm
  let t : EuclideanSpace ℝ (Fin d) := q 0
  let u : Fin 7 → EuclideanSpace ℝ (Fin d) := fun i => q i - t
  have hu0 : u 0 = 0 := sub_self _
  have hv0 : v 0 = 0 := by ext k; fin_cases k <;> simp [v]
  have hu_norm : ∀ i : Fin 7, ‖u i‖ = ‖v i‖ := fun i => by
    have := hdist i 0
    simpa [u, t, dist_eq_norm, hv0] using this
  have hu_inner : ∀ i j : Fin 7, inner ℝ (u i) (u j) = inner ℝ (v i) (v j) := by
    intro i j
    rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
      real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
    have hsub : ‖u i - u j‖ = ‖v i - v j‖ := by
      have : u i - u j = q i - q j := by dsimp only [u]; abel
      rw [this, ← dist_eq_norm, ← dist_eq_norm]
      exact hdist i j
    rw [hu_norm i, hu_norm j, hsub]
  let e0 : EuclideanSpace ℝ (Fin d) := (1 / 2 : ℝ) • (u 1 + u 2)
  let e1 : EuclideanSpace ℝ (Fin d) := (1 / (2 * y1)) • (u 1 - u 2)
  have hv_inner : ∀ i j : Fin 7, inner ℝ (v i) (v j) = v i 0 * v j 0 + v i 1 * v j 1 := by
    intro i j
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct, Fin.sum_univ_two, mul_comm]
  have hv10 : v 1 0 = 1 := rfl
  have hv11 : v 1 1 = y1 := rfl
  have hv20 : v 2 0 = 1 := rfl
  have hv21 : v 2 1 = -y1 := rfl
  have he0_norm : inner ℝ e0 e0 = 1 := by
    simp only [e0, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
      conj_trivial, hu_inner, hv_inner, hv10, hv11, hv20, hv21]
    ring
  have he1_norm : inner ℝ e1 e1 = 1 := by
    simp only [e1, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
      conj_trivial, hu_inner, hv_inner, hv10, hv11, hv20, hv21]
    field_simp [hy1_pos.ne']
    ring
  have he01 : inner ℝ e0 e1 = 0 := by
    simp only [e0, e1, inner_smul_left, inner_smul_right, inner_add_left, inner_sub_right,
      conj_trivial, hu_inner, hv_inner, hv10, hv11, hv20, hv21]
    ring
  have hui_e0 : ∀ i : Fin 7, inner ℝ (u i) e0 = v i 0 := by
    intro i
    simp only [e0, inner_smul_right, inner_add_right, hu_inner, hv_inner, hv10, hv11, hv20, hv21]
    ring
  have hui_e1 : ∀ i : Fin 7, inner ℝ (u i) e1 = v i 1 := by
    intro i
    simp only [e1, inner_smul_right, inner_sub_right, hu_inner, hv_inner, hv10, hv11, hv20, hv21]
    field_simp [hy1_pos.ne']
    ring
  have hq_decomp : ∀ i : Fin 7, q i = t + (v i 0) • e0 + (v i 1) • e1 := by
    intro i
    have hzero : ‖u i - ((v i 0) • e0 + (v i 1) • e1)‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, conj_trivial]
      simp only [real_inner_comm (u i) e0, real_inner_comm (u i) e1, real_inner_comm e0 e1,
        hui_e0, hui_e1, he0_norm, he1_norm, he01, hu_inner, hv_inner]
      ring
    have hnorm0 : ‖u i - ((v i 0) • e0 + (v i 1) • e1)‖ = 0 := sq_eq_zero_iff.mp hzero
    have heq : u i = (v i 0) • e0 + (v i 1) • e1 := sub_eq_zero.mp (norm_eq_zero.mp hnorm0)
    have hq_eq : q i = t + u i := by dsimp only [u]; abel
    rw [hq_eq, heq, add_assoc]
  have he1_sum : ∑ m : Fin d, (e1 m) ^ 2 = 1 := by
    have h := he1_norm
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simpa [dotProduct, sq] using h
  let w : Fin 7 → ℤ := ![2, -2, -2, 2, 2, -1, -1]
  have hD_coord : ∀ (m : Fin d) (i : Fin 7),
      D (q i m) =
        D (t m) + (v i 0) * D (e0 m) + (v i 1) * D (e1 m) + D (v i 1) * (e1 m) := by
    intro m i
    have hqm : q i m = t m + v i 0 * e0 m + v i 1 * e1 m := by
      have := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x m) (hq_decomp i)
      simpa using this
    have hDv0 : D (v i 0) = 0 := by
      fin_cases i
      · simpa [v] using hD0
      · simpa [v] using hD1
      · simpa [v] using hD1
      · simpa [v] using hDnat 3
      · simpa [v] using hDnat 3
      · simpa [v] using hDnat 4
      · simpa [v] using hDnat 4
    rw [hqm, hD_add, hD_add, hD_mul, hD_mul, hDv0]
    ring
  have hcoord_sum : ∀ m : Fin d,
      ∑ i : Fin 7, (w i : ℝ) * (D (q i m)) ^ 2 =
        (e1 m) ^ 2 * (-4 * (D y1) ^ 2 + 4 * (D y3) ^ 2 - 2 * (D y4) ^ 2) := by
    intro m
    simp_rw [hD_coord m]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      w, v, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ, PiLp.toLp_apply, hD0, hDneg]
    push_cast
    linear_combination
      (-4 * (D (e1 m)) ^ 2) * hy1_sq +
      (4 * (D (e1 m)) ^ 2) * hy3_sq +
      (-2 * (D (e1 m)) ^ 2) * hy4_sq +
      (-8 * D (e1 m) * e1 m) * hDy1 +
      (8 * D (e1 m) * e1 m) * hDy3 +
      (-4 * D (e1 m) * e1 m) * hDy4
  have hPhi_sum : ∑ i : Fin 7, (w i : ℝ) * Φ (q i) = -24 := by
    have hswap :
        ∑ i : Fin 7, (w i : ℝ) * Φ (q i) =
          R * ∑ m : Fin d, ∑ i : Fin 7, (w i : ℝ) * (D (q i m)) ^ 2 := by
      simp only [Φ]
      simp_rw [mul_left_comm (w _ : ℝ) R, ← Finset.mul_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hswap]
    simp_rw [hcoord_sum, ← Finset.sum_mul, he1_sum, one_mul]
    rw [hDy1_sq, hDy3_sq, hDy4_sq]
    dsimp only [R]
    field_simp [h2r1.ne', h2r3.ne', h2r4.ne']
    ring
  have hmod_eq : ∀ i : Fin 7, ⌊Φ (q i)⌋ % 31 = (c₀.1 : ℤ) := by
    intro i
    have hc : col (q i) = c₀ := hmono ⟨v i, ⟨i, rfl⟩⟩
    have hv : (col (q i)).1 = c₀.1 := congrArg Fin.val hc
    have hnn : 0 ≤ ⌊Φ (q i)⌋ % 31 := Int.emod_nonneg _ (by norm_num)
    have hcast : (((⌊Φ (q i)⌋ % 31).toNat : ℕ) : ℤ) = (c₀.1 : ℤ) := by
      exact_mod_cast hv
    rwa [Int.toNat_of_nonneg hnn] at hcast
  let k : Fin 7 → ℤ := fun i => ⌊Φ (q i)⌋ / 31
  let f : Fin 7 → ℝ := fun i => Φ (q i) - (⌊Φ (q i)⌋ : ℝ)
  have hf_bounds : ∀ i : Fin 7, 0 ≤ f i ∧ f i < 1 := fun i =>
    ⟨sub_nonneg.mpr (Int.floor_le _), by dsimp only [f]; linarith [Int.lt_floor_add_one (Φ (q i))]⟩
  have hPhi_split : ∀ i : Fin 7, Φ (q i) = 31 * (k i : ℝ) + (c₀.1 : ℝ) + f i := by
    intro i
    have hdiv : 31 * k i + (c₀.1 : ℤ) = ⌊Φ (q i)⌋ := by
      have hm := hmod_eq i
      dsimp only [k]
      omega
    have hdivR : 31 * (k i : ℝ) + (c₀.1 : ℝ) = (⌊Φ (q i)⌋ : ℝ) := by exact_mod_cast hdiv
    dsimp only [f]
    linarith
  let K : ℤ := ∑ i : Fin 7, w i * k i
  have hsum_split :
      ∑ i : Fin 7, (w i : ℝ) * Φ (q i) = 31 * (K : ℝ) + ∑ i : Fin 7, (w i : ℝ) * f i := by
    simp_rw [hPhi_split]
    have hw_zero : ∑ i : Fin 7, (w i : ℝ) = 0 := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, w, Matrix.cons_val_zero,
        Matrix.cons_val_succ]
      norm_num
    have hK_cast : (K : ℝ) = ∑ i : Fin 7, (w i : ℝ) * (k i : ℝ) := by
      dsimp only [K]
      push_cast
      rfl
    calc
      ∑ i : Fin 7, (w i : ℝ) * (31 * (k i : ℝ) + (c₀.1 : ℝ) + f i)
          = ∑ i : Fin 7, (31 * ((w i : ℝ) * (k i : ℝ)) + (w i : ℝ) * (c₀.1 : ℝ) +
              (w i : ℝ) * f i) := by
                refine Finset.sum_congr rfl fun i _ => ?_; ring
      _ = 31 * (∑ i : Fin 7, (w i : ℝ) * (k i : ℝ)) + (∑ i : Fin 7, (w i : ℝ)) * (c₀.1 : ℝ) +
            ∑ i : Fin 7, (w i : ℝ) * f i := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
                ← Finset.sum_mul]
      _ = 31 * (K : ℝ) + ∑ i : Fin 7, (w i : ℝ) * f i := by
            rw [hw_zero, zero_mul, add_zero, hK_cast]
  have hf_sum_bounds : -6 < ∑ i : Fin 7, (w i : ℝ) * f i ∧ ∑ i : Fin 7, (w i : ℝ) * f i < 6 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, w, Matrix.cons_val_zero,
      Matrix.cons_val_succ]
    push_cast
    have h0 := hf_bounds 0
    have h1 := hf_bounds 1
    have h2 := hf_bounds 2
    have h3 := hf_bounds 3
    have h4 := hf_bounds 4
    have h5 := hf_bounds 5
    have h6 := hf_bounds 6
    constructor <;> linarith
  have hK_low : (-30 : ℝ) < 31 * (K : ℝ) := by linarith
  have hK_high : 31 * (K : ℝ) < (-18 : ℝ) := by linarith
  have hK_lowZ : (-30 : ℤ) < 31 * K := by exact_mod_cast hK_low
  have hK_highZ : 31 * K < (-18 : ℤ) := by exact_mod_cast hK_high
  omega
