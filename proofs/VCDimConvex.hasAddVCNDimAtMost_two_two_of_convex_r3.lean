import FormalConjectures.Other.VCDimConvex

/-!
# Proof of `VCDimConvex.hasAddVCNDimAtMost_two_two_of_convex_r3`

Every convex set `C ⊆ ℝ³` has additive `VC₂`-dimension at most `2` (i.e. cannot `2`-shatter any
`3 × 3` Minkowski grid `U + V`).

The proof is completely elementary (no Hahn-Banach, no topology, no Ramsey theory):
1. Translate `u 0 = v 0 = 0`; shattering forces `u 1, u 2` and `v 1, v 2` to be linearly
   independent, so `P_U = span{u 1, u 2}` and `P_V = span{v 1, v 2}` are `2`-dimensional.
2. A barycentric-cone convex combination argument shows `v 1 ∉ P_U`, so `P_U ≠ P_V`, hence
   `dim(P_U ∩ P_V) = 1`.
3. Passing to a basis `{e₁ ∈ P_U, e₂ ∈ P_V, z ∈ P_U ∩ P_V}`, sorting along `e₁, e₂`, and
   applying a shear-and-scale linear equivalence puts the grid into the normal form
   `U = {(0,0,0), (λ,0,1), (1,0,0)}`, `V = {(0,0,0), (0,μ,r), (0,1,0)}` with `λ, μ ∈ [0, 1]`, `r ≠ 0`.
4. Convex position eliminates `r < 0` and all boundary values `λ, μ ∈ {0, 1}`, leaving
   `0 < λ, μ < 1` and `r > 0`.
5. Finally, the two `7`-element subsets `S₁ = G \ {(1,0), (1,2)}` and `S₂ = G \ {(0,1), (2,1)}`
   yield opposite strict vertical-bracketing inequalities for the relative translation `y(S₂) - y(S₁)`
   across all three cases of its horizontal displacement.
-/

open scoped EuclideanGeometry Pointwise

namespace VCDimConvexTwoTwoProof

/-- Convenience predicate for `2`-shattering a `3 × 3` grid in `Fin 3 → ℝ`. -/
private def Shatters3x3 (C : Set (Fin 3 → ℝ)) (u v : Fin 3 → Fin 3 → ℝ) : Prop :=
  ∃ y : Set (Fin 2 → Fin 3) → (Fin 3 → ℝ),
    ∀ (i : Fin 2 → Fin 3) (s : Set (Fin 2 → Fin 3)),
      y s + (u (i 0) + v (i 1)) ∈ C ↔ i ∈ s

private def mkPair (a b : Fin 3) : Fin 2 → Fin 3 := ![a, b]

private lemma mkPair_0 (a b : Fin 3) : mkPair a b 0 = a := rfl
private lemma mkPair_1 (a b : Fin 3) : mkPair a b 1 = b := rfl

private lemma mkPair_eq_iff (a b c d : Fin 3) :
    mkPair a b = mkPair c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨by simpa [mkPair] using congrFun h 0, by simpa [mkPair] using congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩; rfl

private lemma fin3_ext {α : Type*} {p q : Fin 3 → α}
    (h0 : p 0 = q 0) (h1 : p 1 = q 1) (h2 : p 2 = q 2) : p = q := by
  ext k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2

@[local simp] private lemma v3_0 {α : Type*} (a b c : α) : (![a, b, c] : Fin 3 → α) 0 = a := rfl
@[local simp] private lemma v3_1 {α : Type*} (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[local simp] private lemma v3_2 {α : Type*} (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl

private lemma shatters3x3_linearEquiv {C : Set (Fin 3 → ℝ)} {u v : Fin 3 → Fin 3 → ℝ}
    (h : Shatters3x3 C u v) (e : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) :
    Shatters3x3 (e '' C) (fun a => e (u a)) (fun b => e (v b)) := by
  obtain ⟨y, hy⟩ := h
  refine ⟨fun s => e (y s), fun i s => ?_⟩
  have heq : e (y s) + (e (u (i 0)) + e (v (i 1))) = e (y s + (u (i 0) + v (i 1))) := by
    simp [map_add]
  rw [heq, e.injective.mem_set_image]
  exact hy i s

private lemma shatters3x3_translate {C : Set (Fin 3 → ℝ)} {u v : Fin 3 → Fin 3 → ℝ}
    (h : Shatters3x3 C u v) (du dv : Fin 3 → ℝ) :
    Shatters3x3 C (fun a => u a - du) (fun b => v b - dv) := by
  obtain ⟨y, hy⟩ := h
  refine ⟨fun s => y s + (du + dv), fun i s => ?_⟩
  have heq : y s + (du + dv) + (u (i 0) - du + (v (i 1) - dv)) = y s + (u (i 0) + v (i 1)) := by
    abel
  rw [heq]
  exact hy i s

private lemma shatters3x3_perm {C : Set (Fin 3 → ℝ)} {u v : Fin 3 → Fin 3 → ℝ}
    (h : Shatters3x3 C u v) (σ τ : Equiv.Perm (Fin 3)) :
    Shatters3x3 C (u ∘ σ) (v ∘ τ) := by
  obtain ⟨y, hy⟩ := h
  let φ : (Fin 2 → Fin 3) ≃ (Fin 2 → Fin 3) :=
    { toFun := fun i => ![σ (i 0), τ (i 1)]
      invFun := fun i => ![σ.symm (i 0), τ.symm (i 1)]
      left_inv := fun i => by ext k; fin_cases k <;> simp
      right_inv := fun i => by ext k; fin_cases k <;> simp }
  refine ⟨fun s => y (φ '' s), fun i s => ?_⟩
  have h0 : φ i 0 = σ (i 0) := rfl
  have h1 : φ i 1 = τ (i 1) := rfl
  have := hy (φ i) (φ '' s)
  rw [h0, h1, φ.injective.mem_set_image] at this
  exact this

private lemma shatters3x3_swap {C : Set (Fin 3 → ℝ)} {u v : Fin 3 → Fin 3 → ℝ}
    (h : Shatters3x3 C u v) :
    Shatters3x3 C v u := by
  obtain ⟨y, hy⟩ := h
  let φ : (Fin 2 → Fin 3) ≃ (Fin 2 → Fin 3) :=
    { toFun := fun i => ![i 1, i 0]
      invFun := fun i => ![i 1, i 0]
      left_inv := fun i => by ext k; fin_cases k <;> simp
      right_inv := fun i => by ext k; fin_cases k <;> simp }
  refine ⟨fun s => y (φ '' s), fun i s => ?_⟩
  have := hy (φ i) (φ '' s)
  have h0 : φ i 0 = i 1 := rfl
  have h1 : φ i 1 = i 0 := rfl
  rw [h0, h1, add_comm (u (i 1)) (v (i 0)), φ.injective.mem_set_image] at this
  exact this

private lemma conv3_mem {C : Set (Fin 3 → ℝ)} (hC : Convex ℝ C) {p1 p2 p3 : Fin 3 → ℝ}
    (h1 : p1 ∈ C) (h2 : p2 ∈ C) (h3 : p3 ∈ C)
    (w1 w2 w3 : ℝ) (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (hw3 : 0 ≤ w3) (hsum : w1 + w2 + w3 = 1) :
    w1 • p1 + w2 • p2 + w3 • p3 ∈ C := by
  by_cases h12 : w1 + w2 = 0
  · have hw10 : w1 = 0 := by linarith
    have hw20 : w2 = 0 := by linarith
    have hw31 : w3 = 1 := by linarith
    simpa [hw10, hw20, hw31] using h3
  · have h12p : 0 < w1 + w2 := lt_of_le_of_ne (by linarith) (Ne.symm h12)
    have m12 : (w1 / (w1 + w2)) • p1 + (w2 / (w1 + w2)) • p2 ∈ C :=
      hC h1 h2 (div_nonneg hw1 h12p.le) (div_nonneg hw2 h12p.le) (by field_simp)
    have hfin := hC m12 h3 h12p.le hw3 (by linarith)
    convert hfin using 1
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp

private lemma not_mem_conv3 {C : Set (Fin 3 → ℝ)} (hC : Convex ℝ C) {u v : Fin 3 → Fin 3 → ℝ}
    (h : Shatters3x3 C u v)
    (p0 p1 p2 p3 : Fin 2 → Fin 3) (h1 : p1 ≠ p0) (h2 : p2 ≠ p0) (h3 : p3 ≠ p0)
    (w1 w2 w3 : ℝ) (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (hw3 : 0 ≤ w3) (hsum : w1 + w2 + w3 = 1)
    (heq : w1 • (u (p1 0) + v (p1 1)) + w2 • (u (p2 0) + v (p2 1)) + w3 • (u (p3 0) + v (p3 1)) =
      u (p0 0) + v (p0 1)) : False := by
  obtain ⟨y, hy⟩ := h
  let s : Set (Fin 2 → Fin 3) := {p1, p2, p3}
  have hp0 : p0 ∉ s := by
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1.symm, h2.symm, h3.symm⟩
  have hm1 : y s + (u (p1 0) + v (p1 1)) ∈ C := (hy p1 s).2 (by simp [s])
  have hm2 : y s + (u (p2 0) + v (p2 1)) ∈ C := (hy p2 s).2 (by simp [s])
  have hm3 : y s + (u (p3 0) + v (p3 1)) ∈ C := (hy p3 s).2 (by simp [s])
  have hcomb : y s + (u (p0 0) + v (p0 1)) ∈ C := by
    have htot : w1 • (y s + (u (p1 0) + v (p1 1))) + w2 • (y s + (u (p2 0) + v (p2 1))) +
        w3 • (y s + (u (p3 0) + v (p3 1))) = y s + (u (p0 0) + v (p0 1)) := by
      calc w1 • (y s + (u (p1 0) + v (p1 1))) + w2 • (y s + (u (p2 0) + v (p2 1))) +
            w3 • (y s + (u (p3 0) + v (p3 1)))
          = (w1 + w2 + w3) • y s +
              (w1 • (u (p1 0) + v (p1 1)) + w2 • (u (p2 0) + v (p2 1)) + w3 • (u (p3 0) + v (p3 1))) := by
            simp [smul_add, add_smul]; abel
        _ = y s + (u (p0 0) + v (p0 1)) := by rw [hsum, one_smul, heq]
    rw [← htot]
    exact conv3_mem hC hm1 hm2 hm3 w1 w2 w3 hw1 hw2 hw3 hsum
  exact hp0 ((hy p0 s).1 hcomb)

private lemma not_mem_conv4 {C : Set (Fin 3 → ℝ)} (hC : Convex ℝ C) {u v : Fin 3 → Fin 3 → ℝ}
    (h : Shatters3x3 C u v)
    (p0 p1 p2 p3 p4 : Fin 2 → Fin 3)
    (h1 : p1 ≠ p0) (h2 : p2 ≠ p0) (h3 : p3 ≠ p0) (h4 : p4 ≠ p0)
    (w1 w2 w3 w4 : ℝ) (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (hw3 : 0 ≤ w3) (hw4 : 0 ≤ w4)
    (hsum : w1 + w2 + w3 + w4 = 1)
    (heq : w1 • (u (p1 0) + v (p1 1)) + w2 • (u (p2 0) + v (p2 1)) +
        w3 • (u (p3 0) + v (p3 1)) + w4 • (u (p4 0) + v (p4 1)) =
      u (p0 0) + v (p0 1)) : False := by
  obtain ⟨y, hy⟩ := h
  let s : Set (Fin 2 → Fin 3) := {p1, p2, p3, p4}
  have hp0 : p0 ∉ s := by
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1.symm, h2.symm, h3.symm, h4.symm⟩
  have hm1 : y s + (u (p1 0) + v (p1 1)) ∈ C := (hy p1 s).2 (by simp [s])
  have hm2 : y s + (u (p2 0) + v (p2 1)) ∈ C := (hy p2 s).2 (by simp [s])
  have hm3 : y s + (u (p3 0) + v (p3 1)) ∈ C := (hy p3 s).2 (by simp [s])
  have hm4 : y s + (u (p4 0) + v (p4 1)) ∈ C := (hy p4 s).2 (by simp [s])
  have hcomb : y s + (u (p0 0) + v (p0 1)) ∈ C := by
    have htot : w1 • (y s + (u (p1 0) + v (p1 1))) + w2 • (y s + (u (p2 0) + v (p2 1))) +
        w3 • (y s + (u (p3 0) + v (p3 1))) + w4 • (y s + (u (p4 0) + v (p4 1))) =
        y s + (u (p0 0) + v (p0 1)) := by
      calc _ = (w1 + w2 + w3 + w4) • y s +
              (w1 • (u (p1 0) + v (p1 1)) + w2 • (u (p2 0) + v (p2 1)) +
               w3 • (u (p3 0) + v (p3 1)) + w4 • (u (p4 0) + v (p4 1))) := by
            simp [smul_add, add_smul]; abel
        _ = y s + (u (p0 0) + v (p0 1)) := by rw [hsum, one_smul, heq]
    rw [← htot]
    by_cases h12 : w1 + w2 = 0
    · have hw10 : w1 = 0 := by linarith
      have hw20 : w2 = 0 := by linarith
      have h34 : w3 + w4 = 1 := by linarith
      have := hC hm3 hm4 hw3 hw4 h34
      simpa [hw10, hw20] using this
    · by_cases h34 : w3 + w4 = 0
      · have hw30 : w3 = 0 := by linarith
        have hw40 : w4 = 0 := by linarith
        have h12' : w1 + w2 = 1 := by linarith
        have := hC hm1 hm2 hw1 hw2 h12'
        simpa [hw30, hw40] using this
      · have h12p : 0 < w1 + w2 := lt_of_le_of_ne (by linarith) (Ne.symm h12)
        have h34p : 0 < w3 + w4 := lt_of_le_of_ne (by linarith) (Ne.symm h34)
        have m12 : (w1 / (w1 + w2)) • (y s + (u (p1 0) + v (p1 1))) +
            (w2 / (w1 + w2)) • (y s + (u (p2 0) + v (p2 1))) ∈ C :=
          hC hm1 hm2 (div_nonneg hw1 h12p.le) (div_nonneg hw2 h12p.le) (by field_simp)
        have m34 : (w3 / (w3 + w4)) • (y s + (u (p3 0) + v (p3 1))) +
            (w4 / (w3 + w4)) • (y s + (u (p4 0) + v (p4 1))) ∈ C :=
          hC hm3 hm4 (div_nonneg hw3 h34p.le) (div_nonneg hw4 h34p.le) (by field_simp)
        have hfin := hC m12 m34 h12p.le h34p.le (by linarith)
        convert hfin using 1
        ext k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
        ring
  exact hp0 ((hy p0 s).1 hcomb)

private lemma vertical_bracket {C : Set (Fin 3 → ℝ)} (hC : Convex ℝ C)
    {x y z_lo z_mid z_hi : ℝ}
    (hlo : ![x, y, z_lo] ∈ C) (hhi : ![x, y, z_hi] ∈ C) (hmid : ![x, y, z_mid] ∉ C)
    (hlt : z_lo < z_mid) : z_hi < z_mid := by
  by_contra hge
  push Not at hge
  have hden : 0 < z_hi - z_lo := by linarith
  let t : ℝ := (z_mid - z_lo) / (z_hi - z_lo)
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hden.le
  have ht1 : 0 ≤ 1 - t := by
    have : t ≤ 1 := (div_le_one hden).2 (by linarith)
    linarith
  have hmem := hC hlo hhi ht1 ht0 (by ring)
  apply hmid
  convert hmem using 1
  apply fin3_ext
  · simp; ring
  · simp; ring
  · simp only [v3_2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, t]
    field_simp
    ring

private lemma core_obstruction_nonneg {C : Set (Fin 3 → ℝ)} (hC : Convex ℝ C)
    {lam mu rho a b c : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hmu0 : 0 < mu) (hmu1 : mu < 1) (hrho : 0 < rho)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA02 : ![0, 1, 0] ∈ C) (hA22 : ![1, 1, 0] ∈ C)
    (hA01 : ![0, mu, rho] ∈ C) (hA11 : ![lam, mu, 1 + rho] ∈ C)
    (hB00 : ![a, b, c] ∈ C) (hB02 : ![a, b + 1, c] ∈ C)
    (hB11 : ![a + lam, b + mu, c + 1 + rho] ∈ C) (hB12 : ![a + lam, b + 1, c + 1] ∈ C)
    (hPtop : ![lam, 1, 1] ∉ C) (hQleft : ![a, b + mu, c + rho] ∉ C) : False := by
  have hY1 : ![a, b + mu, c] ∈ C := by
    have := hC hB00 hB02 (by linarith : 0 ≤ 1 - mu) hmu0.le (by ring)
    convert this using 1
    apply fin3_ext <;> simp <;> ring
  have hY2 : ![lam, 1, 0] ∈ C := by
    have := hC hA02 hA22 (by linarith : 0 ≤ 1 - lam) hlam0.le (by ring)
    convert this using 1
    apply fin3_ext <;> (simp; try ring)
  by_cases hb1 : b ≤ 1 - mu
  · let t : ℝ := b / (1 - mu)
    have h1mu : 0 < 1 - mu := by linarith
    have ht0 : 0 ≤ t := div_nonneg hb h1mu.le
    have ht1 : t ≤ 1 := (div_le_one h1mu).2 hb1
    have hal : 0 < a + lam := by linarith
    have hX1 : ![a, b + mu, (lam * (1 - t) * rho + a * (c + 1 + rho)) / (a + lam)] ∈ C := by
      have hm := conv3_mem hC hA01 hA02 hB11
        (lam * (1 - t) / (a + lam)) (lam * t / (a + lam)) (a / (a + lam))
        (div_nonneg (mul_nonneg hlam0.le (by linarith)) hal.le)
        (div_nonneg (mul_nonneg hlam0.le ht0) hal.le)
        (div_nonneg ha hal.le)
        (by field_simp; ring)
      convert hm using 1
      apply fin3_ext <;> simp [t] <;> field_simp <;> ring
    have hX2 : ![lam, 1, (lam * (c + 1 + t * rho)) / (a + lam)] ∈ C := by
      have hm := conv3_mem hC hA02 hB11 hB12
        (a / (a + lam)) (lam * t / (a + lam)) (lam * (1 - t) / (a + lam))
        (div_nonneg ha hal.le)
        (div_nonneg (mul_nonneg hlam0.le ht0) hal.le)
        (div_nonneg (mul_nonneg hlam0.le (by linarith)) hal.le)
        (by field_simp; ring)
      convert hm using 1
      apply fin3_ext <;> simp [t] <;> field_simp <;> ring
    have hlt1 := vertical_bracket hC hY1 hX1 hQleft (by linarith)
    have hlt2 := vertical_bracket hC hY2 hX2 hPtop (by linarith)
    rw [div_lt_iff₀ hal] at hlt1 hlt2
    linarith
  · push Not at hb1
    by_cases ha1 : a ≤ lam
    · let s : ℝ := a / lam
      have hs0 : 0 ≤ s := div_nonneg ha hlam0.le
      have hs1 : s ≤ 1 := (div_le_one hlam0).2 ha1
      have hbm : 0 < b + 1 - mu := by linarith
      have h1mu : 0 < 1 - mu := by linarith
      have hX1' : ![a, b + mu, ((1 - mu) * (rho + s) + b * c) / (b + 1 - mu)] ∈ C := by
        have hm := conv3_mem hC hA01 hA11 hB02
          ((1 - mu) * (1 - s) / (b + 1 - mu)) ((1 - mu) * s / (b + 1 - mu)) (b / (b + 1 - mu))
          (div_nonneg (mul_nonneg h1mu.le (by linarith)) hbm.le)
          (div_nonneg (mul_nonneg h1mu.le hs0) hbm.le)
          (div_nonneg hb hbm.le)
          (by field_simp; ring)
        convert hm using 1
        apply fin3_ext <;> simp [s] <;> field_simp <;> ring
      have hX2' : ![lam, 1, (b * (1 + rho) + (1 - mu) * (c + 1 - s)) / (b + 1 - mu)] ∈ C := by
        have hm := conv3_mem hC hA11 hB12 hB02
          (b / (b + 1 - mu)) ((1 - mu) * (1 - s) / (b + 1 - mu)) ((1 - mu) * s / (b + 1 - mu))
          (div_nonneg hb hbm.le)
          (div_nonneg (mul_nonneg h1mu.le (by linarith)) hbm.le)
          (div_nonneg (mul_nonneg h1mu.le hs0) hbm.le)
          (by field_simp; ring)
        convert hm using 1
        apply fin3_ext <;> simp [s] <;> field_simp <;> ring
      have hlt1 := vertical_bracket hC hY1 hX1' hQleft (by linarith)
      have hlt2 := vertical_bracket hC hY2 hX2' hPtop (by linarith)
      rw [div_lt_iff₀ hbm] at hlt1 hlt2
      linarith
    · push Not at ha1
      have h1mu : 0 < 1 - mu := by linarith
      let dx : ℝ := a - lam
      let dy : ℝ := b - (1 - mu)
      have hdx : 0 < dx := by linarith
      have hdy : 0 < dy := by linarith
      let W : ℝ := 2 + dx / lam + dy / (1 - mu)
      have hW : 0 < W := by
        have h1 : 0 < dx / lam := div_pos hdx hlam0
        have h2 : 0 < dy / (1 - mu) := div_pos hdy h1mu
        linarith
      have hX3 : ![lam, 1, ((dy / (1 - mu)) * (1 + rho) + (c + 1 + rho)) / W] ∈ C := by
        have hm := conv3_mem hC hA02 hA11 hB11
          ((1 + dx / lam) / W) ((dy / (1 - mu)) / W) (1 / W)
          (div_nonneg (by have := div_nonneg hdx.le hlam0.le; linarith) hW.le)
          (div_nonneg (div_nonneg hdy.le h1mu.le) hW.le)
          (div_nonneg zero_le_one hW.le)
          (by simp only [W]; field_simp; ring)
        convert hm using 1
        apply fin3_ext <;> simp [W, dx, dy] <;> field_simp <;> ring
      have hX4 : ![a, b + mu, ((dx / lam) * (c + 1 + rho) + (1 + dy / (1 - mu)) * c + (1 + rho)) / W] ∈ C := by
        have hm := conv3_mem hC hB11 hB02 hA11
          ((dx / lam) / W) ((1 + dy / (1 - mu)) / W) (1 / W)
          (div_nonneg (div_nonneg hdx.le hlam0.le) hW.le)
          (div_nonneg (by have := div_nonneg hdy.le h1mu.le; linarith) hW.le)
          (div_nonneg zero_le_one hW.le)
          (by simp only [W]; field_simp; ring)
        convert hm using 1
        apply fin3_ext <;> simp [W, dx, dy] <;> field_simp <;> ring
      have hlt3 := vertical_bracket hC hY2 hX3 hPtop (by linarith)
      have hlt4 := vertical_bracket hC hY1 hX4 hQleft (by linarith)
      rw [div_lt_iff₀ hW] at hlt3 hlt4
      have hW_eq : W = 2 + dx / lam + dy / (1 - mu) := rfl
      rw [hW_eq] at hlt3 hlt4
      linarith

private lemma core_obstruction {C : Set (Fin 3 → ℝ)} (hC : Convex ℝ C)
    {lam mu rho : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hmu0 : 0 < mu) (hmu1 : mu < 1) (hrho : 0 < rho) :
    ¬ Shatters3x3 C
        (![![0, 0, 0], ![lam, 0, 1], ![1, 0, 0]])
        (![![0, 0, 0], ![0, mu, rho], ![0, 1, 0]]) := by
  intro hsh
  obtain ⟨y, hy⟩ := hsh
  let S1 : Set (Fin 2 → Fin 3) := {i | i ≠ mkPair 1 0 ∧ i ≠ mkPair 1 2}
  let S2 : Set (Fin 2 → Fin 3) := {i | i ≠ mkPair 0 1 ∧ i ≠ mkPair 2 1}
  let diff := y S2 - y S1
  have run_with : ∀ (fx fy : Bool),
      0 ≤ (if fx then (1 : ℝ) else -1) * diff 0 →
      0 ≤ (if fy then (1 : ℝ) else -1) * diff 1 → False := by
    intro fx fy hdx hdy
    let sx : ℝ := if fx then 1 else -1
    let sy : ℝ := if fy then 1 else -1
    let ox : ℝ := if fx then 0 else 1
    let oy : ℝ := if fy then 0 else 1
    let lam' : ℝ := if fx then lam else 1 - lam
    let mu' : ℝ := if fy then mu else 1 - mu
    have hlam'0 : 0 < lam' := by cases fx <;> dsimp [lam'] <;> linarith
    have hlam'1 : lam' < 1 := by cases fx <;> dsimp [lam'] <;> linarith
    have hmu'0 : 0 < mu' := by cases fy <;> dsimp [mu'] <;> linarith
    have hmu'1 : mu' < 1 := by cases fy <;> dsimp [mu'] <;> linarith
    let f : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun p =>
      ![sx * (p 0 - y S1 0) + ox, sy * (p 1 - y S1 1) + oy, p 2 - y S1 2]
    have hf_inj : Function.Injective f := by
      intro p q hpq
      have h0 := congrFun hpq 0
      have h1 := congrFun hpq 1
      have h2 := congrFun hpq 2
      simp only [f, v3_0, v3_1, v3_2] at h0 h1 h2
      apply fin3_ext
      · cases fx <;> dsimp [sx] at h0 <;> linarith
      · cases fy <;> dsimp [sy] at h1 <;> linarith
      · linarith
    have hC' : Convex ℝ (f '' C) := by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ t1 t2 ht1 ht2 h12
      refine ⟨t1 • p + t2 • q, hC hp hq ht1 ht2 h12, ?_⟩
      have ht1_eq : t1 = 1 - t2 := by linarith
      apply fin3_ext <;> simp [f, ht1_eq] <;> ring
    have hmem : ∀ (i : Fin 2 → Fin 3) (s : Set (Fin 2 → Fin 3)),
        f (y s + ((![![0, 0, 0], ![lam, 0, 1], ![1, 0, 0]] : Fin 3 → Fin 3 → ℝ) (i 0) +
                  (![![0, 0, 0], ![0, mu, rho], ![0, 1, 0]] : Fin 3 → Fin 3 → ℝ) (i 1))) ∈ f '' C ↔ i ∈ s := by
      intro i s
      rw [hf_inj.mem_set_image]
      exact hy i s
    let a : ℝ := sx * diff 0
    let b : ℝ := sy * diff 1
    let c : ℝ := diff 2
    let px : Fin 3 → Fin 3 := fun k => if fx then k else ![2, 1, 0] k
    let py : Fin 3 → Fin 3 := fun k => if fy then k else ![2, 1, 0] k
    have hA02 : ![0, 1, 0] ∈ f '' C := by
      have h := (hmem (mkPair (px 0) (py 2)) S1).2 (by
        cases fx <;> cases fy <;> simp [S1, px, py, mkPair_eq_iff])
      convert h using 1
      cases fx <;> cases fy <;>
        (apply fin3_ext <;>
          simp only [f, sx, sy, ox, oy, px, py, mkPair_0, mkPair_1, Pi.add_apply, v3_0, v3_1, v3_2,
            ↓reduceIte, Bool.false_eq_true] <;> ring)
    have hA22 : ![1, 1, 0] ∈ f '' C := by
      have h := (hmem (mkPair (px 2) (py 2)) S1).2 (by
        cases fx <;> cases fy <;> simp [S1, px, py, mkPair_eq_iff])
      convert h using 1
      cases fx <;> cases fy <;>
        (apply fin3_ext <;>
          simp only [f, sx, sy, ox, oy, px, py, mkPair_0, mkPair_1, Pi.add_apply, v3_0, v3_1, v3_2,
            ↓reduceIte, Bool.false_eq_true] <;> ring)
    have hA01 : ![0, mu', rho] ∈ f '' C := by
      have h := (hmem (mkPair (px 0) (py 1)) S1).2 (by
        cases fx <;> cases fy <;> simp [S1, px, py, mkPair_eq_iff])
      convert h using 1
      cases fx <;> cases fy <;>
        (apply fin3_ext <;>
          simp only [f, sx, sy, ox, oy, mu', px, py, mkPair_0, mkPair_1, Pi.add_apply, v3_0, v3_1, v3_2,
            ↓reduceIte, Bool.false_eq_true] <;> ring)
    have hA11 : ![lam', mu', 1 + rho] ∈ f '' C := by
      have h := (hmem (mkPair (px 1) (py 1)) S1).2 (by
        cases fx <;> cases fy <;> simp [S1, px, py, mkPair_eq_iff])
      convert h using 1
      cases fx <;> cases fy <;>
        (apply fin3_ext <;>
          simp only [f, sx, sy, ox, oy, lam', mu', px, py, mkPair_0, mkPair_1, Pi.add_apply, v3_0, v3_1, v3_2,
            ↓reduceIte, Bool.false_eq_true] <;> ring)
    have hB00 : ![a, b, c] ∈ f '' C := by
      have h := (hmem (mkPair (px 0) (py 0)) S2).2 (by
        cases fx <;> cases fy <;> simp [S2, px, py, mkPair_eq_iff])
      convert h using 1
      cases fx <;> cases fy <;>
        (apply fin3_ext <;>
          simp only [f, a, b, c, diff, sx, sy, ox, oy, px, py, mkPair_0, mkPair_1, Pi.add_apply, Pi.sub_apply,
            v3_0, v3_1, v3_2, ↓reduceIte, Bool.false_eq_true] <;> ring)
    have hB02 : ![a, b + 1, c] ∈ f '' C := by
      have h := (hmem (mkPair (px 0) (py 2)) S2).2 (by
        cases fx <;> cases fy <;> simp [S2, px, py, mkPair_eq_iff])
      convert h using 1
      cases fx <;> cases fy <;>
        (apply fin3_ext <;>
          simp only [f, a, b, c, diff, sx, sy, ox, oy, px, py, mkPair_0, mkPair_1, Pi.add_apply, Pi.sub_apply,
            v3_0, v3_1, v3_2, ↓reduceIte, Bool.false_eq_true] <;> ring)
    have hB11 : ![a + lam', b + mu', c + 1 + rho] ∈ f '' C := by
      have h := (hmem (mkPair (px 1) (py 1)) S2).2 (by
        cases fx <;> cases fy <;> simp [S2, px, py, mkPair_eq_iff])
      convert h using 1
      cases fx <;> cases fy <;>
        (apply fin3_ext <;>
          simp only [f, a, b, c, diff, sx, sy, ox, oy, lam', mu', px, py, mkPair_0, mkPair_1, Pi.add_apply,
            Pi.sub_apply, v3_0, v3_1, v3_2, ↓reduceIte, Bool.false_eq_true] <;> ring)
    have hB12 : ![a + lam', b + 1, c + 1] ∈ f '' C := by
      have h := (hmem (mkPair (px 1) (py 2)) S2).2 (by
        cases fx <;> cases fy <;> simp [S2, px, py, mkPair_eq_iff])
      convert h using 1
      cases fx <;> cases fy <;>
        (apply fin3_ext <;>
          simp only [f, a, b, c, diff, sx, sy, ox, oy, lam', px, py, mkPair_0, mkPair_1, Pi.add_apply,
            Pi.sub_apply, v3_0, v3_1, v3_2, ↓reduceIte, Bool.false_eq_true] <;> ring)
    have hPtop : ![lam', 1, 1] ∉ f '' C := by
      have h : mkPair (px 1) (py 2) ∉ S1 := by
        cases fx <;> cases fy <;> simp [S1, px, py, mkPair_eq_iff]
      intro hm
      apply h
      apply (hmem (mkPair (px 1) (py 2)) S1).1
      convert hm using 1
      cases fx <;> cases fy <;>
        (apply fin3_ext <;>
          simp only [f, sx, sy, ox, oy, lam', px, py, mkPair_0, mkPair_1, Pi.add_apply, v3_0, v3_1, v3_2,
            ↓reduceIte, Bool.false_eq_true] <;> ring)
    have hQleft : ![a, b + mu', c + rho] ∉ f '' C := by
      have h : mkPair (px 0) (py 1) ∉ S2 := by
        cases fx <;> cases fy <;> simp [S2, px, py, mkPair_eq_iff]
      intro hm
      apply h
      apply (hmem (mkPair (px 0) (py 1)) S2).1
      convert hm using 1
      cases fx <;> cases fy <;>
        (apply fin3_ext <;>
          simp only [f, a, b, c, diff, sx, sy, ox, oy, mu', px, py, mkPair_0, mkPair_1, Pi.add_apply,
            Pi.sub_apply, v3_0, v3_1, v3_2, ↓reduceIte, Bool.false_eq_true] <;> ring)
    exact core_obstruction_nonneg hC' hlam'0 hlam'1 hmu'0 hmu'1 hrho hdx hdy
      hA02 hA22 hA01 hA11 hB00 hB02 hB11 hB12 hPtop hQleft
  by_cases hx : 0 ≤ diff 0 <;> by_cases hy0 : 0 ≤ diff 1
  · exact run_with true true (by simp; linarith) (by simp; linarith)
  · exact run_with true false (by simp; linarith) (by simp; linarith)
  · exact run_with false true (by simp; linarith) (by simp; linarith)
  · exact run_with false false (by simp; linarith) (by simp; linarith)

private lemma u_linIndep {C : Set (Fin 3 → ℝ)} (hC : Convex ℝ C) {u v : Fin 3 → Fin 3 → ℝ}
    (h : Shatters3x3 C u v) (hu0 : u 0 = 0) :
    LinearIndependent ℝ ![u 1, u 2] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  have hnot0 : g 0 ≠ 0 ∨ g 1 ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hne
    intro k; fin_cases k <;> simp [hall.1, hall.2]
  have hsum_vec : g 0 • u 1 + g 1 • u 2 = 0 := by
    simpa [Fin.sum_univ_two] using hg
  have kill : ∀ (p0 p1 p2 : Fin 3), p1 ≠ p0 → p2 ≠ p0 →
      ∀ (w1 w2 : ℝ), 0 ≤ w1 → 0 ≤ w2 → w1 + w2 = 1 →
      w1 • u p1 + w2 • u p2 = u p0 → False := by
    intro p0 p1 p2 hp1 hp2 w1 w2 hw1 hw2 h12 heq
    exact not_mem_conv3 hC h (mkPair p0 0) (mkPair p1 0) (mkPair p2 0) (mkPair p2 0)
      (by simp [mkPair_eq_iff, hp1]) (by simp [mkPair_eq_iff, hp2]) (by simp [mkPair_eq_iff, hp2])
      w1 w2 0 hw1 hw2 le_rfl (by linarith) (by
        simp only [mkPair, Matrix.cons_val_zero, Matrix.cons_val_one, zero_smul, add_zero, smul_add]
        have : w1 • u p1 + w1 • v 0 + (w2 • u p2 + w2 • v 0) =
            (w1 • u p1 + w2 • u p2) + (w1 + w2) • v 0 := by rw [add_smul]; abel
        rw [this, heq, h12, one_smul])
  let a : ℝ := -(g 0 + g 1)
  let b : ℝ := g 0
  let c : ℝ := g 1
  have habc : a + b + c = 0 := by ring
  have hrel : a • u 0 + b • u 1 + c • u 2 = 0 := by simp [hu0, b, c, hsum_vec]
  have one_pos : ∀ (i0 i1 i2 : Fin 3), i1 ≠ i0 → i2 ≠ i0 →
      ∀ (x y z : ℝ), 0 < x → y ≤ 0 → z ≤ 0 → x + y + z = 0 →
      x • u i0 + y • u i1 + z • u i2 = 0 → False := by
    intro i0 i1 i2 hi1 hi2 x y z hx hy hz hxyz hrel'
    apply kill i0 i1 i2 hi1 hi2 (-y / x) (-z / x)
      (div_nonneg (by linarith) hx.le) (div_nonneg (by linarith) hx.le)
      (by field_simp; linarith)
    ext k
    have hk := congrFun hrel' k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk ⊢
    field_simp
    linarith
  have hrel_neg : (-a) • u 0 + (-b) • u 1 + (-c) • u 2 = 0 := by
    calc _ = -(a • u 0 + b • u 1 + c • u 2) := by simp [neg_smul]; abel
      _ = 0 := by rw [hrel, neg_zero]
  by_cases ha : 0 < a
  · by_cases hb : b ≤ 0
    · by_cases hc : c ≤ 0
      · exact one_pos 0 1 2 (by decide) (by decide) a b c ha hb hc habc hrel
      · push Not at hc
        exact one_pos 1 0 2 (by decide) (by decide) (-b) (-a) (-c) (by linarith) (by linarith) (by linarith) (by linarith) (by convert hrel_neg using 1; abel)
    · push Not at hb
      exact one_pos 2 0 1 (by decide) (by decide) (-c) (-a) (-b) (by linarith) (by linarith) (by linarith) (by linarith) (by convert hrel_neg using 1; abel)
  · push Not at ha
    by_cases hb : 0 < b
    · by_cases hc : c ≤ 0
      · exact one_pos 1 0 2 (by decide) (by decide) b a c hb ha hc (by linarith) (by convert hrel using 1; abel)
      · push Not at hc
        exact one_pos 0 1 2 (by decide) (by decide) (-a) (-b) (-c) (by linarith) (by linarith) (by linarith) (by linarith) hrel_neg
    · push Not at hb
      have hc : 0 < c := by
        rcases hnot0 with h0 | h1
        · have : b < 0 := lt_of_le_of_ne hb h0; linarith
        · by_contra hc'
          push Not at hc'
          have : c < 0 := lt_of_le_of_ne hc' h1
          linarith
      exact one_pos 2 0 1 (by decide) (by decide) c a b hc ha hb (by linarith) (by convert hrel using 1; abel)

private lemma not_in_span_u {C : Set (Fin 3 → ℝ)} (hC : Convex ℝ C) {u v : Fin 3 → Fin 3 → ℝ}
    (h : Shatters3x3 C u v) (hu0 : u 0 = 0) (hv0 : v 0 = 0)
    (hv1 : v 1 ∈ Submodule.span ℝ {u 1, u 2}) : False := by
  rw [Submodule.mem_span_pair] at hv1
  obtain ⟨β, γ, hbg⟩ := hv1
  have hv1_ne : v 1 ≠ 0 := by
    intro h0
    have hv_ind := u_linIndep hC (shatters3x3_swap h) hv0
    have := hv_ind.ne_zero (0 : Fin 2)
    exact this (by simpa using h0)
  have hnot0 : β ≠ 0 ∨ γ ≠ 0 := by
    by_contra hall; push Not at hall
    apply hv1_ne; rw [← hbg, hall.1, hall.2]; simp
  have kill_bary : ∀ (i0 i1 i2 j0 j1 : Fin 3), i1 ≠ i0 → i2 ≠ i0 → j1 ≠ j0 →
      ∀ (x y z : ℝ), 0 < x → y ≤ 0 → z ≤ 0 → x + y + z = 0 →
      x • u i0 + y • u i1 + z • u i2 = v j1 - v j0 → False := by
    intro i0 i1 i2 j0 j1 hi1 hi2 hj1 x y z hx hy hz hxyz hrel
    have h1x : 0 < 1 + x := by linarith
    apply not_mem_conv3 hC h (mkPair i0 j0) (mkPair i0 j1) (mkPair i1 j0) (mkPair i2 j0)
      (by simp [mkPair_eq_iff, hj1]) (by simp [mkPair_eq_iff, hi1]) (by simp [mkPair_eq_iff, hi2])
      (1 / (1 + x)) (-y / (1 + x)) (-z / (1 + x))
      (div_nonneg zero_le_one h1x.le) (div_nonneg (by linarith) h1x.le) (div_nonneg (by linarith) h1x.le)
      (by field_simp; linarith)
    ext k
    have hk := congrFun hrel k
    simp only [mkPair, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] at hk ⊢
    field_simp
    linear_combination -hk - v j0 k * hxyz
  let α : ℝ := -(β + γ)
  have habg : α + β + γ = 0 := by ring
  have hrel1 : α • u 0 + β • u 1 + γ • u 2 = v 1 - v 0 := by
    simp [hu0, hv0, hbg]
  have hrel2 : (-α) • u 0 + (-β) • u 1 + (-γ) • u 2 = v 0 - v 1 := by
    calc _ = -(α • u 0 + β • u 1 + γ • u 2) := by simp [neg_smul]; abel
      _ = -(v 1 - v 0) := by rw [hrel1]
      _ = v 0 - v 1 := by abel
  by_cases ha : 0 < α
  · by_cases hb : β ≤ 0
    · by_cases hc : γ ≤ 0
      · exact kill_bary 0 1 2 0 1 (by decide) (by decide) (by decide) α β γ ha hb hc habg hrel1
      · push Not at hc
        exact kill_bary 1 0 2 1 0 (by decide) (by decide) (by decide) (-β) (-α) (-γ)
          (by linarith) (by linarith) (by linarith) (by linarith) (by convert hrel2 using 1; abel)
    · push Not at hb
      exact kill_bary 2 0 1 1 0 (by decide) (by decide) (by decide) (-γ) (-α) (-β)
        (by linarith) (by linarith) (by linarith) (by linarith) (by convert hrel2 using 1; abel)
  · push Not at ha
    by_cases hb : 0 < β
    · by_cases hc : γ ≤ 0
      · exact kill_bary 1 0 2 0 1 (by decide) (by decide) (by decide) β α γ hb ha hc
          (by linarith) (by convert hrel1 using 1; abel)
      · push Not at hc
        exact kill_bary 0 1 2 1 0 (by decide) (by decide) (by decide) (-α) (-β) (-γ)
          (by linarith) (by linarith) (by linarith) (by linarith) hrel2
    · push Not at hb
      have hc : 0 < γ := by
        rcases hnot0 with h0 | h1
        · have : β < 0 := lt_of_le_of_ne hb h0; linarith
        · by_contra hc'; push Not at hc'
          have : γ < 0 := lt_of_le_of_ne hc' h1; linarith
      exact kill_bary 2 0 1 0 1 (by decide) (by decide) (by decide) γ α β hc ha hb
        (by linarith) (by convert hrel1 using 1; abel)

private lemma exists_sort3 (f : Fin 3 → ℝ) :
    ∃ σ : Equiv.Perm (Fin 3), f (σ 0) ≤ f (σ 1) ∧ f (σ 1) ≤ f (σ 2) := by
  by_cases h01 : f 0 ≤ f 1
  · by_cases h12 : f 1 ≤ f 2
    · exact ⟨1, h01, h12⟩
    · by_cases h02 : f 0 ≤ f 2
      · refine ⟨Equiv.swap 1 2, ?_, ?_⟩
        · have : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
          have : (Equiv.swap (1 : Fin 3) 2) 1 = 2 := by decide
          simp_all
        · have : (Equiv.swap (1 : Fin 3) 2) 1 = 2 := by decide
          have : (Equiv.swap (1 : Fin 3) 2) 2 = 1 := by decide
          simp_all; linarith
      · refine ⟨Equiv.swap 0 2 * Equiv.swap 1 2, ?_, ?_⟩
        · have h_0 : ((Equiv.swap (0 : Fin 3) 2 * Equiv.swap 1 2 : Equiv.Perm (Fin 3))) 0 = 2 := by decide
          have h_1 : ((Equiv.swap (0 : Fin 3) 2 * Equiv.swap 1 2 : Equiv.Perm (Fin 3))) 1 = 0 := by decide
          rw [h_0, h_1]; linarith
        · have h_1 : ((Equiv.swap (0 : Fin 3) 2 * Equiv.swap 1 2 : Equiv.Perm (Fin 3))) 1 = 0 := by decide
          have h_2 : ((Equiv.swap (0 : Fin 3) 2 * Equiv.swap 1 2 : Equiv.Perm (Fin 3))) 2 = 1 := by decide
          rw [h_1, h_2]; exact h01
  · by_cases h02 : f 0 ≤ f 2
    · refine ⟨Equiv.swap 0 1, ?_, ?_⟩
      · have h_0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
        have h_1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
        rw [h_0, h_1]; linarith
      · have h_1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
        have h_2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
        rw [h_1, h_2]; exact h02
    · by_cases h12 : f 1 ≤ f 2
      · refine ⟨Equiv.swap 0 1 * Equiv.swap 1 2, ?_, ?_⟩
        · have h_0 : ((Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3))) 0 = 1 := by decide
          have h_1 : ((Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3))) 1 = 2 := by decide
          rw [h_0, h_1]; exact h12
        · have h_1 : ((Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3))) 1 = 2 := by decide
          have h_2 : ((Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3))) 2 = 0 := by decide
          rw [h_1, h_2]; linarith
      · refine ⟨Equiv.swap 0 2, ?_, ?_⟩
        · have h_0 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := by decide
          have h_1 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
          rw [h_0, h_1]; linarith
        · have h_1 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
          have h_2 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := by decide
          rw [h_1, h_2]; linarith

private lemma not_shatters3x3 {C : Set (Fin 3 → ℝ)} (hC : Convex ℝ C) (u v : Fin 3 → Fin 3 → ℝ) :
    ¬ Shatters3x3 C u v := by
  intro hsh
  have hsh0 := shatters3x3_translate hsh (u 0) (v 0)
  set u' : Fin 3 → Fin 3 → ℝ := fun a => u a - u 0
  set v' : Fin 3 → Fin 3 → ℝ := fun b => v b - v 0
  have hu0 : u' 0 = 0 := sub_self _
  have hv0 : v' 0 = 0 := sub_self _
  have hu_li := u_linIndep hC hsh0 hu0
  have hv_li := u_linIndep hC (shatters3x3_swap hsh0) hv0
  let PU : Submodule ℝ (Fin 3 → ℝ) := Submodule.span ℝ {u' 1, u' 2}
  let PV : Submodule ℝ (Fin 3 → ℝ) := Submodule.span ℝ {v' 1, v' 2}
  have hPU_rank : Module.finrank ℝ PU = 2 := by
    have hrange : Set.range ![u' 1, u' 2] = {u' 1, u' 2} := by
      ext x; simp [or_comm]
    rw [show PU = Submodule.span ℝ (Set.range ![u' 1, u' 2]) by rw [hrange]]
    rw [finrank_span_eq_card hu_li, Fintype.card_fin]
  have hPV_rank : Module.finrank ℝ PV = 2 := by
    have hrange : Set.range ![v' 1, v' 2] = {v' 1, v' 2} := by
      ext x; simp [or_comm]
    rw [show PV = Submodule.span ℝ (Set.range ![v' 1, v' 2]) by rw [hrange]]
    rw [finrank_span_eq_card hv_li, Fintype.card_fin]
  have hinf_pos : 1 ≤ Module.finrank ℝ (PU ⊓ PV : Submodule ℝ (Fin 3 → ℝ)) := by
    have hadd := Submodule.finrank_sup_add_finrank_inf_eq PU PV
    have hsup : Module.finrank ℝ (PU ⊔ PV : Submodule ℝ (Fin 3 → ℝ)) ≤ 3 := by
      calc Module.finrank ℝ (PU ⊔ PV : Submodule ℝ (Fin 3 → ℝ))
          ≤ Module.finrank ℝ (Fin 3 → ℝ) := Submodule.finrank_le _
        _ = 3 := by simp
    omega
  have hne_bot : (PU ⊓ PV : Submodule ℝ (Fin 3 → ℝ)) ≠ ⊥ := by
    intro hbot; rw [hbot, finrank_bot] at hinf_pos; omega
  obtain ⟨z, hz_mem, hz_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
  have hzU : z ∈ PU := hz_mem.1
  have hzV : z ∈ PV := hz_mem.2
  have hspan_z_rank : Module.finrank ℝ (Submodule.span ℝ ({z} : Set (Fin 3 → ℝ))) = 1 := by
    have hli : LinearIndependent ℝ (fun _ : Fin 1 => z) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have h0 : g 0 • z = 0 := by simpa using hg
      have hg0 : g 0 = 0 := (smul_eq_zero.mp h0).resolve_right hz_ne
      intro k; fin_cases k; exact hg0
    have hr : Set.range (fun _ : Fin 1 => z) = {z} := by ext x; simp
    rw [← hr, finrank_span_eq_card hli, Fintype.card_fin]
  have exists_not_span_z : ∀ (P : Submodule ℝ (Fin 3 → ℝ)), Module.finrank ℝ P = 2 → z ∈ P →
      ∃ w ∈ P, w ∉ Submodule.span ℝ ({z} : Set (Fin 3 → ℝ)) := by
    intro P hP hzP
    by_contra hall
    push Not at hall
    have hle : P ≤ Submodule.span ℝ ({z} : Set (Fin 3 → ℝ)) := fun w hw => hall w hw
    have hfr := Submodule.finrank_mono hle
    omega
  obtain ⟨e1, he1U, he1_not_z⟩ := exists_not_span_z PU hPU_rank hzU
  obtain ⟨e2, he2V, he2_not_z⟩ := exists_not_span_z PV hPV_rank hzV
  have hli_pair : ∀ (w : Fin 3 → ℝ), w ∉ Submodule.span ℝ ({z} : Set (Fin 3 → ℝ)) →
      LinearIndependent ℝ ![z, w] := by
    intro w hw
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : g 0 • z + g 1 • w = 0 := by simpa [Fin.sum_univ_two] using hg
    have hg1 : g 1 = 0 := by
      by_contra h1
      apply hw
      rw [Submodule.mem_span_singleton]
      refine ⟨-(g 0 / g 1), ?_⟩
      ext k; have hk := congrFun h0 k; simp at hk ⊢; field_simp; linarith
    have hg0 : g 0 = 0 := by
      simp [hg1] at h0
      exact h0.resolve_right hz_ne
    intro k; fin_cases k <;> assumption
  have hspanU : Submodule.span ℝ {z, e1} = PU := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]; rintro x (rfl | rfl) <;> assumption
    · have hr : Set.range ![z, e1] = {z, e1} := by ext x; simp [or_comm]
      rw [← hr, finrank_span_eq_card (hli_pair e1 he1_not_z), Fintype.card_fin, hPU_rank]
  have hspanV : Submodule.span ℝ {z, e2} = PV := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]; rintro x (rfl | rfl) <;> assumption
    · have hr : Set.range ![z, e2] = {z, e2} := by ext x; simp [or_comm]
      rw [← hr, finrank_span_eq_card (hli_pair e2 he2_not_z), Fintype.card_fin, hPV_rank]
  have he2_not_PU : e2 ∉ PU := by
    intro he2U
    have hv1_in_PU : v' 1 ∈ PU := by
      have hv1_in_PV : v' 1 ∈ PV := Submodule.subset_span (by simp)
      rw [← hspanV] at hv1_in_PV
      have hle : Submodule.span ℝ {z, e2} ≤ PU := by
        rw [Submodule.span_le]; rintro x (rfl | rfl) <;> assumption
      exact hle hv1_in_PV
    exact not_in_span_u hC hsh0 hu0 hv0 hv1_in_PU
  have hbasis_li : LinearIndependent ℝ ![e1, e2, z] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : g 0 • e1 + g 1 • e2 + g 2 • z = 0 := by
      simpa [Fin.sum_univ_three] using hg
    have hg1 : g 1 = 0 := by
      by_contra h1
      apply he2_not_PU
      have he2_eq : e2 = (-(g 0 / g 1)) • e1 + (-(g 2 / g 1)) • z := by
        ext k; have hk := congrFun h0 k; simp at hk ⊢; field_simp; linarith
      rw [he2_eq]
      exact PU.add_mem (PU.smul_mem _ he1U) (PU.smul_mem _ hzU)
    have hg0 : g 0 = 0 := by
      by_contra h0'
      apply he1_not_z
      rw [Submodule.mem_span_singleton]
      refine ⟨-(g 2 / g 0), ?_⟩
      ext k; have hk := congrFun h0 k; simp [hg1] at hk ⊢; field_simp; linarith
    have hg2 : g 2 = 0 := by
      simp [hg0, hg1] at h0
      exact h0.resolve_right hz_ne
    intro k; fin_cases k <;> assumption
  have hbasis_span : ⊤ ≤ Submodule.span ℝ (Set.range ![e1, e2, z]) := by
    have htop : Submodule.span ℝ (Set.range ![e1, e2, z]) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card hbasis_li, Fintype.card_fin]; simp)
    rw [htop]
  let B : Module.Basis (Fin 3) ℝ (Fin 3 → ℝ) := Module.Basis.mk hbasis_li hbasis_span
  let e := B.equivFun
  have hsh1 := shatters3x3_linearEquiv hsh0 e
  have hC1 : Convex ℝ (e '' C) := hC.linear_image e.toLinearMap
  have he_PU : ∀ w ∈ PU, e w 1 = 0 := by
    intro w hw
    rw [← hspanU, Submodule.mem_span_pair] at hw
    obtain ⟨c1, c2, rfl⟩ := hw
    have hz_coord : e z 1 = 0 := by
      rw [show z = B 2 by simp [B]]
      simp [e, B.equivFun_self 2 1]
    have he1_coord : e e1 1 = 0 := by
      rw [show e1 = B 0 by simp [B]]
      simp [e, B.equivFun_self 0 1]
    simp [map_add, map_smul, hz_coord, he1_coord]
  have he_PV : ∀ w ∈ PV, e w 0 = 0 := by
    intro w hw
    rw [← hspanV, Submodule.mem_span_pair] at hw
    obtain ⟨c1, c2, rfl⟩ := hw
    have hz_coord : e z 0 = 0 := by
      rw [show z = B 2 by simp [B]]
      simp [e, B.equivFun_self 2 0]
    have he2_coord : e e2 0 = 0 := by
      rw [show e2 = B 1 by simp [B]]
      simp [e, B.equivFun_self 1 0]
    simp [map_add, map_smul, hz_coord, he2_coord]
  set U : Fin 3 → Fin 3 → ℝ := fun a => e (u' a)
  set V : Fin 3 → Fin 3 → ℝ := fun b => e (v' b)
  have hU_y : ∀ a, U a 1 = 0 := by
    intro a; apply he_PU
    fin_cases a
    · simp [hu0]
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  have hV_x : ∀ b, V b 0 = 0 := by
    intro b; apply he_PV
    fin_cases b
    · simp [hv0]
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  obtain ⟨σ, hσ1, hσ2⟩ := exists_sort3 (fun a => U a 0)
  obtain ⟨τ, hτ1, hτ2⟩ := exists_sort3 (fun b => V b 1)
  have hsh2 := shatters3x3_translate (shatters3x3_perm hsh1 σ τ) (U (σ 0)) (V (τ 0))
  set U2 : Fin 3 → Fin 3 → ℝ := fun a => U (σ a) - U (σ 0)
  set V2 : Fin 3 → Fin 3 → ℝ := fun b => V (τ b) - V (τ 0)
  have hU2_0 : U2 0 = 0 := sub_self _
  have hV2_0 : V2 0 = 0 := sub_self _
  have hU2_y : ∀ a, U2 a 1 = 0 := fun a => by simp [U2, hU_y]
  have hV2_x : ∀ b, V2 b 0 = 0 := fun b => by simp [V2, hV_x]
  have hU2_x01 : 0 ≤ U2 1 0 := by simp [U2]; linarith
  have hU2_x12 : U2 1 0 ≤ U2 2 0 := by simp [U2]; linarith
  have hV2_y01 : 0 ≤ V2 1 1 := by simp [V2]; linarith
  have hV2_y12 : V2 1 1 ≤ V2 2 1 := by simp [V2]; linarith
  have hU2_li := u_linIndep hC1 hsh2 hU2_0
  have hV2_li := u_linIndep hC1 (shatters3x3_swap hsh2) hV2_0
  have hU2_x2_pos : 0 < U2 2 0 := by
    by_contra hle; push Not at hle
    have hx1 : U2 1 0 = 0 := by linarith
    have hx2 : U2 2 0 = 0 := by linarith
    have hdep : (U2 2 2) • U2 1 + (-(U2 1 2)) • U2 2 = 0 := by
      apply fin3_ext
      · simp [hx1, hx2]
      · simp [hU2_y]
      · simp; ring
    have hcoeff := Fintype.linearIndependent_iff.mp hU2_li ![U2 2 2, -(U2 1 2)]
      (by simpa [Fin.sum_univ_two] using hdep)
    have hz1 : U2 1 2 = 0 := by simpa using hcoeff 1
    have hU21 : U2 1 = 0 := by apply fin3_ext <;> simp [hx1, hU2_y, hz1]
    exact hU2_li.ne_zero (0 : Fin 2) (by simpa using hU21)
  have hV2_y2_pos : 0 < V2 2 1 := by
    by_contra hle; push Not at hle
    have hy1 : V2 1 1 = 0 := by linarith
    have hy2 : V2 2 1 = 0 := by linarith
    have hdep : (V2 2 2) • V2 1 + (-(V2 1 2)) • V2 2 = 0 := by
      apply fin3_ext
      · simp [hV2_x]
      · simp [hy1, hy2]
      · simp; ring
    have hcoeff := Fintype.linearIndependent_iff.mp hV2_li ![V2 2 2, -(V2 1 2)]
      (by simpa [Fin.sum_univ_two] using hdep)
    have hz1 : V2 1 2 = 0 := by simpa using hcoeff 1
    have hV21 : V2 1 = 0 := by apply fin3_ext <;> simp [hV2_x, hy1, hz1]
    exact hV2_li.ne_zero (0 : Fin 2) (by simpa using hV21)
  let lam : ℝ := U2 1 0 / U2 2 0
  let mu : ℝ := V2 1 1 / V2 2 1
  have hlam0 : 0 ≤ lam := div_nonneg hU2_x01 hU2_x2_pos.le
  have hlam1 : lam ≤ 1 := (div_le_one hU2_x2_pos).2 hU2_x12
  have hmu0 : 0 ≤ mu := div_nonneg hV2_y01 hV2_y2_pos.le
  have hmu1 : mu ≤ 1 := (div_le_one hV2_y2_pos).2 hV2_y12
  let hU : ℝ := U2 1 2 - lam * U2 2 2
  let hV : ℝ := V2 1 2 - mu * V2 2 2
  have hhU_ne : hU ≠ 0 := by
    intro h0
    have hdep : (1 : ℝ) • U2 1 + (-lam) • U2 2 = 0 := by
      apply fin3_ext
      · simp [lam]; field_simp [hU2_x2_pos.ne']; ring
      · simp [hU2_y]
      · simp only [hU] at h0; simp; linarith
    have hc := Fintype.linearIndependent_iff.mp hU2_li ![1, -lam]
      (by simpa [Fin.sum_univ_two] using hdep)
    exact (one_ne_zero : (1 : ℝ) ≠ 0) (by simpa using hc (0 : Fin 2))
  have hhV_ne : hV ≠ 0 := by
    intro h0
    have hdep : (1 : ℝ) • V2 1 + (-mu) • V2 2 = 0 := by
      apply fin3_ext
      · simp [hV2_x]
      · simp [mu]; field_simp [hV2_y2_pos.ne']; ring
      · simp only [hV] at h0; simp; linarith
    have hc := Fintype.linearIndependent_iff.mp hV2_li ![1, -mu]
      (by simpa [Fin.sum_univ_two] using hdep)
    exact (one_ne_zero : (1 : ℝ) ≠ 0) (by simpa using hc (0 : Fin 2))
  let sx := U2 2 0
  let sy := V2 2 1
  have hsx : sx ≠ 0 := hU2_x2_pos.ne'
  have hsy : sy ≠ 0 := hV2_y2_pos.ne'
  let ax := U2 2 2 / sx
  let ay := V2 2 2 / sy
  let T : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
    { toFun := fun p => ![p 0 / sx, p 1 / sy, (p 2 - ax * p 0 - ay * p 1) / hU]
      invFun := fun q => ![sx * q 0, sy * q 1, hU * q 2 + ax * sx * q 0 + ay * sy * q 1]
      map_add' := fun p q => by apply fin3_ext <;> simp <;> ring
      map_smul' := fun r p => by apply fin3_ext <;> simp <;> ring
      left_inv := fun p => by
        apply fin3_ext <;> simp <;> field_simp [hsx, hsy, hhU_ne] <;> ring
      right_inv := fun q => by
        apply fin3_ext <;> simp <;> field_simp [hsx, hsy, hhU_ne] <;> ring }
  have hsh3 : Shatters3x3 (T '' (e '' C)) (fun a => T (U2 a)) (fun b => T (V2 b)) :=
    shatters3x3_linearEquiv hsh2 T
  have hC3 : Convex ℝ (T '' (e '' C)) := hC1.linear_image T.toLinearMap
  let r : ℝ := hV / hU
  have hr_ne : r ≠ 0 := div_ne_zero hhV_ne hhU_ne
  have hTU : (fun a => T (U2 a)) = ![![0, 0, 0], ![lam, 0, 1], ![1, 0, 0]] := by
    apply fin3_ext
    · apply fin3_ext <;> simp [T, hU2_0]
    · apply fin3_ext
      · simp [T, lam, sx]
      · simp [T, hU2_y]
      · simp only [T, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, v3_1, v3_2, hU2_y,
          mul_zero, sub_zero]
        rw [div_eq_one_iff_eq hhU_ne]
        dsimp [hU, lam, ax, sx]
        field_simp [hsx]
    · apply fin3_ext
      · simp only [T, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, v3_2, v3_0]
        exact div_self hsx
      · simp [T, hU2_y]
      · simp only [T, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, v3_2, hU2_y,
          mul_zero, sub_zero]
        rw [div_eq_zero_iff]; left
        dsimp [ax, sx]; field_simp [hsx]; ring
  have hTV : (fun b => T (V2 b)) = ![![0, 0, 0], ![0, mu, r], ![0, 1, 0]] := by
    apply fin3_ext
    · apply fin3_ext <;> simp [T, hV2_0]
    · apply fin3_ext
      · simp [T, hV2_x]
      · simp [T, mu, sy]
      · simp only [T, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, v3_1, v3_2, hV2_x,
          mul_zero, sub_zero]
        dsimp [r, hV, mu, ay, sy]
        field_simp [hsy, hhU_ne]
    · apply fin3_ext
      · simp [T, hV2_x]
      · simp only [T, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, v3_2, v3_1]
        exact div_self hsy
      · simp only [T, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, v3_2, hV2_x,
          mul_zero, sub_zero]
        rw [div_eq_zero_iff]; left
        dsimp [ay, sy]; field_simp [hsy]; ring
  rw [hTU, hTV] at hsh3
  by_cases hr : r < 0
  · let rho := -r
    have hrho : 0 < rho := by linarith
    have h1rho : 0 < 1 + rho := by linarith
    have hr_eq : r = -rho := by simp [rho]
    exact not_mem_conv4 hC3 hsh3 (mkPair 1 1) (mkPair 0 1) (mkPair 2 1) (mkPair 1 0) (mkPair 1 2)
      (by simp [mkPair_eq_iff]) (by simp [mkPair_eq_iff]) (by simp [mkPair_eq_iff]) (by simp [mkPair_eq_iff])
      (rho * (1 - lam) / (1 + rho)) (rho * lam / (1 + rho)) ((1 - mu) / (1 + rho)) (mu / (1 + rho))
      (div_nonneg (mul_nonneg hrho.le (by linarith)) h1rho.le)
      (div_nonneg (mul_nonneg hrho.le hlam0) h1rho.le)
      (div_nonneg (by linarith) h1rho.le)
      (div_nonneg hmu0 h1rho.le)
      (by field_simp; ring)
      (by
        apply fin3_ext <;>
          (simp only [mkPair_0, mkPair_1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, v3_0, v3_1, v3_2]
           try rw [hr_eq]
           field_simp [h1rho.ne']
           ring))
  · push Not at hr
    have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr_ne)
    have h1r : 0 < 1 + r := by linarith
    by_cases hlam0' : lam = 0
    · exact not_mem_conv3 hC3 hsh3 (mkPair 0 1) (mkPair 0 0) (mkPair 0 2) (mkPair 1 1)
        (by simp [mkPair_eq_iff]) (by simp [mkPair_eq_iff]) (by simp [mkPair_eq_iff])
        ((1 - mu) / (1 + r)) (mu / (1 + r)) (r / (1 + r))
        (div_nonneg (by linarith) h1r.le) (div_nonneg hmu0 h1r.le) (div_nonneg hr_pos.le h1r.le)
        (by field_simp; ring)
        (by apply fin3_ext <;> simp [mkPair, hlam0'] <;> field_simp <;> ring)
    by_cases hlam1' : lam = 1
    · exact not_mem_conv3 hC3 hsh3 (mkPair 2 1) (mkPair 2 0) (mkPair 2 2) (mkPair 1 1)
        (by simp [mkPair_eq_iff]) (by simp [mkPair_eq_iff]) (by simp [mkPair_eq_iff])
        ((1 - mu) / (1 + r)) (mu / (1 + r)) (r / (1 + r))
        (div_nonneg (by linarith) h1r.le) (div_nonneg hmu0 h1r.le) (div_nonneg hr_pos.le h1r.le)
        (by field_simp; ring)
        (by apply fin3_ext <;> simp [mkPair, hlam1'] <;> field_simp <;> ring)
    by_cases hmu0' : mu = 0
    · exact not_mem_conv3 hC3 hsh3 (mkPair 1 0) (mkPair 0 0) (mkPair 2 0) (mkPair 1 1)
        (by simp [mkPair_eq_iff]) (by simp [mkPair_eq_iff]) (by simp [mkPair_eq_iff])
        (r * (1 - lam) / (1 + r)) (r * lam / (1 + r)) (1 / (1 + r))
        (div_nonneg (mul_nonneg hr_pos.le (by linarith)) h1r.le)
        (div_nonneg (mul_nonneg hr_pos.le hlam0) h1r.le)
        (div_nonneg zero_le_one h1r.le)
        (by field_simp; ring)
        (by apply fin3_ext <;> simp [mkPair, hmu0'] <;> field_simp <;> ring)
    by_cases hmu1' : mu = 1
    · exact not_mem_conv3 hC3 hsh3 (mkPair 1 2) (mkPair 0 2) (mkPair 2 2) (mkPair 1 1)
        (by simp [mkPair_eq_iff]) (by simp [mkPair_eq_iff]) (by simp [mkPair_eq_iff])
        (r * (1 - lam) / (1 + r)) (r * lam / (1 + r)) (1 / (1 + r))
        (div_nonneg (mul_nonneg hr_pos.le (by linarith)) h1r.le)
        (div_nonneg (mul_nonneg hr_pos.le hlam0) h1r.le)
        (div_nonneg zero_le_one h1r.le)
        (by field_simp; ring)
        (by apply fin3_ext <;> simp [mkPair, hmu1'] <;> field_simp <;> ring)
    exact core_obstruction hC3
      (lt_of_le_of_ne hlam0 (Ne.symm hlam0')) (lt_of_le_of_ne hlam1 hlam1')
      (lt_of_le_of_ne hmu0 (Ne.symm hmu0')) (lt_of_le_of_ne hmu1 hmu1')
      hr_pos hsh3

end VCDimConvexTwoTwoProof

theorem OMA.solution : type_of% @VCDimConvex.hasAddVCNDimAtMost_two_two_of_convex_r3 := by
  intro C hC x y hxy
  let e : ℝ³ ≃ₗ[ℝ] (Fin 3 → ℝ) := WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)
  have hC' : Convex ℝ (e '' C) := hC.linear_image e.toLinearMap
  apply VCDimConvexTwoTwoProof.not_shatters3x3 hC' (fun a => e (x 0 a)) (fun b => e (x 1 b))
  refine ⟨fun s => e (y s), fun i s => ?_⟩
  have heq : e (y s) + (e (x 0 (i 0)) + e (x 1 (i 1))) = e (y s + ∑ k : Fin 2, x k (i k)) := by
    simp [Fin.sum_univ_two, map_add]
  rw [heq, e.injective.mem_set_image]
  exact hxy i s
