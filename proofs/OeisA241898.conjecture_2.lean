import FormalConjectures.OEIS.«241898»

/-!
Proof of `OeisA241898.conjecture_2`: every natural number is a sum of four squares none equal to 7^2.
-/

namespace OMA_A241898_C2

open MeasureTheory
open scoped Matrix

/- Part 1: 2D Gauss reduction for positive-definite determinant-1 binary quadratic forms -/

private lemma gauss_2d_aux : ∀ n : ℕ, ∀ a b c : ℤ,
    a.toNat = n → 0 < a → a * c - b * b = 1 →
    ∃ p q r s : ℤ,
      p * s - q * r = 1 ∧
      p * p + r * r = a ∧
      p * q + r * s = b ∧
      q * q + s * s = c := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b c hna ha hdet
    by_cases ha1 : a = 1
    · refine ⟨1, b, 0, 1, by ring, ?_, by ring, ?_⟩
      · omega
      · nlinarith
    · have ha2 : 2 ≤ a := by omega
      let r0 : ℤ := b % a
      have hr0_nonneg : 0 ≤ r0 := Int.emod_nonneg b (by omega)
      have hr0_lt : r0 < a := Int.emod_lt_of_pos b ha
      let k : ℤ := if 2 * r0 ≤ a then b / a else b / a + 1
      let b' : ℤ := b - k * a
      have hdiv : r0 + a * (b / a) = b := Int.emod_add_mul_ediv b a
      have hb'_bound : 4 * (b' * b') ≤ a * a := by
        dsimp only [b', k]
        split_ifs with h
        · have heq : b - b / a * a = r0 := by linarith
          rw [heq]; nlinarith
        · have heq : b - (b / a + 1) * a = r0 - a := by linarith
          rw [heq]; nlinarith
      let c' : ℤ := a * k * k - 2 * b * k + c
      have hdet' : a * c' - b' * b' = 1 := by
        dsimp only [c', b']; ring_nf; linarith
      have hc'_pos : 0 < c' := by nlinarith
      have hc'_lt : c' < a := by nlinarith
      have hc'_nat_lt : c'.toNat < n := by omega
      obtain ⟨p', q', r', s', hd', h1', h2', h3'⟩ :=
        ih c'.toNat hc'_nat_lt c' (-b') a rfl hc'_pos (by linarith)
      refine ⟨q', -p' + k * q', s', -r' + k * s', ?_, ?_, ?_, ?_⟩
      · linear_combination hd'
      · exact h3'
      · have hbe : b = b' + k * a := by dsimp only [b']; ring
        rw [hbe]
        linear_combination -h2' + k * h3'
      · have hce : c = c' + 2 * k * b' + k * k * a := by dsimp only [c', b']; ring
        rw [hce]
        linear_combination h1' - 2 * k * h2' + k * k * h3'

/- Part 2: Extending a primitive 3-vector to SL(3, ℤ) -/

private lemma extend_primitive_vec3 {v0 v1 v2 w0 w1 w2 : ℤ}
    (h : v0 * w0 + v1 * w1 + v2 * w2 = 1) :
    ∃ Q : Matrix (Fin 3) (Fin 3) ℤ,
      Q.det = 1 ∧ Q 0 0 = v0 ∧ Q 1 0 = v1 ∧ Q 2 0 = v2 := by
  by_cases hg0 : Int.gcd v0 v1 = 0
  · have hv0 : v0 = 0 := Int.gcd_eq_zero_iff.mp hg0 |>.1
    have hv1 : v1 = 0 := Int.gcd_eq_zero_iff.mp hg0 |>.2
    rw [hv0, hv1] at h
    have hv2 : v2 = 1 ∨ v2 = -1 := by
      have h1 : v2 * w2 = 1 := by linarith
      have h2 : v2 ∣ 1 := ⟨w2, h1.symm⟩
      exact Int.isUnit_iff.mp (isUnit_of_dvd_one h2)
    rcases hv2 with rfl | rfl
    · refine ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], ?_, by simp [hv0], by simp [hv1], by simp⟩
      decide
    · refine ⟨!![0, 1, 0; 0, 0, -1; -1, 0, 0], ?_, by simp [hv0], by simp [hv1], by simp⟩
      decide
  · set g : ℤ := (Int.gcd v0 v1 : ℤ)
    have hg_pos : 0 < g := by omega
    have hdv0 : g ∣ v0 := Int.gcd_dvd_left v0 v1
    have hdv1 : g ∣ v1 := Int.gcd_dvd_right v0 v1
    obtain ⟨u0, hu0⟩ := hdv0
    obtain ⟨u1, hu1⟩ := hdv1
    set a0 : ℤ := Int.gcdA v0 v1
    set b0 : ℤ := Int.gcdB v0 v1
    have hbez0 : g = v0 * a0 + v1 * b0 := Int.gcd_eq_gcd_ab v0 v1
    have hu_bez : u0 * a0 + u1 * b0 = 1 := by
      have : g * (u0 * a0 + u1 * b0) = g * 1 := by
        calc g * (u0 * a0 + u1 * b0)
            = (g * u0) * a0 + (g * u1) * b0 := by ring
          _ = v0 * a0 + v1 * b0 := by rw [← hu0, ← hu1]
          _ = g := hbez0.symm
          _ = g * 1 := by ring
      exact mul_left_cancel₀ (by omega) this
    have hgcd1 : Int.gcd g v2 = 1 := by
      set d : ℤ := (Int.gcd g v2 : ℤ)
      have hd1 : d ∣ g := Int.gcd_dvd_left g v2
      have hd2 : d ∣ v2 := Int.gcd_dvd_right g v2
      have hd_one : d ∣ 1 := by
        have hlin : g * (u0 * w0 + u1 * w1) + v2 * w2 = 1 := by
          calc g * (u0 * w0 + u1 * w1) + v2 * w2
              = (g * u0) * w0 + (g * u1) * w1 + v2 * w2 := by ring
            _ = v0 * w0 + v1 * w1 + v2 * w2 := by rw [← hu0, ← hu1]
            _ = 1 := h
        rw [← hlin]
        exact dvd_add (dvd_mul_of_dvd_left hd1 _) (dvd_mul_of_dvd_left hd2 _)
      have hd_nat : Int.gcd g v2 ∣ 1 := by
        exact Int.ofNat_dvd.mp hd_one
      exact Nat.eq_one_of_dvd_one hd_nat
    set a1 : ℤ := Int.gcdA g v2
    set b1 : ℤ := Int.gcdB g v2
    have hbez1 : g * a1 + v2 * b1 = 1 := by
      have := Int.gcd_eq_gcd_ab g v2
      rw [hgcd1] at this
      simpa using this.symm
    refine ⟨!![v0, -b0, -b1 * u0; v1, a0, -b1 * u1; v2, 0, a1], ?_, by simp, by simp, by simp⟩
    simp [Matrix.det_fin_three]
    calc v0 * a0 * a1 + b0 * v1 * a1 + b0 * (b1 * u1) * v2 + b1 * u0 * a0 * v2
        = (g * a1 + v2 * b1) * (u0 * a0 + u1 * b0) := by rw [hu0, hu1]; ring
      _ = 1 * 1 := by rw [hbez1, hu_bez]
      _ = 1 := one_mul 1

/- Part 3: Minkowski's theorem on the special 3x3 unimodular form -/

private lemma volume_ball_fin3_sqrt2 :
    (8 : ENNReal) < volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt 2)) := by
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin]
  have hG1 : Real.Gamma ((3 : ℝ) / 2 + 1) = 3 / 4 * Real.sqrt Real.pi := by
    have h32 : (3 : ℝ) / 2 ≠ 0 := by norm_num
    have h12 : (1 : ℝ) / 2 ≠ 0 := by norm_num
    rw [Real.Gamma_add_one h32]
    have hrew : (3 : ℝ) / 2 = 1 / 2 + 1 := by norm_num
    rw [hrew, Real.Gamma_add_one h12, Real.Gamma_one_half_eq]
    ring
  rw [show ((3 : ℕ) : ℝ) = (3 : ℝ) by norm_num, hG1]
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hsqrt_pi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi_pos
  have hsqrt2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsimp : Real.sqrt Real.pi ^ 3 / (3 / 4 * Real.sqrt Real.pi) = 4 / 3 * Real.pi := by
    have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt hpi_pos.le
    field_simp [hsqrt_pi_pos.ne']
    nlinarith [hsq]
  rw [hsimp, ← ENNReal.ofReal_pow hsqrt2_nonneg,
    ← ENNReal.ofReal_mul (pow_nonneg hsqrt2_nonneg 3)]
  have h8 : (8 : ENNReal) = ENNReal.ofReal 8 := by norm_num
  rw [h8]
  apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr
  have hsqrt2_gt1 : 1 < Real.sqrt 2 := by
    rw [Real.lt_sqrt zero_le_one]; norm_num
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2_cube : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    calc Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [hsqrt2_sq]
  rw [hsqrt2_cube]
  have hpi_gt3 : 3 < Real.pi := Real.pi_gt_three
  nlinarith

private lemma volume_fundamentalDomain_euclideanBasisFun :
    volume (ZSpan.fundamentalDomain (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis) = 1 := by
  have hpre :
      (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) ⁻¹'
        ZSpan.fundamentalDomain (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis =
      Set.univ.pi (fun _ : Fin 3 => Set.Ico (0 : ℝ) 1) := by
    ext x
    simp [ZSpan.mem_fundamentalDomain, EuclideanSpace.basisFun_toBasis]
  have hmeas : MeasurableSet (ZSpan.fundamentalDomain (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis) :=
    ZSpan.fundamentalDomain_measurableSet _
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage hmeas.nullMeasurableSet, hpre,
    volume_pi, Measure.pi_pi]
  simp [Real.volume_Ico]

private lemma minkowski_short_vector {a b c d m : ℤ}
    (ha : 0 < a) (hm : 0 < m) (hdet1 : a * c - b * b = m) (hdet2 : d * m - a = 1) :
    ∃ v : Fin 3 → ℤ, v ≠ 0 ∧
      a * v 0 * v 0 + 2 * b * v 0 * v 1 + c * v 1 * v 1 + 2 * v 1 * v 2 + d * v 2 * v 2 = 1 := by
  let aR : ℝ := (a : ℝ)
  let bR : ℝ := (b : ℝ)
  let cR : ℝ := (c : ℝ)
  let dR : ℝ := (d : ℝ)
  let mR : ℝ := (m : ℝ)
  have haR : 0 < aR := Int.cast_pos.mpr ha
  have hmR : 0 < mR := Int.cast_pos.mpr hm
  let sa : ℝ := Real.sqrt aR
  let sm : ℝ := Real.sqrt mR
  have hsa : 0 < sa := Real.sqrt_pos.mpr haR
  have hsm : 0 < sm := Real.sqrt_pos.mpr hmR
  have hsa2 : sa ^ 2 = aR := Real.sq_sqrt haR.le
  have hsm2 : sm ^ 2 = mR := Real.sq_sqrt hmR.le
  have hdet1R : aR * cR - bR * bR = mR := by dsimp only [aR, bR, cR, mR]; exact_mod_cast hdet1
  have hdet2R : dR * mR - aR = 1 := by dsimp only [aR, dR, mR]; exact_mod_cast hdet2
  let U : Matrix (Fin 3) (Fin 3) ℝ :=
    !![sa, bR / sa, 0;
       0, sm / sa, sa / sm;
       0, 0, 1 / sm]
  let Uinv : Matrix (Fin 3) (Fin 3) ℝ :=
    !![1 / sa, -bR / (sa * sm), bR / sm;
       0, sa / sm, -aR / sm;
       0, 0, sm]
  have hUU : U * Uinv = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, Uinv, Matrix.mul_apply, Fin.sum_univ_three] <;>
      field_simp [hsa.ne', hsm.ne'] <;>
      (try rw [hsa2]) <;> ring
  have hUinvU : Uinv * U = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, Uinv, Matrix.mul_apply, Fin.sum_univ_three] <;>
      field_simp [hsa.ne', hsm.ne'] <;>
      (try rw [hsa2]) <;> ring
  have hUdet : U.det = 1 := by
    simp [U, Matrix.det_fin_three]
    field_simp [hsa.ne', hsm.ne']
  let b0 : Module.Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let eU : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    LinearEquiv.ofLinearMap (Matrix.toLin b0 b0 U) (Matrix.toLin b0 b0 Uinv)
      (by rw [← Matrix.toLin_mul, hUU, Matrix.toLin_one])
      (by rw [← Matrix.toLin_mul, hUinvU, Matrix.toLin_one])
  let bas : Module.Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) := b0.map eU
  have hdet_bas : b0.det bas = 1 := by
    rw [Module.Basis.det_apply]
    have hmat : b0.toMatrix bas = U := by
      ext i j
      rw [Module.Basis.toMatrix_apply]
      change b0.repr (Matrix.toLin b0 b0 U (b0 j)) i = U i j
      rw [Matrix.toLin_self]
      simp [Finsupp.single_apply]
    rw [hmat, hUdet]
  have hvol_fund : volume (ZSpan.fundamentalDomain bas) = 1 := by
    rw [ZSpan.measure_fundamentalDomain bas volume b0, hdet_bas,
      volume_fundamentalDomain_euclideanBasisFun]
    simp
  set L : AddSubgroup (EuclideanSpace ℝ (Fin 3)) :=
    (Submodule.span ℤ (Set.range bas)).toAddSubgroup
  have hLcount : Countable L := by
    let f : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 3) := fun v => ∑ i : Fin 3, (v i : ℤ) • bas i
    have hsurj : ∀ x : L, ∃ v : Fin 3 → ℤ, f v = x.1 := by
      intro ⟨x, hx⟩
      rw [Submodule.mem_toAddSubgroup, Finsupp.mem_span_range_iff_exists_finsupp] at hx
      obtain ⟨c, rfl⟩ := hx
      exact ⟨fun i => c i, by simp [f, Finsupp.sum_fintype]⟩
    exact Function.Surjective.countable (f := fun v => (⟨f v, by
      change f v ∈ Submodule.span ℤ (Set.range bas)
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)⟩ : L))
      (fun x => by obtain ⟨v, hv⟩ := hsurj x; exact ⟨v, Subtype.ext hv⟩)
  have hfund : IsAddFundamentalDomain L (ZSpan.fundamentalDomain bas) volume :=
    ZSpan.isAddFundamentalDomain' bas volume
  have h_lt : volume (ZSpan.fundamentalDomain bas) * 2 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) <
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt 2)) := by
    rw [hvol_fund, finrank_euclideanSpace_fin]
    simpa [show (1 : ENNReal) * 2 ^ 3 = 8 by norm_num] using volume_ball_fin3_sqrt2
  obtain ⟨⟨x, hxL⟩, hxne0, hxball⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      hfund (fun y hy => by simpa [Metric.mem_ball, norm_neg] using hy)
      (convex_ball 0 (Real.sqrt 2)) h_lt
  have hx_ne : x ≠ 0 := fun h => hxne0 (Subtype.ext h)
  rw [Submodule.mem_toAddSubgroup, Finsupp.mem_span_range_iff_exists_finsupp] at hxL
  obtain ⟨coeff, hcoeff⟩ := hxL
  let v : Fin 3 → ℤ := fun i => coeff i
  have hv_ne : v ≠ 0 := by
    intro hv0
    apply hx_ne
    rw [← hcoeff]
    have hc0 : coeff = 0 := by ext i; exact congr_fun hv0 i
    simp [hc0]
  have hx_eq : x = eU (∑ i : Fin 3, (v i : ℝ) • b0 i) := by
    rw [← hcoeff, map_sum]
    rw [Finsupp.sum_fintype]
    · apply Finset.sum_congr rfl
      intro i _
      change (coeff i : ℤ) • eU (b0 i) = eU ((v i : ℝ) • b0 i)
      rw [map_smul, Int.cast_smul_eq_zsmul ℝ]
    · intro i; simp
  have hx_coord : ∀ i : Fin 3, x i = (U.mulVec (fun j => (v j : ℝ))) i := by
    intro i
    rw [hx_eq]
    have hrepr : b0.repr (∑ j : Fin 3, (v j : ℝ) • b0 j) =
        Finsupp.equivFunOnFinite.symm (fun j => (v j : ℝ)) := by
      ext j; simp [Finsupp.single_apply]
    change (Matrix.toLin b0 b0 U (∑ j : Fin 3, (v j : ℝ) • b0 j)) i = _
    rw [Matrix.toLin_apply, hrepr]
    simp [b0, EuclideanSpace.basisFun_toBasis, Pi.single_apply]
  have hnorm_sq : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  have hform_eq : (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 =
      ((a * v 0 * v 0 + 2 * b * v 0 * v 1 + c * v 1 * v 1 + 2 * v 1 * v 2 + d * v 2 * v 2 : ℤ) : ℝ) := by
    rw [hx_coord 0, hx_coord 1, hx_coord 2]
    simp [U, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    change (sa * (v 0 : ℝ) + bR / sa * (v 1 : ℝ)) ^ 2 +
        (sm / sa * (v 1 : ℝ) + sa / sm * (v 2 : ℝ)) ^ 2 +
        (sm⁻¹ * (v 2 : ℝ)) ^ 2 =
      aR * (v 0 : ℝ) * (v 0 : ℝ) + 2 * bR * (v 0 : ℝ) * (v 1 : ℝ) +
        cR * (v 1 : ℝ) * (v 1 : ℝ) + 2 * (v 1 : ℝ) * (v 2 : ℝ) +
        dR * (v 2 : ℝ) * (v 2 : ℝ)
    field_simp [hsa.ne', hsm.ne']
    rw [hsa2, hsm2]
    linear_combination -mR * (v 1 : ℝ) ^ 2 * hdet1R - aR * (v 2 : ℝ) ^ 2 * hdet2R
  have hnorm_pos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx_ne)
  have hnorm_lt2 : ‖x‖ ^ 2 < 2 := by
    have hlt : ‖x‖ < Real.sqrt 2 := by simpa [Metric.mem_ball, dist_zero_right] using hxball
    have hnn : 0 ≤ ‖x‖ := norm_nonneg x
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  set q : ℤ := a * v 0 * v 0 + 2 * b * v 0 * v 1 + c * v 1 * v 1 + 2 * v 1 * v 2 + d * v 2 * v 2
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith [hnorm_sq, hform_eq]
  have hq_lt2 : (q : ℝ) < 2 := by linarith [hnorm_sq, hform_eq]
  have hq_posZ : 0 < q := by exact_mod_cast hq_pos
  have hq_lt2Z : q < 2 := by exact_mod_cast hq_lt2
  exact ⟨v, hv_ne, by omega⟩

/- Part 4: From unimodular 3x3 form to sum of three squares -/

private lemma three_squares_of_matrix {a b c d m : ℤ}
    (ha : 0 < a) (hm : 0 < m) (hdet1 : a * c - b * b = m) (hdet2 : d * m - a = 1) :
    ∃ x y z : ℤ, x * x + y * y + z * z = m := by
  let A : Matrix (Fin 3) (Fin 3) ℤ := !![a, b, 0; b, c, 1; 0, 1, d]
  have hAsym : Aᵀ = A := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hAdet : A.det = 1 := by
    simp [A, Matrix.det_fin_three]
    nlinarith
  have hquad_pos : ∀ y : Fin 3 → ℤ, y ≠ 0 →
      0 < a * y 0 * y 0 + 2 * b * y 0 * y 1 + c * y 1 * y 1 + 2 * y 1 * y 2 + d * y 2 * y 2 := by
    intro y hy
    have hmul : (a * m) * (a * y 0 * y 0 + 2 * b * y 0 * y 1 + c * y 1 * y 1 +
          2 * y 1 * y 2 + d * y 2 * y 2) =
        m * (a * y 0 + b * y 1) ^ 2 + (m * y 1 + a * y 2) ^ 2 + a * y 2 ^ 2 := by
      linear_combination m * y 1 ^ 2 * hdet1 + a * y 2 ^ 2 * hdet2
    have hpos_rhs : 0 < m * (a * y 0 + b * y 1) ^ 2 + (m * y 1 + a * y 2) ^ 2 + a * y 2 ^ 2 := by
      by_contra hle
      have hle' : m * (a * y 0 + b * y 1) ^ 2 + (m * y 1 + a * y 2) ^ 2 + a * y 2 ^ 2 ≤ 0 := by
        linarith
      have ht1 : 0 ≤ m * (a * y 0 + b * y 1) ^ 2 := mul_nonneg hm.le (sq_nonneg _)
      have ht2 : 0 ≤ (m * y 1 + a * y 2) ^ 2 := sq_nonneg _
      have ht3 : 0 ≤ a * y 2 ^ 2 := mul_nonneg ha.le (sq_nonneg _)
      have hz3 : a * y 2 ^ 2 = 0 := by linarith
      have hy2 : y 2 = 0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp hz3).resolve_left ha.ne')
      have hz2 : (m * y 1 + a * y 2) ^ 2 = 0 := by linarith
      have hy1 : y 1 = 0 := by
        rw [hy2, mul_zero, add_zero] at hz2
        exact (mul_eq_zero.mp (sq_eq_zero_iff.mp hz2)).resolve_left hm.ne'
      have hz1 : m * (a * y 0 + b * y 1) ^ 2 = 0 := by linarith
      have hy0 : y 0 = 0 := by
        rw [hy1, mul_zero, add_zero] at hz1
        exact (mul_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hz1).resolve_left hm.ne'))).resolve_left ha.ne'
      apply hy; ext i; fin_cases i <;> assumption
    exact pos_of_mul_pos_right (by linarith [hmul, hpos_rhs]) (mul_pos ha hm).le
  obtain ⟨v, hvne, hv1⟩ := minkowski_short_vector ha hm hdet1 hdet2
  have hlin : v 0 * (a * v 0 + b * v 1) + v 1 * (b * v 0 + c * v 1 + v 2) +
      v 2 * (v 1 + d * v 2) = 1 := by linarith
  obtain ⟨Q, hQdet, hQ0, hQ1, hQ2⟩ := extend_primitive_vec3 hlin
  let A1 : Matrix (Fin 3) (Fin 3) ℤ := Qᵀ * A * Q
  have hA1sym : A1ᵀ = A1 := by
    simp only [A1, Matrix.transpose_mul, Matrix.transpose_transpose, hAsym, Matrix.mul_assoc]
  have hA1det : A1.det = 1 := by
    simp [A1, Matrix.det_mul, Matrix.det_transpose, hQdet, hAdet]
  have hA1_00 : A1 0 0 = 1 := by
    simp [A1, A, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, hQ0, hQ1, hQ2]
    linarith
  let E : Matrix (Fin 3) (Fin 3) ℤ := !![1, -(A1 0 1), -(A1 0 2); 0, 1, 0; 0, 0, 1]
  have hEdet : E.det = 1 := by
    rw [Matrix.det_fin_three]
    simp [E]
  let M : Matrix (Fin 3) (Fin 3) ℤ := Q * E
  have hMdet : M.det = 1 := by simp [M, Matrix.det_mul, hQdet, hEdet]
  let A2 : Matrix (Fin 3) (Fin 3) ℤ := Eᵀ * A1 * E
  have hA2eq : A2 = Mᵀ * A * M := by
    simp only [A2, A1, M, Matrix.transpose_mul, Matrix.mul_assoc]
  have hA2sym : A2ᵀ = A2 := by
    simp only [A2, Matrix.transpose_mul, Matrix.transpose_transpose, hA1sym, Matrix.mul_assoc]
  have hA2det : A2.det = 1 := by
    simp [A2, Matrix.det_mul, Matrix.det_transpose, hEdet, hA1det]
  have hA1_10 : A1 1 0 = A1 0 1 := by
    have := congr_fun (congr_fun hA1sym 0) 1; simpa [Matrix.transpose_apply] using this
  have hA1_20 : A1 2 0 = A1 0 2 := by
    have := congr_fun (congr_fun hA1sym 0) 2; simpa [Matrix.transpose_apply] using this
  have hA2_00 : A2 0 0 = 1 := by
    simp [A2, E, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, hA1_00]
  have hA2_01 : A2 0 1 = 0 := by
    simp [A2, E, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, hA1_00]
  have hA2_02 : A2 0 2 = 0 := by
    simp [A2, E, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, hA1_00]
  have hA2_10 : A2 1 0 = 0 := by
    simp [A2, E, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, hA1_00, hA1_10]
  have hA2_20 : A2 2 0 = 0 := by
    simp [A2, E, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, hA1_00, hA1_20]
  have hA2_21 : A2 2 1 = A2 1 2 := by
    have := congr_fun (congr_fun hA2sym 1) 2; simpa [Matrix.transpose_apply] using this
  have hBdet : A2 1 1 * A2 2 2 - A2 1 2 * A2 1 2 = 1 := by
    have hd := hA2det
    rw [Matrix.det_fin_three, hA2_00, hA2_01, hA2_02, hA2_10, hA2_20, hA2_21] at hd
    linarith
  have hBpos : 0 < A2 1 1 := by
    let y : Fin 3 → ℤ := fun i => M i 1
    have hyne : y ≠ 0 := by
      intro hy0
      have hM0 : M.det = 0 := by
        rw [Matrix.det_fin_three]
        have h0 : M 0 1 = 0 := congr_fun hy0 0
        have h1 : M 1 1 = 0 := congr_fun hy0 1
        have h2 : M 2 1 = 0 := congr_fun hy0 2
        simp [h0, h1, h2]
      omega
    have hval : A2 1 1 = a * y 0 * y 0 + 2 * b * y 0 * y 1 + c * y 1 * y 1 +
        2 * y 1 * y 2 + d * y 2 * y 2 := by
      rw [hA2eq]
      simp [A, y, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
      ring
    rw [hval]
    exact hquad_pos y hyne
  obtain ⟨p, q, r, s, hRdet2, hR11, hR12, hR22⟩ :=
    gauss_2d_aux (A2 1 1).toNat (A2 1 1) (A2 1 2) (A2 2 2) rfl hBpos hBdet
  let R3 : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, p, q; 0, r, s]
  have hR3det : R3.det = 1 := by
    rw [Matrix.det_fin_three]
    simp [R3]
    linarith
  have hR3gram : R3ᵀ * R3 = A2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [R3, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
        hA2_00, hA2_01, hA2_02, hA2_10, hA2_20, hA2_21]
    · exact hR11
    · exact hR12
    · linarith
    · exact hR22
  let P : Matrix (Fin 3) (Fin 3) ℤ := R3 * M.adjugate
  let S : Matrix (Fin 3) (Fin 3) ℤ := M * R3.adjugate
  have hMMadj : M * M.adjugate = 1 := by rw [Matrix.mul_adjugate, hMdet, one_smul]
  have hMadjM : M.adjugate * M = 1 := by rw [Matrix.adjugate_mul, hMdet, one_smul]
  have hRR : R3 * R3.adjugate = 1 := by rw [Matrix.mul_adjugate, hR3det, one_smul]
  have hRadjR : R3.adjugate * R3 = 1 := by rw [Matrix.adjugate_mul, hR3det, one_smul]
  have hAadjA : A.adjugate * A = 1 := by rw [Matrix.adjugate_mul, hAdet, one_smul]
  have hPgram : Pᵀ * P = A := by
    calc Pᵀ * P
        = M.adjugateᵀ * (R3ᵀ * R3) * M.adjugate := by
          simp only [P, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = M.adjugateᵀ * (Mᵀ * A * M) * M.adjugate := by rw [hR3gram, hA2eq]
      _ = (M * M.adjugate)ᵀ * A * (M * M.adjugate) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = A := by rw [hMMadj, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hPS : P * S = 1 := by
    calc P * S = R3 * (M.adjugate * M) * R3.adjugate := by simp only [P, S, Matrix.mul_assoc]
      _ = R3 * R3.adjugate := by rw [hMadjM, Matrix.mul_one]
      _ = 1 := hRR
  have hSP : S * P = 1 := by
    calc S * P = M * (R3.adjugate * R3) * M.adjugate := by simp only [P, S, Matrix.mul_assoc]
      _ = M * M.adjugate := by rw [hRadjR, Matrix.mul_one]
      _ = 1 := hMMadj
  have hAadj : A.adjugate = S * Sᵀ := by
    have hASS : A * (S * Sᵀ) = 1 := by
      calc A * (S * Sᵀ) = (Pᵀ * P) * (S * Sᵀ) := by rw [hPgram]
        _ = Pᵀ * ((P * S) * Sᵀ) := by rw [Matrix.mul_assoc Pᵀ P, ← Matrix.mul_assoc P S Sᵀ]
        _ = Pᵀ * Sᵀ := by rw [hPS, Matrix.one_mul]
        _ = (S * P)ᵀ := (Matrix.transpose_mul S P).symm
        _ = 1 := by rw [hSP, Matrix.transpose_one]
    calc A.adjugate = A.adjugate * (A * (S * Sᵀ)) := by rw [hASS, Matrix.mul_one]
      _ = (A.adjugate * A) * (S * Sᵀ) := (Matrix.mul_assoc _ _ _).symm
      _ = S * Sᵀ := by rw [hAadjA, Matrix.one_mul]
  have h22 : A.adjugate 2 2 = m := by
    simp [A, Matrix.adjugate_fin_three]
    exact hdet1
  have hS22 : (S * Sᵀ) 2 2 = S 2 0 * S 2 0 + S 2 1 * S 2 1 + S 2 2 * S 2 2 := by
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  refine ⟨S 2 0, S 2 1, S 2 2, ?_⟩
  rw [← hS22, ← hAadj, h22]

/- Part 5: Dirichlet's theorem + Jacobi reciprocity for m ≡ 2, 3, 6 (mod 8) -/

private lemma modEq_coprime {a b m : ℕ} (h : a ≡ b [MOD m]) (hb : b.Coprime m) :
    a.Coprime m := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec, h, ← Nat.gcd_rec, Nat.gcd_comm]
  exact hb.gcd_eq_one

private lemma exists_sq_add_mod_prime {p : ℕ} [Fact p.Prime] {m : ℕ}
    (hm_ne : (((-(m : ℤ)) : ℤ) : ZMod p) ≠ 0) (hleg : jacobiSym (-(m : ℤ)) p = 1) :
    ∃ b : ℤ, (p : ℤ) ∣ b * b + m := by
  have hl : legendreSym p (-(m : ℤ)) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]; exact hleg
  obtain ⟨x, hx⟩ := (legendreSym.eq_one_iff p hm_ne).mp hl
  refine ⟨(x.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have hxval : ((x.val : ℕ) : ZMod p) = x := ZMod.natCast_zmod_val x
  rw [hxval]
  have hx' : x * x = -((m : ℕ) : ZMod p) := by simpa using hx.symm
  rw [hx']
  ring

private lemma three_squares_mod8_3 {m : ℕ} (hm : m % 8 = 3) :
    ∃ x y z : ℤ, x * x + y * y + z * z = m := by
  have hm_ge3 : 3 ≤ m := by omega
  have hm_odd : Odd m := ⟨m / 2, by omega⟩
  have hm4 : m % 4 = 3 := by omega
  let r : ℕ := (m - 1) / 2
  have h2r : 2 * r + 1 = m := by omega
  have hcop_rm : r.Coprime m := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hd1 : Nat.gcd r m ∣ r := Nat.gcd_dvd_left r m
    have hd2 : Nat.gcd r m ∣ m := Nat.gcd_dvd_right r m
    have hd3 : Nat.gcd r m ∣ 2 * r := dvd_mul_of_dvd_right hd1 2
    have hd_one : Nat.gcd r m ∣ m - 2 * r := Nat.dvd_sub hd2 hd3
    rw [show m - 2 * r = 1 by omega] at hd_one
    exact Nat.eq_one_of_dvd_one hd_one
  have hcop_4m : Nat.Coprime 4 m := by
    have : Nat.Coprime 2 m := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
    simpa [show (4 : ℕ) = 2 * 2 by norm_num] using this.mul_left this
  let crt := Nat.chineseRemainder hcop_4m 1 r
  let t : ℕ := crt.1
  have ht4 : t ≡ 1 [MOD 4] := crt.2.1
  have htm : t ≡ r [MOD m] := crt.2.2
  have ht_cop4 : t.Coprime 4 := modEq_coprime ht4 (by decide)
  have ht_copm : t.Coprime m := modEq_coprime htm hcop_rm
  have ht_cop : t.Coprime (4 * m) := ht_cop4.mul_right ht_copm
  obtain ⟨p, hp2, hp_prime, hp_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq 2 (q := 4 * m) (a := t) (by omega) ht_cop
  have : Fact p.Prime := ⟨hp_prime⟩
  have hp4_mod : p ≡ 1 [MOD 4] :=
    (hp_mod.of_dvd (dvd_mul_right 4 m)).trans ht4
  have hp4 : p % 4 = 1 := by simpa [Nat.ModEq] using hp4_mod
  have hp_odd : Odd p := ⟨p / 2, by omega⟩
  have hpm_mod : p ≡ r [MOD m] :=
    (hp_mod.of_dvd (dvd_mul_left m 4)).trans htm
  have hdiv_m : m ∣ 2 * p + 1 := by
    have h2p : 2 * p + 1 ≡ 2 * r + 1 [MOD m] := (hpm_mod.mul_left 2).add_right 1
    rw [h2r] at h2p
    exact Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using h2p)
  have hp_copm : p.Coprime m := modEq_coprime hpm_mod hcop_rm
  have hnotdvd : ¬ (p ∣ m) := by
    intro h
    have hd1 : p ∣ Nat.gcd p m := Nat.dvd_gcd dvd_rfl h
    rw [hp_copm.gcd_eq_one] at hd1
    have hle := Nat.le_of_dvd one_pos hd1
    omega
  have hm_ne_zmod : (((-(m : ℤ)) : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    have hd : (p : ℤ) ∣ -(m : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (-(m : ℤ)) p).mp h0
    have hd2 : (p : ℤ) ∣ (m : ℤ) := dvd_neg.mp hd
    exact hnotdvd (Int.ofNat_dvd.mp hd2)
  have hjac : jacobiSym (-(m : ℤ)) p = 1 := by
    rw [show (-(m : ℤ)) = (-1) * (m : ℤ) by ring, jacobiSym.mul_left,
      jacobiSym.at_neg_one hp_odd, ZMod.χ₄_nat_one_mod_four hp4, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four' hm_odd hp4]
    have h2p_eq : jacobiSym (2 * (p : ℤ)) m = jacobiSym (-1) m := by
      apply jacobiSym.mod_left'
      obtain ⟨k, hk⟩ := hdiv_m
      have hkZ : (2 * p : ℤ) = (m : ℤ) * (k : ℤ) + (-1) := by omega
      rw [hkZ, Int.mul_add_emod_self_left]
    have hmul2 : jacobiSym 2 m * jacobiSym (p : ℤ) m = -1 := by
      rw [← jacobiSym.mul_left, h2p_eq, jacobiSym.at_neg_one hm_odd,
        ZMod.χ₄_nat_three_mod_four hm4]
    have hj2 : jacobiSym 2 m = -1 := by
      rw [jacobiSym.at_two hm_odd, ZMod.χ₈_nat_mod_eight, hm]
      decide
    rw [hj2] at hmul2
    linarith
  obtain ⟨b0, hb0⟩ := exists_sq_add_mod_prime hm_ne_zmod hjac
  let b : ℤ := if b0 % 2 = 1 then b0 else b0 + (p : ℤ)
  have hb_odd : b % 2 = 1 := by
    dsimp only [b]; split_ifs with h <;> omega
  have hbp : (p : ℤ) ∣ b * b + m := by
    dsimp only [b]
    split_ifs with h
    · exact hb0
    · have : (b0 + p) * (b0 + p) + m = (b0 * b0 + m) + p * (2 * b0 + p) := by ring
      rw [this]
      exact dvd_add hb0 (dvd_mul_right _ _)
  have hb2 : (2 : ℤ) ∣ b * b + m := by
    have : (b * b + m) % 2 = 0 := by
      have hb2mod : (b * b) % 2 = 1 := by
        rw [Int.mul_emod, hb_odd]; norm_num
      omega
    exact Int.dvd_of_emod_eq_zero this
  have h2p_dvd : (2 * (p : ℤ)) ∣ b * b + m := by
    have hcop2p : IsCoprime (2 : ℤ) (p : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have hcopN : Nat.gcd 2 p = 1 := (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).gcd_eq_one
      exact hcopN
    exact hcop2p.mul_dvd hb2 hbp
  obtain ⟨c, hc⟩ := h2p_dvd
  obtain ⟨dN, hdN⟩ := hdiv_m
  refine three_squares_of_matrix (a := 2 * (p : ℤ)) (b := b) (c := c) (d := (dN : ℤ)) (m := (m : ℤ))
    (by omega) (by omega) ?_ ?_
  · linarith
  · have : (2 * p + 1 : ℤ) = (m : ℤ) * (dN : ℤ) := by exact_mod_cast hdN
    linarith

private lemma three_squares_mod8_2_or_6 {m : ℕ} (hm : m % 8 = 2 ∨ m % 8 = 6) :
    ∃ x y z : ℤ, x * x + y * y + z * z = m := by
  let m0 : ℕ := m / 2
  have hm_eq : m = 2 * m0 := by omega
  have hm0_pos : 1 ≤ m0 := by omega
  have hm0_odd : Odd m0 := ⟨m0 / 2, by omega⟩
  let r8 : ℕ := if m % 8 = 2 then 1 else 5
  have hr8_cop : r8.Coprime 8 := by
    dsimp only [r8]; split_ifs <;> decide
  have hcop_8m0 : Nat.Coprime 8 m0 := by
    have h2 : Nat.Coprime 2 m0 := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
    have h4 : Nat.Coprime 4 m0 := by simpa [show (4 : ℕ) = 2 * 2 by norm_num] using h2.mul_left h2
    simpa [show (8 : ℕ) = 4 * 2 by norm_num] using h4.mul_left h2
  let crt := Nat.chineseRemainder hcop_8m0 r8 (m0 - 1)
  let t : ℕ := crt.1
  have ht8 : t ≡ r8 [MOD 8] := crt.2.1
  have htm0 : t ≡ m0 - 1 [MOD m0] := crt.2.2
  have ht_cop8 : t.Coprime 8 := modEq_coprime ht8 hr8_cop
  have hcop_pred : (m0 - 1).Coprime m0 := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hd1 : Nat.gcd (m0 - 1) m0 ∣ m0 - 1 := Nat.gcd_dvd_left _ _
    have hd2 : Nat.gcd (m0 - 1) m0 ∣ m0 := Nat.gcd_dvd_right _ _
    have hd_one : Nat.gcd (m0 - 1) m0 ∣ m0 - (m0 - 1) := Nat.dvd_sub hd2 hd1
    rw [show m0 - (m0 - 1) = 1 by omega] at hd_one
    exact Nat.eq_one_of_dvd_one hd_one
  have ht_copm0 : t.Coprime m0 := modEq_coprime htm0 hcop_pred
  have ht_cop : t.Coprime (8 * m0) := ht_cop8.mul_right ht_copm0
  obtain ⟨p, hp2, hp_prime, hp_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq 2 (q := 8 * m0) (a := t) (by omega) ht_cop
  have : Fact p.Prime := ⟨hp_prime⟩
  have hp8_mod : p ≡ r8 [MOD 8] := (hp_mod.of_dvd (dvd_mul_right 8 m0)).trans ht8
  have hp8 : p % 8 = r8 := by
    have hr8_lt : r8 < 8 := by dsimp only [r8]; split_ifs <;> omega
    have := hp8_mod
    rw [Nat.ModEq, Nat.mod_eq_of_lt hr8_lt] at this
    exact this
  have hp4 : p % 4 = 1 := by
    dsimp only [r8] at hp8; split_ifs at hp8 <;> omega
  have hp_odd : Odd p := ⟨p / 2, by omega⟩
  have hpm0_mod : p ≡ m0 - 1 [MOD m0] := (hp_mod.of_dvd (dvd_mul_left m0 8)).trans htm0
  have hdiv_m0 : m0 ∣ p + 1 := by
    have h1 : p + 1 ≡ (m0 - 1) + 1 [MOD m0] := hpm0_mod.add_right 1
    rw [Nat.sub_add_cancel hm0_pos] at h1
    exact Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using h1)
  have hdiv_2 : 2 ∣ p + 1 := by omega
  have hdiv_m : m ∣ p + 1 := by
    rw [hm_eq]
    have hcop2m0 : Nat.Coprime 2 m0 := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
    exact hcop2m0.mul_dvd_of_dvd_of_dvd hdiv_2 hdiv_m0
  have hp_cop8m0 : p.Coprime (8 * m0) := modEq_coprime hp_mod ht_cop
  have hnotdvd : ¬ (p ∣ m) := by
    intro h
    have h2 : p ∣ 8 * m0 := dvd_trans h ⟨4, by omega⟩
    have hd1 : p ∣ Nat.gcd p (8 * m0) := Nat.dvd_gcd dvd_rfl h2
    rw [hp_cop8m0.gcd_eq_one] at hd1
    have hle := Nat.le_of_dvd one_pos hd1
    omega
  have hm_ne_zmod : (((-(m : ℤ)) : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    have hd : (p : ℤ) ∣ -(m : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (-(m : ℤ)) p).mp h0
    have hd2 : (p : ℤ) ∣ (m : ℤ) := dvd_neg.mp hd
    exact hnotdvd (Int.ofNat_dvd.mp hd2)
  have hjac : jacobiSym (-(m : ℤ)) p = 1 := by
    have hmeqZ : (-(m : ℤ)) = (-1) * 2 * (m0 : ℤ) := by omega
    rw [hmeqZ, jacobiSym.mul_left, jacobiSym.mul_left,
      jacobiSym.at_neg_one hp_odd, ZMod.χ₄_nat_one_mod_four hp4, one_mul,
      jacobiSym.at_two hp_odd, ZMod.χ₈_nat_mod_eight, hp8,
      jacobiSym.quadratic_reciprocity_one_mod_four' hm0_odd hp4]
    have hp_m0_eq : jacobiSym (p : ℤ) m0 = jacobiSym (-1) m0 := by
      apply jacobiSym.mod_left'
      obtain ⟨k, hk⟩ := hdiv_m0
      have hkZ : (p : ℤ) = (m0 : ℤ) * (k : ℤ) + (-1) := by omega
      rw [hkZ, Int.mul_add_emod_self_left]
    rw [hp_m0_eq, jacobiSym.at_neg_one hm0_odd]
    rcases hm with hm2 | hm6
    · have hr8_eq : r8 = 1 := by dsimp only [r8]; rw [if_pos hm2]
      have hm04 : m0 % 4 = 1 := by omega
      rw [hr8_eq, ZMod.χ₄_nat_one_mod_four hm04]
      decide
    · have hr8_eq : r8 = 5 := by dsimp only [r8]; rw [if_neg (by omega)]
      have hm04 : m0 % 4 = 3 := by omega
      rw [hr8_eq, ZMod.χ₄_nat_three_mod_four hm04]
      decide
  obtain ⟨b, hb⟩ := exists_sq_add_mod_prime hm_ne_zmod hjac
  obtain ⟨c, hc⟩ := hb
  obtain ⟨dN, hdN⟩ := hdiv_m
  refine three_squares_of_matrix (a := (p : ℤ)) (b := b) (c := c) (d := (dN : ℤ)) (m := (m : ℤ))
    (by omega) (by omega) ?_ ?_
  · linarith
  · have : (p + 1 : ℤ) = (m : ℤ) * (dN : ℤ) := by exact_mod_cast hdN
    linarith

private lemma three_squares_of_mod8 {m : ℕ} (hm : m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 6) :
    ∃ x y z : ℤ, x * x + y * y + z * z = m := by
  rcases hm with h2 | h3 | h6
  · exact three_squares_mod8_2_or_6 (Or.inl h2)
  · exact three_squares_mod8_3 h3
  · exact three_squares_mod8_2_or_6 (Or.inr h6)

/- Part 6: Asymptotic four-square decompositions avoiding 7 -/

private lemma four_squares_no7_of_dvd4 {n : ℕ} (h4 : n % 4 = 0) :
    ∃ a b c d : ℕ, a ≠ 7 ∧ b ≠ 7 ∧ c ≠ 7 ∧ d ≠ 7 ∧ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares (n / 4)
  refine ⟨2 * a, 2 * b, 2 * c, 2 * d, by omega, by omega, by omega, by omega, ?_⟩
  have hn : 4 * (n / 4) = n := by omega
  nlinarith

private lemma int_sq_mod2 (x : ℤ) : (x * x) % 2 = x % 2 := by
  rcases Int.even_or_odd x with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · have : (t + t) * (t + t) = 2 * (2 * (t * t)) := by ring
    omega
  · have : (2 * t + 1) * (2 * t + 1) = 2 * (2 * (t * t) + 2 * t) + 1 := by ring
    omega

private lemma int_sq_mod4_of_odd {x : ℤ} (h : x % 2 = 1) : (x * x) % 4 = 1 := by
  let q := x / 2
  have hx : x = 2 * q + 1 := by omega
  have : x * x = 4 * (q * q + q) + 1 := by rw [hx]; ring
  omega

private lemma int_sq_mod4_of_even {x : ℤ} (h : x % 2 = 0) : (x * x) % 4 = 0 := by
  let q := x / 2
  have hx : x = 2 * q := by omega
  have : x * x = 4 * (q * q) := by rw [hx]; ring
  omega

private lemma four_squares_no7_of_mod4_2 {n : ℕ} (hn : 1640 < n) (h4 : n % 4 = 2) :
    ∃ a b c d : ℕ, a ≠ 7 ∧ b ≠ 7 ∧ c ≠ 7 ∧ d ≠ 7 ∧ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n := by
  let m : ℕ := Nat.sqrt (n / 4)
  have hm_ge20 : 20 ≤ m := by
    rw [Nat.le_sqrt]; omega
  have hlo : 4 * m ^ 2 ≤ n := by
    have h1 : m * m ≤ n / 4 := Nat.sqrt_le (n / 4)
    rw [sq]; omega
  have hhi : n < 4 * (m + 1) ^ 2 := by
    have h1 : n / 4 < (m + 1) * (m + 1) := Nat.lt_succ_sqrt (n / 4)
    rw [sq]; omega
  let k : ℕ := n - 4 * m ^ 2
  have hk_lt : k < 8 * m + 4 := by
    have hexp : 4 * (m + 1) ^ 2 = 4 * m ^ 2 + 8 * m + 4 := by ring
    omega
  have hk_mod4 : k % 4 = 2 := by omega
  have hk_mod8 : k % 8 = 2 ∨ k % 8 = 3 ∨ k % 8 = 6 := by omega
  obtain ⟨u, v, w, huvw⟩ := three_squares_of_mod8 hk_mod8
  have hpar : (u + v + w) % 2 = 0 := by
    have hu := int_sq_mod2 u
    have hv := int_sq_mod2 v
    have hw := int_sq_mod2 w
    omega
  let α : ℤ := (u + v + w) / 2
  let β : ℤ := (u - v - w) / 2
  let γ : ℤ := (-u + v - w) / 2
  let δ : ℤ := (-u - v + w) / 2
  have h2α : 2 * α = u + v + w := by omega
  have h2β : 2 * β = u - v - w := by omega
  have h2γ : 2 * γ = -u + v - w := by omega
  have h2δ : 2 * δ = -u - v + w := by omega
  have hsum1 : α + β + γ + δ = 0 := by linarith
  have hsum2 : α ^ 2 + β ^ 2 + γ ^ 2 + δ ^ 2 = (k : ℤ) := by
    have h4eq : (2 * α) ^ 2 + (2 * β) ^ 2 + (2 * γ) ^ 2 + (2 * δ) ^ 2 =
        4 * (u * u + v * v + w * w) := by
      rw [h2α, h2β, h2γ, h2δ]; ring
    linarith
  have hbound : ∀ t : ℤ, t ^ 2 ≤ (k : ℤ) → 7 < (m : ℤ) + t := by
    intro t ht
    by_contra hle
    have hneg : (m : ℤ) - 7 ≤ -t := by linarith
    have hm_sub_pos : (0 : ℤ) < (m : ℤ) - 7 := by omega
    have hsq : ((m : ℤ) - 7) ^ 2 ≤ t ^ 2 := by nlinarith
    have hk_le : (k : ℤ) < ((m : ℤ) - 7) ^ 2 := by
      have hmZ : (20 : ℤ) ≤ (m : ℤ) := by omega
      have hkZ : (k : ℤ) < 8 * (m : ℤ) + 4 := by exact_mod_cast hk_lt
      nlinarith
    linarith
  have hα : 7 < (m : ℤ) + α := hbound α (by linarith [sq_nonneg β, sq_nonneg γ, sq_nonneg δ])
  have hβ : 7 < (m : ℤ) + β := hbound β (by linarith [sq_nonneg α, sq_nonneg γ, sq_nonneg δ])
  have hγ : 7 < (m : ℤ) + γ := hbound γ (by linarith [sq_nonneg α, sq_nonneg β, sq_nonneg δ])
  have hδ : 7 < (m : ℤ) + δ := hbound δ (by linarith [sq_nonneg α, sq_nonneg β, sq_nonneg γ])
  refine ⟨((m : ℤ) + α).toNat, ((m : ℤ) + β).toNat, ((m : ℤ) + γ).toNat, ((m : ℤ) + δ).toNat,
    by omega, by omega, by omega, by omega, ?_⟩
  zify
  rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega),
    Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
  have hnk : (4 * (m : ℤ) ^ 2) + (k : ℤ) = (n : ℤ) := by dsimp only [k]; zify [hlo]; ring
  linear_combination 2 * (m : ℤ) * hsum1 + hsum2 + hnk

private lemma four_squares_no7_of_odd {n : ℕ} (hn : 1640 < n) (hodd : n % 2 = 1) :
    ∃ a b c d : ℕ, a ≠ 7 ∧ b ≠ 7 ∧ c ≠ 7 ∧ d ≠ 7 ∧ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n := by
  let s : ℕ := Nat.sqrt (4 * n)
  have hs_ge81 : 81 ≤ s := by
    rw [Nat.le_sqrt]; omega
  let m : ℕ := (s - 1) / 4
  have hm_ge20 : 20 ≤ m := by omega
  have hs_lo : 4 * m + 1 ≤ s := by omega
  have hs_hi : s ≤ 4 * m + 4 := by omega
  have hs_sq_le : s * s ≤ 4 * n := Nat.sqrt_le (4 * n)
  have hs_sq_gt : 4 * n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt (4 * n)
  have hlo : 4 * m ^ 2 + 2 * m < n := by
    have h1 : (4 * m + 1) * (4 * m + 1) ≤ s * s := Nat.mul_le_mul hs_lo hs_lo
    have h2 : (4 * m + 1) * (4 * m + 1) = 4 * (4 * m ^ 2 + 2 * m) + 1 := by ring
    omega
  have hhi : n ≤ 4 * m ^ 2 + 10 * m + 6 := by
    have h1 : (s + 1) * (s + 1) ≤ (4 * m + 5) * (4 * m + 5) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : (4 * m + 5) * (4 * m + 5) = 4 * (4 * m ^ 2 + 10 * m + 6) + 1 := by ring
    omega
  let r : ℕ := n - (4 * m ^ 2 + 2 * m)
  have hr_pos : 1 ≤ r := by omega
  have hr_le : r ≤ 8 * m + 6 := by omega
  have hr_odd : r % 2 = 1 := by omega
  let K : ℕ := 4 * r - 1
  have hK_mod8 : K % 8 = 2 ∨ K % 8 = 3 ∨ K % 8 = 6 := by omega
  obtain ⟨u0, v, w, huvw0⟩ := three_squares_of_mod8 hK_mod8
  have hK_mod4 : K % 4 = 3 := by omega
  have hall_odd : u0 % 2 = 1 ∧ v % 2 = 1 ∧ w % 2 = 1 := by
    have h4mod : ∀ x : ℤ, (x * x) % 4 = if x % 2 = 0 then 0 else 1 := fun x => by
      by_cases hx : x % 2 = 0
      · simp [hx, int_sq_mod4_of_even hx]
      · have hx1 : x % 2 = 1 := by omega
        simp [hx, int_sq_mod4_of_odd hx1]
    have hu := h4mod u0
    have hv := h4mod v
    have hw := h4mod w
    split_ifs at hu hv hw <;> omega
  let u : ℤ := if (1 + u0 + v + w) % 4 = 0 then u0 else -u0
  have huvw : u * u + v * v + w * w = (K : ℤ) := by
    dsimp only [u]; split_ifs <;> linarith
  have hu_odd : u % 2 = 1 := by
    dsimp only [u]; split_ifs <;> omega
  have hdiv4_1 : (1 + u + v + w) % 4 = 0 := by
    dsimp only [u]
    split_ifs with h
    · exact h
    · omega
  have hdiv4_2 : (1 + u - v - w) % 4 = 0 := by omega
  have hdiv4_3 : (1 - u + v - w) % 4 = 0 := by omega
  have hdiv4_4 : (1 - u - v + w) % 4 = 0 := by omega
  let α : ℤ := (1 + u + v + w) / 4
  let β : ℤ := (1 + u - v - w) / 4
  let γ : ℤ := (1 - u + v - w) / 4
  let δ : ℤ := (1 - u - v + w) / 4
  have h4α : 4 * α = 1 + u + v + w := by omega
  have h4β : 4 * β = 1 + u - v - w := by omega
  have h4γ : 4 * γ = 1 - u + v - w := by omega
  have h4δ : 4 * δ = 1 - u - v + w := by omega
  have hsum1 : α + β + γ + δ = 1 := by linarith
  have hsum2 : α ^ 2 + β ^ 2 + γ ^ 2 + δ ^ 2 = (r : ℤ) := by
    have hK_eq : (K : ℤ) + 1 = 4 * (r : ℤ) := by omega
    have h16eq : (4 * α) ^ 2 + (4 * β) ^ 2 + (4 * γ) ^ 2 + (4 * δ) ^ 2 =
        4 * (1 + u * u + v * v + w * w) := by
      rw [h4α, h4β, h4γ, h4δ]; ring
    linarith
  have hbound : ∀ t : ℤ, t ^ 2 ≤ (r : ℤ) → 7 < (m : ℤ) + t := by
    intro t ht
    by_contra hle
    have hneg : (m : ℤ) - 7 ≤ -t := by linarith
    have hm_sub_pos : (0 : ℤ) < (m : ℤ) - 7 := by omega
    have hsq : ((m : ℤ) - 7) ^ 2 ≤ t ^ 2 := by
      rw [show t ^ 2 = (-t) ^ 2 by ring]
      exact pow_le_pow_left₀ hm_sub_pos.le hneg 2
    have hr_lt : (r : ℤ) < ((m : ℤ) - 7) ^ 2 := by
      have hrZ : (r : ℤ) ≤ 8 * (m : ℤ) + 6 := by exact_mod_cast hr_le
      have hpoly : ((m : ℤ) - 7) ^ 2 - (8 * (m : ℤ) + 6) = ((m : ℤ) - 20) * ((m : ℤ) - 2) + 3 := by
        ring
      have hprod : 0 ≤ ((m : ℤ) - 20) * ((m : ℤ) - 2) := mul_nonneg (by omega) (by omega)
      linarith
    linarith
  have hα : 7 < (m : ℤ) + α := hbound α (by linarith [sq_nonneg β, sq_nonneg γ, sq_nonneg δ])
  have hβ : 7 < (m : ℤ) + β := hbound β (by linarith [sq_nonneg α, sq_nonneg γ, sq_nonneg δ])
  have hγ : 7 < (m : ℤ) + γ := hbound γ (by linarith [sq_nonneg α, sq_nonneg β, sq_nonneg δ])
  have hδ : 7 < (m : ℤ) + δ := hbound δ (by linarith [sq_nonneg α, sq_nonneg β, sq_nonneg γ])
  refine ⟨((m : ℤ) + α).toNat, ((m : ℤ) + β).toNat, ((m : ℤ) + γ).toNat, ((m : ℤ) + δ).toNat,
    by omega, by omega, by omega, by omega, ?_⟩
  zify
  rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega),
    Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
  have hnr : (4 * (m : ℤ) ^ 2 + 2 * (m : ℤ)) + (r : ℤ) = (n : ℤ) := by
    have hlo' : 4 * m ^ 2 + 2 * m ≤ n := by omega
    dsimp only [r]; zify [hlo']; ring
  linear_combination 2 * (m : ℤ) * hsum1 + hsum2 + hnr

/- Part 7: Finite verification for n ≤ 1640 -/

private def checkBlock (k : ℕ) : List (ℕ × ℕ × ℕ × ℕ) → Bool
  | [] => true
  | (a, b, c, d) :: rest =>
    a != 7 && b != 7 && c != 7 && d != 7 &&
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 == k &&
    checkBlock (k + 1) rest

private lemma exists_of_checkBlock {k : ℕ} {L : List (ℕ × ℕ × ℕ × ℕ)}
    (h : checkBlock k L = true) {n : ℕ} (hlo : k ≤ n) (hhi : n < k + L.length) :
    ∃ a b c d : ℕ, a ≠ 7 ∧ b ≠ 7 ∧ c ≠ 7 ∧ d ≠ 7 ∧ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n := by
  induction L generalizing k with
  | nil => simp at hhi; omega
  | cons hd tl ih =>
    rcases hd with ⟨a, b, c, d⟩
    simp only [checkBlock, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
    rcases eq_or_lt_of_le hlo with rfl | hlt
    · exact ⟨a, b, c, d, h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2⟩
    · simp only [List.length_cons] at hhi
      exact ih h.2 (by omega) (by omega)

private def wBlock0 : List (ℕ × ℕ × ℕ × ℕ) := [
  (0,0,0,0), (1,0,0,0), (1,1,0,0), (1,1,1,0), (2,0,0,0), (2,1,0,0), (2,1,1,0), (2,1,1,1),
  (2,2,0,0), (3,0,0,0), (3,1,0,0), (3,1,1,0), (3,1,1,1), (3,2,0,0), (3,2,1,0), (3,2,1,1),
  (4,0,0,0), (4,1,0,0), (4,1,1,0), (4,1,1,1), (4,2,0,0), (4,2,1,0), (4,2,1,1), (3,3,2,1),
  (4,2,2,0), (5,0,0,0), (5,1,0,0), (5,1,1,0), (5,1,1,1), (5,2,0,0), (5,2,1,0), (5,2,1,1),
  (4,4,0,0), (5,2,2,0), (5,3,0,0), (5,3,1,0), (6,0,0,0), (6,1,0,0), (6,1,1,0), (6,1,1,1),
  (6,2,0,0), (6,2,1,0), (6,2,1,1), (5,4,1,1), (6,2,2,0), (6,3,0,0), (6,3,1,0), (6,3,1,1),
  (6,2,2,2), (6,3,2,0), (6,3,2,1), (5,5,1,0), (6,4,0,0), (6,4,1,0), (6,4,1,1), (6,3,3,1),
  (6,4,2,0), (6,4,2,1), (6,3,3,2), (5,5,3,0), (6,4,2,2), (6,5,0,0), (6,5,1,0), (6,5,1,1),
  (8,0,0,0), (8,1,0,0), (8,1,1,0), (8,1,1,1), (8,2,0,0), (8,2,1,0), (8,2,1,1), (6,5,3,1),
  (8,2,2,0), (8,3,0,0), (8,3,1,0), (8,3,1,1), (8,2,2,2), (8,3,2,0), (8,3,2,1), (6,5,3,3),
  (8,4,0,0), (9,0,0,0), (9,1,0,0), (9,1,1,0), (9,1,1,1), (9,2,0,0), (9,2,1,0), (9,2,1,1),
  (8,4,2,2), (9,2,2,0), (9,3,0,0), (9,3,1,0), (9,3,1,1), (9,2,2,2), (9,3,2,0), (9,3,2,1),
  (8,4,4,0), (9,4,0,0), (9,4,1,0), (9,4,1,1)
]

private def wBlock1 : List (ℕ × ℕ × ℕ × ℕ) := [
  (10,0,0,0), (10,1,0,0), (10,1,1,0), (10,1,1,1), (10,2,0,0), (10,2,1,0), (10,2,1,1), (9,5,1,0),
  (10,2,2,0), (10,3,0,0), (10,3,1,0), (10,3,1,1), (10,2,2,2), (10,3,2,0), (10,3,2,1), (9,5,3,0),
  (10,4,0,0), (10,4,1,0), (10,4,1,1), (10,3,3,1), (10,4,2,0), (11,0,0,0), (11,1,0,0), (11,1,1,0),
  (11,1,1,1), (11,2,0,0), (11,2,1,0), (11,2,1,1), (8,8,0,0), (11,2,2,0), (11,3,0,0), (11,3,1,0),
  (11,3,1,1), (11,2,2,2), (11,3,2,0), (11,3,2,1), (10,6,0,0), (11,4,0,0), (11,4,1,0), (11,4,1,1),
  (11,3,3,1), (11,4,2,0), (11,4,2,1), (11,3,3,2), (12,0,0,0), (12,1,0,0), (12,1,1,0), (12,1,1,1),
  (12,2,0,0), (12,2,1,0), (12,2,1,1), (11,5,2,1), (12,2,2,0), (12,3,0,0), (12,3,1,0), (12,3,1,1),
  (12,2,2,2), (12,3,2,0), (12,3,2,1), (11,6,1,1), (12,4,0,0), (12,4,1,0), (12,4,1,1), (12,3,3,1),
  (12,4,2,0), (12,4,2,1), (12,3,3,2), (11,6,3,1), (12,4,2,2), (13,0,0,0), (13,1,0,0), (13,1,1,0),
  (13,1,1,1), (13,2,0,0), (13,2,1,0), (13,2,1,1), (12,4,4,0), (13,2,2,0), (13,3,0,0), (13,3,1,0),
  (13,3,1,1), (13,2,2,2), (13,3,2,0), (13,3,2,1), (12,6,2,0), (13,4,0,0), (13,4,1,0), (13,4,1,1),
  (13,3,3,1), (13,4,2,0), (13,4,2,1), (13,3,3,2), (12,4,4,4), (13,4,2,2), (13,5,0,0), (13,5,1,0),
  (14,0,0,0), (14,1,0,0), (14,1,1,0), (14,1,1,1)
]

private def wBlock2 : List (ℕ × ℕ × ℕ × ℕ) := [
  (14,2,0,0), (14,2,1,0), (14,2,1,1), (13,5,3,0), (14,2,2,0), (14,3,0,0), (14,3,1,0), (14,3,1,1),
  (14,2,2,2), (14,3,2,0), (14,3,2,1), (13,5,4,1), (14,4,0,0), (14,4,1,0), (14,4,1,1), (14,3,3,1),
  (14,4,2,0), (14,4,2,1), (14,3,3,2), (13,5,5,0), (14,4,2,2), (14,5,0,0), (14,5,1,0), (14,5,1,1),
  (12,8,4,0), (15,0,0,0), (15,1,0,0), (15,1,1,0), (15,1,1,1), (15,2,0,0), (15,2,1,0), (15,2,1,1),
  (14,6,0,0), (15,2,2,0), (15,3,0,0), (15,3,1,0), (15,3,1,1), (15,2,2,2), (15,3,2,0), (15,3,2,1),
  (14,6,2,2), (15,4,0,0), (15,4,1,0), (15,4,1,1), (15,3,3,1), (15,4,2,0), (15,4,2,1), (15,3,3,2),
  (14,6,4,0), (15,4,2,2), (15,5,0,0), (15,5,1,0), (15,5,1,1), (14,5,4,4), (15,5,2,0), (15,5,2,1),
  (16,0,0,0), (16,1,0,0), (16,1,1,0), (16,1,1,1), (16,2,0,0), (16,2,1,0), (16,2,1,1), (15,6,1,1),
  (16,2,2,0), (16,3,0,0), (16,3,1,0), (16,3,1,1), (16,2,2,2), (16,3,2,0), (16,3,2,1), (15,6,3,1),
  (16,4,0,0), (16,4,1,0), (16,4,1,1), (16,3,3,1), (16,4,2,0), (16,4,2,1), (16,3,3,2), (15,6,3,3),
  (16,4,2,2), (16,5,0,0), (16,5,1,0), (16,5,1,1), (15,5,5,3), (16,5,2,0), (16,5,2,1), (15,6,5,1),
  (16,4,4,0), (17,0,0,0), (17,1,0,0), (17,1,1,0), (17,1,1,1), (17,2,0,0), (17,2,1,0), (17,2,1,1),
  (16,6,2,0), (17,2,2,0), (17,3,0,0), (17,3,1,0)
]

private def wBlock3 : List (ℕ × ℕ × ℕ × ℕ) := [
  (17,3,1,1), (17,2,2,2), (17,3,2,0), (17,3,2,1), (16,4,4,4), (17,4,0,0), (17,4,1,0), (17,4,1,1),
  (17,3,3,1), (17,4,2,0), (17,4,2,1), (17,3,3,2), (16,6,4,2), (17,4,2,2), (17,5,0,0), (17,5,1,0),
  (17,5,1,1), (16,6,5,0), (17,5,2,0), (17,5,2,1), (16,8,0,0), (17,4,4,0), (17,5,2,2), (17,5,3,0),
  (18,0,0,0), (18,1,0,0), (18,1,1,0), (18,1,1,1), (18,2,0,0), (18,2,1,0), (18,2,1,1), (17,5,4,1),
  (18,2,2,0), (18,3,0,0), (18,3,1,0), (18,3,1,1), (18,2,2,2), (18,3,2,0), (18,3,2,1), (17,5,5,0),
  (18,4,0,0), (18,4,1,0), (18,4,1,1), (18,3,3,1), (18,4,2,0), (18,4,2,1), (18,3,3,2), (16,9,3,1),
  (18,4,2,2), (18,5,0,0), (18,5,1,0), (18,5,1,1), (16,8,4,4), (18,5,2,0), (18,5,2,1), (17,8,1,1),
  (18,4,4,0), (18,5,2,2), (18,5,3,0), (18,5,3,1), (18,6,0,0), (19,0,0,0), (19,1,0,0), (19,1,1,0),
  (19,1,1,1), (19,2,0,0), (19,2,1,0), (19,2,1,1), (18,6,2,2), (19,2,2,0), (19,3,0,0), (19,3,1,0),
  (19,3,1,1), (19,2,2,2), (19,3,2,0), (19,3,2,1), (18,6,4,0), (19,4,0,0), (19,4,1,0), (19,4,1,1),
  (19,3,3,1), (19,4,2,0), (19,4,2,1), (19,3,3,2), (16,8,8,0), (19,4,2,2), (19,5,0,0), (19,5,1,0),
  (19,5,1,1), (18,8,1,0), (19,5,2,0), (19,5,2,1), (18,8,2,0), (19,4,4,0), (19,5,2,2), (19,5,3,0),
  (19,5,3,1), (19,6,0,0), (19,6,1,0), (19,6,1,1)
]

private def wBlock4 : List (ℕ × ℕ × ℕ × ℕ) := [
  (20,0,0,0), (20,1,0,0), (20,1,1,0), (20,1,1,1), (20,2,0,0), (20,2,1,0), (20,2,1,1), (19,6,3,1),
  (20,2,2,0), (20,3,0,0), (20,3,1,0), (20,3,1,1), (20,2,2,2), (20,3,2,0), (20,3,2,1), (19,6,3,3),
  (20,4,0,0), (20,4,1,0), (20,4,1,1), (20,3,3,1), (20,4,2,0), (20,4,2,1), (20,3,3,2), (19,6,5,1),
  (20,4,2,2), (20,5,0,0), (20,5,1,0), (20,5,1,1), (18,10,2,0), (20,5,2,0), (20,5,2,1), (19,6,5,3),
  (20,4,4,0), (20,5,2,2), (20,5,3,0), (20,5,3,1), (20,6,0,0), (20,6,1,0), (20,6,1,1), (18,9,5,3),
  (20,6,2,0), (21,0,0,0), (21,1,0,0), (21,1,1,0), (21,1,1,1), (21,2,0,0), (21,2,1,0), (21,2,1,1),
  (20,4,4,4), (21,2,2,0), (21,3,0,0), (21,3,1,0), (21,3,1,1), (21,2,2,2), (21,3,2,0), (21,3,2,1),
  (20,6,4,2), (21,4,0,0), (21,4,1,0), (21,4,1,1), (21,3,3,1), (21,4,2,0), (21,4,2,1), (21,3,3,2),
  (20,8,0,0), (21,4,2,2), (21,5,0,0), (21,5,1,0), (21,5,1,1), (20,8,2,1), (21,5,2,0), (21,5,2,1),
  (20,8,2,2), (21,4,4,0), (21,5,2,2), (21,5,3,0), (21,5,3,1), (21,6,0,0), (21,6,1,0), (21,6,1,1),
  (20,8,4,0), (21,6,2,0), (21,6,2,1), (21,5,4,1), (22,0,0,0), (22,1,0,0), (22,1,1,0), (22,1,1,1),
  (22,2,0,0), (22,2,1,0), (22,2,1,1), (21,5,5,0), (22,2,2,0), (22,3,0,0), (22,3,1,0), (22,3,1,1),
  (22,2,2,2), (22,3,2,0), (22,3,2,1), (20,9,3,3)
]

private def wBlock5 : List (ℕ × ℕ × ℕ × ℕ) := [
  (22,4,0,0), (22,4,1,0), (22,4,1,1), (22,3,3,1), (22,4,2,0), (22,4,2,1), (22,3,3,2), (21,8,1,1),
  (22,4,2,2), (22,5,0,0), (22,5,1,0), (22,5,1,1), (16,16,0,0), (22,5,2,0), (22,5,2,1), (21,8,3,1),
  (22,4,4,0), (22,5,2,2), (22,5,3,0), (22,5,3,1), (22,6,0,0), (22,6,1,0), (22,6,1,1), (21,9,1,0),
  (22,6,2,0), (22,6,2,1), (22,5,4,1), (22,5,3,3), (22,6,2,2), (23,0,0,0), (23,1,0,0), (23,1,1,0),
  (23,1,1,1), (23,2,0,0), (23,2,1,0), (23,2,1,1), (22,6,4,0), (23,2,2,0), (23,3,0,0), (23,3,1,0),
  (23,3,1,1), (23,2,2,2), (23,3,2,0), (23,3,2,1), (20,12,0,0), (23,4,0,0), (23,4,1,0), (23,4,1,1),
  (23,3,3,1), (23,4,2,0), (23,4,2,1), (23,3,3,2), (22,8,2,0), (23,4,2,2), (23,5,0,0), (23,5,1,0),
  (23,5,1,1), (22,8,3,0), (23,5,2,0), (23,5,2,1), (22,6,6,2), (23,4,4,0), (23,5,2,2), (23,5,3,0),
  (23,5,3,1), (23,6,0,0), (23,6,1,0), (23,6,1,1), (22,8,4,2), (23,6,2,0), (23,6,2,1), (23,5,4,1),
  (23,5,3,3), (23,6,2,2), (23,6,3,0), (23,6,3,1), (24,0,0,0), (24,1,0,0), (24,1,1,0), (24,1,1,1),
  (24,2,0,0), (24,2,1,0), (24,2,1,1), (23,6,3,3), (24,2,2,0), (24,3,0,0), (24,3,1,0), (24,3,1,1),
  (24,2,2,2), (24,3,2,0), (24,3,2,1), (23,6,5,1), (24,4,0,0), (24,4,1,0), (24,4,1,1), (24,3,3,1),
  (24,4,2,0), (24,4,2,1), (24,3,3,2), (23,6,5,3)
]

private def wBlock6 : List (ℕ × ℕ × ℕ × ℕ) := [
  (24,4,2,2), (24,5,0,0), (24,5,1,0), (24,5,1,1), (23,5,5,5), (24,5,2,0), (24,5,2,1), (22,11,1,1),
  (24,4,4,0), (24,5,2,2), (24,5,3,0), (24,5,3,1), (24,6,0,0), (24,6,1,0), (24,6,1,1), (23,9,2,1),
  (24,6,2,0), (24,6,2,1), (24,5,4,1), (24,5,3,3), (24,6,2,2), (24,6,3,0), (24,6,3,1), (23,9,3,2),
  (24,4,4,4), (25,0,0,0), (25,1,0,0), (25,1,1,0), (25,1,1,1), (25,2,0,0), (25,2,1,0), (25,2,1,1),
  (24,6,4,2), (25,2,2,0), (25,3,0,0), (25,3,1,0), (25,3,1,1), (25,2,2,2), (25,3,2,0), (25,3,2,1),
  (24,8,0,0), (25,4,0,0), (25,4,1,0), (25,4,1,1), (25,3,3,1), (25,4,2,0), (25,4,2,1), (25,3,3,2),
  (24,8,2,2), (25,4,2,2), (25,5,0,0), (25,5,1,0), (25,5,1,1), (24,8,3,2), (25,5,2,0), (25,5,2,1),
  (24,8,4,0), (25,4,4,0), (25,5,2,2), (25,5,3,0), (25,5,3,1), (25,6,0,0), (25,6,1,0), (25,6,1,1),
  (24,6,6,4), (25,6,2,0), (25,6,2,1), (25,5,4,1), (25,5,3,3), (25,6,2,2), (25,6,3,0), (25,6,3,1),
  (24,8,4,4), (25,4,4,4), (25,6,3,2), (25,5,5,0), (26,0,0,0), (26,1,0,0), (26,1,1,0), (26,1,1,1),
  (26,2,0,0), (26,2,1,0), (26,2,1,1), (24,9,5,1), (26,2,2,0), (26,3,0,0), (26,3,1,0), (26,3,1,1),
  (26,2,2,2), (26,3,2,0), (26,3,2,1), (25,8,1,1), (26,4,0,0), (26,4,1,0), (26,4,1,1), (26,3,3,1),
  (26,4,2,0), (26,4,2,1), (26,3,3,2), (25,8,3,1)
]

private def wBlock7 : List (ℕ × ℕ × ℕ × ℕ) := [
  (26,4,2,2), (26,5,0,0), (26,5,1,0), (26,5,1,1), (24,8,8,0), (26,5,2,0), (26,5,2,1), (25,9,1,0),
  (26,4,4,0), (26,5,2,2), (26,5,3,0), (26,5,3,1), (26,6,0,0), (26,6,1,0), (26,6,1,1), (25,9,3,0),
  (26,6,2,0), (26,6,2,1), (26,5,4,1), (26,5,3,3), (26,6,2,2), (26,6,3,0), (26,6,3,1), (25,9,4,1),
  (26,4,4,4), (26,6,3,2), (26,5,5,0), (26,5,5,1), (26,6,4,0), (27,0,0,0), (27,1,0,0), (27,1,1,0),
  (27,1,1,1), (27,2,0,0), (27,2,1,0), (27,2,1,1), (24,12,4,0), (27,2,2,0), (27,3,0,0), (27,3,1,0),
  (27,3,1,1), (27,2,2,2), (27,3,2,0), (27,3,2,1), (26,8,2,0), (27,4,0,0), (27,4,1,0), (27,4,1,1),
  (27,3,3,1), (27,4,2,0), (27,4,2,1), (27,3,3,2), (26,6,6,2), (27,4,2,2), (27,5,0,0), (27,5,1,0),
  (27,5,1,1), (26,9,0,0), (27,5,2,0), (27,5,2,1), (26,8,4,2), (27,4,4,0), (27,5,2,2), (27,5,3,0),
  (27,5,3,1), (27,6,0,0), (27,6,1,0), (27,6,1,1), (24,8,8,8), (27,6,2,0), (27,6,2,1), (27,5,4,1),
  (27,5,3,3), (27,6,2,2), (27,6,3,0), (27,6,3,1), (26,10,0,0), (27,4,4,4), (27,6,3,2), (27,5,5,0),
  (27,5,5,1), (27,6,4,0), (27,6,4,1), (27,6,3,3), (28,0,0,0), (28,1,0,0), (28,1,1,0), (28,1,1,1),
  (28,2,0,0), (28,2,1,0), (28,2,1,1), (27,6,5,1), (28,2,2,0), (28,3,0,0), (28,3,1,0), (28,3,1,1),
  (28,2,2,2), (28,3,2,0), (28,3,2,1), (27,6,5,3)
]

private def wBlock8 : List (ℕ × ℕ × ℕ × ℕ) := [
  (28,4,0,0), (28,4,1,0), (28,4,1,1), (28,3,3,1), (28,4,2,0), (28,4,2,1), (28,3,3,2), (26,11,3,1),
  (28,4,2,2), (28,5,0,0), (28,5,1,0), (28,5,1,1), (27,9,1,1), (28,5,2,0), (28,5,2,1), (27,9,2,1),
  (28,4,4,0), (28,5,2,2), (28,5,3,0), (28,5,3,1), (28,6,0,0), (28,6,1,0), (28,6,1,1), (27,9,3,2),
  (28,6,2,0), (28,6,2,1), (28,5,4,1), (28,5,3,3), (28,6,2,2), (28,6,3,0), (28,6,3,1), (27,10,1,1),
  (28,4,4,4), (28,6,3,2), (28,5,5,0), (28,5,5,1), (28,6,4,0), (28,6,4,1), (28,6,3,3), (27,10,3,1),
  (28,6,4,2), (29,0,0,0), (29,1,0,0), (29,1,1,0), (29,1,1,1), (29,2,0,0), (29,2,1,0), (29,2,1,1),
  (28,8,0,0), (29,2,2,0), (29,3,0,0), (29,3,1,0), (29,3,1,1), (29,2,2,2), (29,3,2,0), (29,3,2,1),
  (28,8,2,2), (29,4,0,0), (29,4,1,0), (29,4,1,1), (29,3,3,1), (29,4,2,0), (29,4,2,1), (29,3,3,2),
  (28,8,4,0), (29,4,2,2), (29,5,0,0), (29,5,1,0), (29,5,1,1), (28,9,2,0), (29,5,2,0), (29,5,2,1),
  (28,6,6,4), (29,4,4,0), (29,5,2,2), (29,5,3,0), (29,5,3,1), (29,6,0,0), (29,6,1,0), (29,6,1,1),
  (28,8,4,4), (29,6,2,0), (29,6,2,1), (29,5,4,1), (29,5,3,3), (29,6,2,2), (29,6,3,0), (29,6,3,1),
  (28,10,2,0), (29,4,4,4), (29,6,3,2), (29,5,5,0), (29,5,5,1), (29,6,4,0), (29,6,4,1), (29,6,3,3),
  (24,16,8,0), (29,6,4,2), (29,5,4,4), (28,9,5,3)
]

private def wBlock9 : List (ℕ × ℕ × ℕ × ℕ) := [
  (30,0,0,0), (30,1,0,0), (30,1,1,0), (30,1,1,1), (30,2,0,0), (30,2,1,0), (30,2,1,1), (29,8,1,1),
  (30,2,2,0), (30,3,0,0), (30,3,1,0), (30,3,1,1), (30,2,2,2), (30,3,2,0), (30,3,2,1), (29,8,3,1),
  (30,4,0,0), (30,4,1,0), (30,4,1,1), (30,3,3,1), (30,4,2,0), (30,4,2,1), (30,3,3,2), (29,9,1,0),
  (30,4,2,2), (30,5,0,0), (30,5,1,0), (30,5,1,1), (28,12,0,0), (30,5,2,0), (30,5,2,1), (29,9,3,0),
  (30,4,4,0), (30,5,2,2), (30,5,3,0), (30,5,3,1), (30,6,0,0), (30,6,1,0), (30,6,1,1), (29,9,4,1),
  (30,6,2,0), (30,6,2,1), (30,5,4,1), (30,5,3,3), (30,6,2,2), (30,6,3,0), (30,6,3,1), (29,9,5,0),
  (30,4,4,4), (30,6,3,2), (30,5,5,0), (30,5,5,1), (30,6,4,0), (30,6,4,1), (30,6,3,3), (29,8,5,5),
  (30,6,4,2), (30,5,4,4), (29,10,4,1), (30,5,5,3), (28,12,4,4), (31,0,0,0), (31,1,0,0), (31,1,1,0),
  (31,1,1,1), (31,2,0,0), (31,2,1,0), (31,2,1,1), (30,8,2,0), (31,2,2,0), (31,3,0,0), (31,3,1,0),
  (31,3,1,1), (31,2,2,2), (31,3,2,0), (31,3,2,1), (30,6,6,2), (31,4,0,0), (31,4,1,0), (31,4,1,1),
  (31,3,3,1), (31,4,2,0), (31,4,2,1), (31,3,3,2), (30,8,4,2), (31,4,2,2), (31,5,0,0), (31,5,1,0),
  (31,5,1,1), (30,9,2,2), (31,5,2,0), (31,5,2,1), (28,12,8,0), (31,4,4,0), (31,5,2,2), (31,5,3,0),
  (31,5,3,1), (31,6,0,0), (31,6,1,0), (31,6,1,1)
]

private def wBlock10 : List (ℕ × ℕ × ℕ × ℕ) := [
  (30,10,0,0), (31,6,2,0), (31,6,2,1), (31,5,4,1), (31,5,3,3), (31,6,2,2), (31,6,3,0), (31,6,3,1),
  (30,10,2,2), (31,4,4,4), (31,6,3,2), (31,5,5,0), (31,5,5,1), (31,6,4,0), (31,6,4,1), (31,6,3,3),
  (30,10,4,0), (31,6,4,2), (31,5,4,4), (29,13,3,0), (31,5,5,3), (30,11,0,0), (31,6,5,0), (31,6,5,1),
  (32,0,0,0), (32,1,0,0), (32,1,1,0), (32,1,1,1), (32,2,0,0), (32,2,1,0), (32,2,1,1), (31,6,5,3),
  (32,2,2,0), (32,3,0,0), (32,3,1,0), (32,3,1,1), (32,2,2,2), (32,3,2,0), (32,3,2,1), (30,11,3,3),
  (32,4,0,0), (32,4,1,0), (32,4,1,1), (32,3,3,1), (32,4,2,0), (32,4,2,1), (32,3,3,2), (31,9,2,1),
  (32,4,2,2), (32,5,0,0), (32,5,1,0), (32,5,1,1), (31,9,3,1), (32,5,2,0), (32,5,2,1), (31,9,3,2),
  (32,4,4,0), (32,5,2,2), (32,5,3,0), (32,5,3,1), (32,6,0,0), (32,6,1,0), (32,6,1,1), (31,10,1,1),
  (32,6,2,0), (32,6,2,1), (32,5,4,1), (32,5,3,3), (32,6,2,2), (32,6,3,0), (32,6,3,1), (31,10,3,1),
  (32,4,4,4), (32,6,3,2), (32,5,5,0), (32,5,5,1), (32,6,4,0), (32,6,4,1), (32,6,3,3), (31,10,3,3),
  (32,6,4,2), (32,5,4,4), (31,11,0,0), (32,5,5,3), (31,11,1,1), (32,6,5,0), (32,6,5,1), (31,11,2,1),
  (32,8,0,0), (33,0,0,0), (33,1,0,0), (33,1,1,0), (33,1,1,1), (33,2,0,0), (33,2,1,0), (33,2,1,1),
  (32,8,2,2), (33,2,2,0), (33,3,0,0), (33,3,1,0)
]

private def wBlock11 : List (ℕ × ℕ × ℕ × ℕ) := [
  (33,3,1,1), (33,2,2,2), (33,3,2,0), (33,3,2,1), (32,8,4,0), (33,4,0,0), (33,4,1,0), (33,4,1,1),
  (33,3,3,1), (33,4,2,0), (33,4,2,1), (33,3,3,2), (32,6,6,4), (33,4,2,2), (33,5,0,0), (33,5,1,0),
  (33,5,1,1), (32,8,5,2), (33,5,2,0), (33,5,2,1), (32,8,4,4), (33,4,4,0), (33,5,2,2), (33,5,3,0),
  (33,5,3,1), (33,6,0,0), (33,6,1,0), (33,6,1,1), (32,10,2,0), (33,6,2,0), (33,6,2,1), (33,5,4,1),
  (33,5,3,3), (33,6,2,2), (33,6,3,0), (33,6,3,1), (30,14,6,2), (33,4,4,4), (33,6,3,2), (33,5,5,0),
  (33,5,5,1), (33,6,4,0), (33,6,4,1), (33,6,3,3), (32,10,4,2), (33,6,4,2), (33,5,4,4), (32,11,1,1),
  (33,5,5,3), (32,11,2,0), (33,6,5,0), (33,6,5,1), (32,8,8,0), (33,8,0,0), (33,8,1,0), (33,8,1,1),
  (34,0,0,0), (34,1,0,0), (34,1,1,0), (34,1,1,1), (34,2,0,0), (34,2,1,0), (34,2,1,1), (33,8,3,1),
  (34,2,2,0), (34,3,0,0), (34,3,1,0), (34,3,1,1), (34,2,2,2), (34,3,2,0), (34,3,2,1), (33,9,1,0),
  (34,4,0,0), (34,4,1,0), (34,4,1,1), (34,3,3,1), (34,4,2,0), (34,4,2,1), (34,3,3,2), (33,9,3,0),
  (34,4,2,2), (34,5,0,0), (34,5,1,0), (34,5,1,1), (32,12,4,0), (34,5,2,0), (34,5,2,1), (33,9,4,1),
  (34,4,4,0), (34,5,2,2), (34,5,3,0), (34,5,3,1), (34,6,0,0), (34,6,1,0), (34,6,1,1), (33,9,5,0),
  (34,6,2,0), (34,6,2,1), (34,5,4,1), (34,5,3,3)
]

private def wBlock12 : List (ℕ × ℕ × ℕ × ℕ) := [
  (34,6,2,2), (34,6,3,0), (34,6,3,1), (33,8,5,5), (34,4,4,4), (34,6,3,2), (34,5,5,0), (34,5,5,1),
  (34,6,4,0), (34,6,4,1), (34,6,3,3), (33,11,1,0), (34,6,4,2), (34,5,4,4), (33,11,2,0), (34,5,5,3),
  (32,8,8,8), (34,6,5,0), (34,6,5,1), (33,11,3,0), (34,8,0,0), (34,8,1,0), (34,8,1,1), (33,11,3,2),
  (34,8,2,0), (35,0,0,0), (35,1,0,0), (35,1,1,0), (35,1,1,1), (35,2,0,0), (35,2,1,0), (35,2,1,1),
  (34,6,6,2), (35,2,2,0), (35,3,0,0), (35,3,1,0), (35,3,1,1), (35,2,2,2), (35,3,2,0), (35,3,2,1),
  (34,8,4,2), (35,4,0,0), (35,4,1,0), (35,4,1,1), (35,3,3,1), (35,4,2,0), (35,4,2,1), (35,3,3,2),
  (32,12,8,4), (35,4,2,2), (35,5,0,0), (35,5,1,0), (35,5,1,1), (34,9,4,0), (35,5,2,0), (35,5,2,1),
  (34,10,0,0), (35,4,4,0), (35,5,2,2), (35,5,3,0), (35,5,3,1), (35,6,0,0), (35,6,1,0), (35,6,1,1),
  (34,10,2,2), (35,6,2,0), (35,6,2,1), (35,5,4,1), (35,5,3,3), (35,6,2,2), (35,6,3,0), (35,6,3,1),
  (34,10,4,0), (35,4,4,4), (35,6,3,2), (35,5,5,0), (35,5,5,1), (35,6,4,0), (35,6,4,1), (35,6,3,3),
  (32,16,0,0), (35,6,4,2), (35,5,4,4), (33,13,5,0), (35,5,5,3), (34,11,2,2), (35,6,5,0), (35,6,5,1),
  (34,10,4,4), (35,8,0,0), (35,8,1,0), (35,8,1,1), (34,10,6,0), (35,8,2,0), (35,8,2,1), (35,6,5,3),
  (36,0,0,0), (36,1,0,0), (36,1,1,0), (36,1,1,1)
]

private def wBlock13 : List (ℕ × ℕ × ℕ × ℕ) := [
  (36,2,0,0), (36,2,1,0), (36,2,1,1), (34,11,5,1), (36,2,2,0), (36,3,0,0), (36,3,1,0), (36,3,1,1),
  (36,2,2,2), (36,3,2,0), (36,3,2,1), (35,9,2,1), (36,4,0,0), (36,4,1,0), (36,4,1,1), (36,3,3,1),
  (36,4,2,0), (36,4,2,1), (36,3,3,2), (35,9,3,2), (36,4,2,2), (36,5,0,0), (36,5,1,0), (36,5,1,1),
  (35,9,3,3), (36,5,2,0), (36,5,2,1), (35,10,1,1), (36,4,4,0), (36,5,2,2), (36,5,3,0), (36,5,3,1),
  (36,6,0,0), (36,6,1,0), (36,6,1,1), (35,10,3,1), (36,6,2,0), (36,6,2,1), (36,5,4,1), (36,5,3,3),
  (36,6,2,2), (36,6,3,0), (36,6,3,1), (35,10,3,3), (36,4,4,4), (36,6,3,2), (36,5,5,0), (36,5,5,1),
  (36,6,4,0), (36,6,4,1), (36,6,3,3), (35,11,2,1), (36,6,4,2), (36,5,4,4), (35,11,2,2), (36,5,5,3),
  (35,11,3,1), (36,6,5,0), (36,6,5,1), (35,11,3,2), (36,8,0,0), (36,8,1,0), (36,8,1,1), (35,11,4,1),
  (36,8,2,0), (36,8,2,1), (36,6,5,3), (35,9,6,5), (36,8,2,2), (37,0,0,0), (37,1,0,0), (37,1,1,0),
  (37,1,1,1), (37,2,0,0), (37,2,1,0), (37,2,1,1), (36,8,4,0), (37,2,2,0), (37,3,0,0), (37,3,1,0),
  (37,3,1,1), (37,2,2,2), (37,3,2,0), (37,3,2,1), (36,6,6,4), (37,4,0,0), (37,4,1,0), (37,4,1,1),
  (37,3,3,1), (37,4,2,0), (37,4,2,1), (37,3,3,2), (36,8,4,4), (37,4,2,2), (37,5,0,0), (37,5,1,0),
  (37,5,1,1), (36,10,1,0), (37,5,2,0), (37,5,2,1)
]

private def wBlock14 : List (ℕ × ℕ × ℕ × ℕ) := [
  (36,10,2,0), (37,4,4,0), (37,5,2,2), (37,5,3,0), (37,5,3,1), (37,6,0,0), (37,6,1,0), (37,6,1,1),
  (32,16,8,8), (37,6,2,0), (37,6,2,1), (37,5,4,1), (37,5,3,3), (37,6,2,2), (37,6,3,0), (37,6,3,1),
  (36,10,4,2), (37,4,4,4), (37,6,3,2), (37,5,5,0), (37,5,5,1), (37,6,4,0), (37,6,4,1), (37,6,3,3),
  (36,8,8,0), (37,6,4,2), (37,5,4,4), (36,11,3,1), (37,5,5,3), (36,9,6,4), (37,6,5,0), (37,6,5,1),
  (36,10,6,0), (37,8,0,0), (37,8,1,0), (37,8,1,1), (36,10,6,2), (37,8,2,0), (37,8,2,1), (37,6,5,3),
  (36,12,0,0), (37,8,2,2), (37,8,3,0), (37,8,3,1), (38,0,0,0), (38,1,0,0), (38,1,1,0), (38,1,1,1),
  (38,2,0,0), (38,2,1,0), (38,2,1,1), (37,9,1,0), (38,2,2,0), (38,3,0,0), (38,3,1,0), (38,3,1,1),
  (38,2,2,2), (38,3,2,0), (38,3,2,1), (37,9,3,0), (38,4,0,0), (38,4,1,0), (38,4,1,1), (38,3,3,1),
  (38,4,2,0), (38,4,2,1), (38,3,3,2), (37,9,4,1), (38,4,2,2), (38,5,0,0), (38,5,1,0), (38,5,1,1),
  (36,12,4,4), (38,5,2,0), (38,5,2,1), (37,9,5,0), (38,4,4,0), (38,5,2,2), (38,5,3,0), (38,5,3,1),
  (38,6,0,0), (38,6,1,0), (38,6,1,1), (37,8,5,5), (38,6,2,0), (38,6,2,1), (38,5,4,1), (38,5,3,3),
  (38,6,2,2), (38,6,3,0), (38,6,3,1), (37,11,1,0), (38,4,4,4), (38,6,3,2), (38,5,5,0), (38,5,5,1),
  (38,6,4,0), (38,6,4,1), (38,6,3,3), (37,11,3,0)
]

private def wBlock15 : List (ℕ × ℕ × ℕ × ℕ) := [
  (38,6,4,2), (38,5,4,4), (37,9,6,4), (38,5,5,3), (36,12,8,0), (38,6,5,0), (38,6,5,1), (37,11,4,1),
  (38,8,0,0), (38,8,1,0), (38,8,1,1), (37,9,6,5), (38,8,2,0), (38,8,2,1), (38,6,5,3), (37,12,1,1),
  (38,8,2,2), (38,8,3,0), (38,8,3,1), (38,5,5,5), (38,6,6,2), (39,0,0,0), (39,1,0,0), (39,1,1,0),
  (39,1,1,1), (39,2,0,0), (39,2,1,0), (39,2,1,1), (38,8,4,2), (39,2,2,0), (39,3,0,0), (39,3,1,0),
  (39,3,1,1), (39,2,2,2), (39,3,2,0), (39,3,2,1), (32,16,16,0), (39,4,0,0), (39,4,1,0), (39,4,1,1),
  (39,3,3,1), (39,4,2,0), (39,4,2,1), (39,3,3,2), (38,10,0,0), (39,4,2,2), (39,5,0,0), (39,5,1,0),
  (39,5,1,1), (38,10,2,1), (39,5,2,0), (39,5,2,1), (38,10,2,2), (39,4,4,0), (39,5,2,2), (39,5,3,0),
  (39,5,3,1), (39,6,0,0), (39,6,1,0), (39,6,1,1), (38,10,4,0), (39,6,2,0), (39,6,2,1), (39,5,4,1),
  (39,5,3,3), (39,6,2,2), (39,6,3,0), (39,6,3,1), (36,16,4,0), (39,4,4,4), (39,6,3,2), (39,5,5,0),
  (39,5,5,1), (39,6,4,0), (39,6,4,1), (39,6,3,3), (38,10,4,4), (39,6,4,2), (39,5,4,4), (37,13,5,4),
  (39,5,5,3), (38,11,4,0), (39,6,5,0), (39,6,5,1), (38,10,6,2), (39,8,0,0), (39,8,1,0), (39,8,1,1),
  (38,12,0,0), (39,8,2,0), (39,8,2,1), (39,6,5,3), (38,12,2,0), (39,8,2,2), (39,8,3,0), (39,8,3,1),
  (39,5,5,5), (39,6,6,2), (39,8,3,2), (38,11,5,3)
]

private def wBlock16 : List (ℕ × ℕ × ℕ × ℕ) := [
  (40,0,0,0), (40,1,0,0), (40,1,1,0), (40,1,1,1), (40,2,0,0), (40,2,1,0), (40,2,1,1), (39,9,2,1),
  (40,2,2,0), (40,3,0,0), (40,3,1,0), (40,3,1,1), (40,2,2,2), (40,3,2,0), (40,3,2,1), (39,9,3,2),
  (40,4,0,0), (40,4,1,0), (40,4,1,1), (40,3,3,1), (40,4,2,0), (40,4,2,1), (40,3,3,2), (39,10,1,1),
  (40,4,2,2), (40,5,0,0), (40,5,1,0), (40,5,1,1), (39,9,5,1), (40,5,2,0), (40,5,2,1), (39,10,3,1),
  (40,4,4,0), (40,5,2,2), (40,5,3,0), (40,5,3,1), (40,6,0,0), (40,6,1,0), (40,6,1,1), (39,10,3,3),
  (40,6,2,0)
]
private lemma hBlock0 : checkBlock 0 wBlock0 = true ∧ wBlock0.length = 100 := by decide +kernel
private lemma hBlock1 : checkBlock 100 wBlock1 = true ∧ wBlock1.length = 100 := by decide +kernel
private lemma hBlock2 : checkBlock 200 wBlock2 = true ∧ wBlock2.length = 100 := by decide +kernel
private lemma hBlock3 : checkBlock 300 wBlock3 = true ∧ wBlock3.length = 100 := by decide +kernel
private lemma hBlock4 : checkBlock 400 wBlock4 = true ∧ wBlock4.length = 100 := by decide +kernel
private lemma hBlock5 : checkBlock 500 wBlock5 = true ∧ wBlock5.length = 100 := by decide +kernel
private lemma hBlock6 : checkBlock 600 wBlock6 = true ∧ wBlock6.length = 100 := by decide +kernel
private lemma hBlock7 : checkBlock 700 wBlock7 = true ∧ wBlock7.length = 100 := by decide +kernel
private lemma hBlock8 : checkBlock 800 wBlock8 = true ∧ wBlock8.length = 100 := by decide +kernel
private lemma hBlock9 : checkBlock 900 wBlock9 = true ∧ wBlock9.length = 100 := by decide +kernel
private lemma hBlock10 : checkBlock 1000 wBlock10 = true ∧ wBlock10.length = 100 := by decide +kernel
private lemma hBlock11 : checkBlock 1100 wBlock11 = true ∧ wBlock11.length = 100 := by decide +kernel
private lemma hBlock12 : checkBlock 1200 wBlock12 = true ∧ wBlock12.length = 100 := by decide +kernel
private lemma hBlock13 : checkBlock 1300 wBlock13 = true ∧ wBlock13.length = 100 := by decide +kernel
private lemma hBlock14 : checkBlock 1400 wBlock14 = true ∧ wBlock14.length = 100 := by decide +kernel
private lemma hBlock15 : checkBlock 1500 wBlock15 = true ∧ wBlock15.length = 100 := by decide +kernel
private lemma hBlock16 : checkBlock 1600 wBlock16 = true ∧ wBlock16.length = 41 := by decide +kernel

private lemma four_squares_no7_le_1640 {n : ℕ} (hn : n ≤ 1640) :
    ∃ a b c d : ℕ, a ≠ 7 ∧ b ≠ 7 ∧ c ≠ 7 ∧ d ≠ 7 ∧ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n := by
  by_cases h0 : n < 100
  · exact exists_of_checkBlock hBlock0.1 (by omega) (by rw [hBlock0.2]; omega)
  by_cases h1 : n < 200
  · exact exists_of_checkBlock hBlock1.1 (by omega) (by rw [hBlock1.2]; omega)
  by_cases h2 : n < 300
  · exact exists_of_checkBlock hBlock2.1 (by omega) (by rw [hBlock2.2]; omega)
  by_cases h3 : n < 400
  · exact exists_of_checkBlock hBlock3.1 (by omega) (by rw [hBlock3.2]; omega)
  by_cases h4 : n < 500
  · exact exists_of_checkBlock hBlock4.1 (by omega) (by rw [hBlock4.2]; omega)
  by_cases h5 : n < 600
  · exact exists_of_checkBlock hBlock5.1 (by omega) (by rw [hBlock5.2]; omega)
  by_cases h6 : n < 700
  · exact exists_of_checkBlock hBlock6.1 (by omega) (by rw [hBlock6.2]; omega)
  by_cases h7 : n < 800
  · exact exists_of_checkBlock hBlock7.1 (by omega) (by rw [hBlock7.2]; omega)
  by_cases h8 : n < 900
  · exact exists_of_checkBlock hBlock8.1 (by omega) (by rw [hBlock8.2]; omega)
  by_cases h9 : n < 1000
  · exact exists_of_checkBlock hBlock9.1 (by omega) (by rw [hBlock9.2]; omega)
  by_cases h10 : n < 1100
  · exact exists_of_checkBlock hBlock10.1 (by omega) (by rw [hBlock10.2]; omega)
  by_cases h11 : n < 1200
  · exact exists_of_checkBlock hBlock11.1 (by omega) (by rw [hBlock11.2]; omega)
  by_cases h12 : n < 1300
  · exact exists_of_checkBlock hBlock12.1 (by omega) (by rw [hBlock12.2]; omega)
  by_cases h13 : n < 1400
  · exact exists_of_checkBlock hBlock13.1 (by omega) (by rw [hBlock13.2]; omega)
  by_cases h14 : n < 1500
  · exact exists_of_checkBlock hBlock14.1 (by omega) (by rw [hBlock14.2]; omega)
  by_cases h15 : n < 1600
  · exact exists_of_checkBlock hBlock15.1 (by omega) (by rw [hBlock15.2]; omega)
  exact exists_of_checkBlock hBlock16.1 (by omega) (by rw [hBlock16.2]; omega)

end OMA_A241898_C2

theorem OMA.solution : type_of% @OeisA241898.conjecture_2 := by
  intro n
  by_cases hle : n ≤ 1640
  · exact OMA_A241898_C2.four_squares_no7_le_1640 hle
  · have hgt : 1640 < n := by omega
    by_cases h4 : n % 4 = 0
    · exact OMA_A241898_C2.four_squares_no7_of_dvd4 h4
    · by_cases h2 : n % 4 = 2
      · exact OMA_A241898_C2.four_squares_no7_of_mod4_2 hgt h2
      · exact OMA_A241898_C2.four_squares_no7_of_odd hgt (by omega)

