import FormalConjectures.ErdosProblems.«70»

/-!
Disproof of `Erdos70.erdos_70.variants.omega_one` in ZFC using Sierpiński's real-peak coloring
at `n = 4`.

Pick a bijection `φ : (𝔠).ord.ToType ≃ ℝ`, and color an unordered triple `{a, b, c}` (ordered
`a < b < c` in `(𝔠).ord.ToType`) blue iff `φ b` is the strict maximum (`φ a < φ b ∧ φ c < φ b`),
and red otherwise.
- No 4-element subset `{w < x < y < z}` is blue: blue on `{w, x, y}` gives `φ y < φ x`, while
  blue on `{x, y, z}` gives `φ x < φ y`.
- No subset of order type `ω₁` is red: if `φ` is not strictly decreasing on it, there exist
  `a < b` with `φ a < φ b`, forcing `φ` to be strictly increasing on the `ω₁`-tail above `b`.
  In either case we get a strictly monotone map `ω₁ → ℝ`, yielding `ω₁` disjoint nonempty open
  real intervals and contradicting countability of `ℚ`.
-/

namespace Erdos70OmegaOneDisproof

universe u

open Cardinal Ordinal
open scoped Cardinal

private noncomputable abbrev W1 : Ordinal.{u} := (Cardinal.aleph.{u} 1).ord
private noncomputable abbrev C0 : Cardinal.{u} := Cardinal.continuum.{u}

private lemma card_lt_aleph1_of_lt_W1 {o : Ordinal.{u}} (ho : o < W1.{u}) :
    o.card < Cardinal.aleph.{u} 1 :=
  Cardinal.lt_ord.mp ho

private lemma add_lt_W1 {a b : Ordinal.{u}} (ha : a < W1.{u}) (hb : b < W1.{u}) :
    a + b < W1.{u} := by
  rw [Cardinal.lt_ord, Ordinal.card_add]
  exact Cardinal.add_lt_of_lt (Cardinal.aleph0_le_aleph 1)
    (card_lt_aleph1_of_lt_W1 ha) (card_lt_aleph1_of_lt_W1 hb)

private lemma one_lt_W1 : (1 : Ordinal.{u}) < W1.{u} := by
  rw [Cardinal.lt_ord, Ordinal.card_one]
  exact lt_trans (Cardinal.natCast_lt_aleph0 (n := 1)) Cardinal.aleph0_lt_aleph_one

private lemma no_strictMono_W1 (g : W1.{u}.ToType → ℝ) (hg : StrictMono g) : False := by
  let next : W1.{u}.ToType → W1.{u}.ToType := fun x =>
    Ordinal.enum (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop)
      ⟨Ordinal.typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) x + 1, by
        rw [Ordinal.type_toType]
        exact add_lt_W1
          (by simpa [Ordinal.type_toType] using
            Ordinal.typein_lt_type (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) x)
          one_lt_W1⟩
  have htypein_next : ∀ x : W1.{u}.ToType,
      Ordinal.typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) (next x) =
        Ordinal.typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) x + 1 := fun x =>
    Ordinal.typein_enum (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) _
  have hlt_next : ∀ x : W1.{u}.ToType, x < next x := by
    intro x
    rw [← Ordinal.typein_lt_typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop)]
    change Ordinal.typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) x <
      Ordinal.typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) (next x)
    rw [htypein_next x, ← Order.succ_eq_add_one]
    exact Order.lt_succ (Ordinal.typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) x)
  have hnext_le : ∀ {x y : W1.{u}.ToType}, x < y → next x ≤ y := by
    intro x y hxy
    rw [← not_lt, ← Ordinal.typein_lt_typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop), not_lt]
    change Ordinal.typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) (next x) ≤
      Ordinal.typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) y
    rw [htypein_next x, ← Order.succ_eq_add_one]
    exact Order.succ_le_of_lt
      ((Ordinal.typein_lt_typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop)).mpr hxy)
  have hrat : ∀ x : W1.{u}.ToType, ∃ q : ℚ, g x < (q : ℝ) ∧ (q : ℝ) < g (next x) :=
    fun x => exists_rat_btwn (hg (hlt_next x))
  let q : W1.{u}.ToType → ℚ := fun x => (hrat x).choose
  have hq_spec : ∀ x : W1.{u}.ToType, g x < (q x : ℝ) ∧ (q x : ℝ) < g (next x) :=
    fun x => (hrat x).choose_spec
  have hq_inj : Function.Injective (fun x : W1.{u}.ToType => ULift.up.{u} (q x)) := by
    intro x y hxy'
    have hxy : q x = q y := congrArg ULift.down hxy'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : (q x : ℝ) < g (next x) := (hq_spec x).2
      have h2 : g (next x) ≤ g y := hg.monotone (hnext_le hlt)
      have h3 : g y < (q y : ℝ) := (hq_spec y).1
      rw [hxy] at h1
      linarith
    · have h1 : (q y : ℝ) < g (next y) := (hq_spec y).2
      have h2 : g (next y) ≤ g x := hg.monotone (hnext_le hgt)
      have h3 : g x < (q x : ℝ) := (hq_spec x).1
      rw [hxy] at h3
      linarith
  have hle : #(W1.{u}.ToType) ≤ Cardinal.aleph0.{u} :=
    (Cardinal.mk_le_of_injective hq_inj).trans Cardinal.mk_le_aleph0
  have hmkW1 : #(W1.{u}.ToType) = Cardinal.aleph.{u} 1 := by
    rw [Cardinal.mk_toType, Cardinal.card_ord]
  rw [hmkW1] at hle
  exact not_lt_of_ge hle Cardinal.aleph0_lt_aleph_one

private def isPeak (φ : C0.{u}.ord.ToType → ℝ) (a b c : C0.{u}.ord.ToType) : Prop :=
  a < b ∧ b < c ∧ φ a < φ b ∧ φ c < φ b

private def isBlue (φ : C0.{u}.ord.ToType → ℝ) (x y z : C0.{u}.ord.ToType) : Prop :=
  isPeak φ x y z ∨ isPeak φ x z y ∨ isPeak φ y x z ∨
  isPeak φ y z x ∨ isPeak φ z x y ∨ isPeak φ z y x

private def isRed (φ : C0.{u}.ord.ToType → ℝ) (x y z : C0.{u}.ord.ToType) : Prop :=
  ¬ isBlue φ x y z

private lemma isRed_symm (φ : C0.{u}.ord.ToType → ℝ) :
    ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (isRed φ x y z ↔ isRed φ y x z) ∧ (isRed φ x y z ↔ isRed φ x z y) := by
  intro x y z _ _ _
  unfold isRed isBlue
  tauto

private lemma isBlue_of_lt {φ : C0.{u}.ord.ToType → ℝ} {a b c : C0.{u}.ord.ToType}
    (hab : a < b) (hbc : b < c) :
    isBlue φ a b c ↔ φ a < φ b ∧ φ c < φ b := by
  unfold isBlue isPeak
  constructor
  · intro h
    rcases h with ⟨_, _, h1, h2⟩ | ⟨_, hcb, _, _⟩ | ⟨hba, _, _, _⟩ |
        ⟨_, hca, _, _⟩ | ⟨hca, _, _, _⟩ | ⟨hcb, _, _, _⟩
    · exact ⟨h1, h2⟩
    · exact absurd hbc (not_lt_of_gt hcb)
    · exact absurd hab (not_lt_of_gt hba)
    · exact absurd (lt_trans hab hbc) (not_lt_of_gt hca)
    · exact absurd (lt_trans hab hbc) (not_lt_of_gt hca)
    · exact absurd hbc (not_lt_of_gt hcb)
  · rintro ⟨h1, h2⟩
    exact Or.inl ⟨hab, hbc, h1, h2⟩

private lemma no_blue_four (φ : C0.{u}.ord.ToType ≃ ℝ) :
    ¬ ∃ s : Set C0.{u}.ord.ToType, #s = (4 : Cardinal.{u}) ∧
      s.Triplewise (fun x y z => ¬ isRed φ x y z) := by
  rintro ⟨s, hcard, hblue⟩
  have heq : #s = #(ULift.{u} (Fin 4)) := by simp [hcard]
  obtain ⟨e0⟩ := Cardinal.eq.mp heq
  let e : Fin 4 ≃ s := Equiv.ulift.symm.trans e0.symm
  let S : Finset C0.{u}.ord.ToType := Finset.univ.image (fun i : Fin 4 => (e i).val)
  have hScard : S.card = 4 := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro i j hij
      exact e.injective (Subtype.ext hij)
  let f : Fin 4 ↪o C0.{u}.ord.ToType := S.orderEmbOfFin hScard
  have hf_mem : ∀ i : Fin 4, f i ∈ s := by
    intro i
    have hmem : f i ∈ S := S.orderEmbOfFin_mem hScard i
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
    rw [← hj]
    exact (e j).property
  have h01 : f 0 < f 1 := f.strictMono (by decide)
  have h12 : f 1 < f 2 := f.strictMono (by decide)
  have h23 : f 2 < f 3 := f.strictMono (by decide)
  have hb1 : isBlue φ (f 0) (f 1) (f 2) := by
    have h := hblue (hf_mem 0) (hf_mem 1) (hf_mem 2)
      (ne_of_lt h01) (ne_of_lt h12) (ne_of_lt (lt_trans h01 h12))
    simpa [isRed] using h
  have hb2 : isBlue φ (f 1) (f 2) (f 3) := by
    have h := hblue (hf_mem 1) (hf_mem 2) (hf_mem 3)
      (ne_of_lt h12) (ne_of_lt h23) (ne_of_lt (lt_trans h12 h23))
    simpa [isRed] using h
  have h1 := (isBlue_of_lt h01 h12).mp hb1
  have h2 := (isBlue_of_lt h12 h23).mp hb2
  linarith

private lemma no_red_W1 (φ : C0.{u}.ord.ToType ≃ ℝ) :
    ¬ ∃ s : Set C0.{u}.ord.ToType, typeLT s = W1.{u} ∧ s.Triplewise (isRed φ) := by
  rintro ⟨s, htype, hred⟩
  have htype' : Ordinal.type (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) =
      Ordinal.type (· < · : s → s → Prop) := by
    rw [Ordinal.type_toType]
    exact htype.symm
  obtain ⟨e⟩ := Ordinal.type_eq.mp htype'
  let g : W1.{u}.ToType → ℝ := fun a => φ (e a).val
  have hg_inj : Function.Injective g :=
    φ.injective.comp (Subtype.val_injective.comp e.injective)
  have hno_peak : ∀ {a b c : W1.{u}.ToType}, a < b → b < c → ¬ (g a < g b ∧ g c < g b) := by
    intro a b c hab hbc
    have hab' : (e a).val < (e b).val := e.map_rel_iff.mpr hab
    have hbc' : (e b).val < (e c).val := e.map_rel_iff.mpr hbc
    have hr := hred (e a).property (e b).property (e c).property
      (ne_of_lt hab') (ne_of_lt hbc') (ne_of_lt (lt_trans hab' hbc'))
    exact fun hpk => hr ((isBlue_of_lt hab' hbc').mpr hpk)
  by_cases hdec : ∀ a b : W1.{u}.ToType, a < b → g b < g a
  · exact no_strictMono_W1 (fun x => -g x) (fun a b hab => neg_lt_neg (hdec a b hab))
  · push Not at hdec
    obtain ⟨a, b, hab, hge⟩ := hdec
    have hgab : g a < g b := lt_of_le_of_ne hge (fun h => ne_of_lt hab (hg_inj h))
    have hgt_b : ∀ c : W1.{u}.ToType, b < c → g b < g c := by
      intro c hbc
      have hnp := hno_peak hab hbc
      have hne : g c ≠ g b := fun h => ne_of_gt hbc (hg_inj h)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact absurd ⟨hgab, hlt⟩ hnp
      · exact hgt
    have htail_mono : ∀ c d : W1.{u}.ToType, b < c → c < d → g c < g d := by
      intro c d hbc hcd
      have hgbc := hgt_b c hbc
      have hnp := hno_peak hbc hcd
      have hne : g d ≠ g c := fun h => ne_of_gt hcd (hg_inj h)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact absurd ⟨hgbc, hlt⟩ hnp
      · exact hgt
    let β : Ordinal.{u} := Ordinal.typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) b
    have hβ : β < W1.{u} := by
      simpa [Ordinal.type_toType] using
        Ordinal.typein_lt_type (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) b
    let shift : W1.{u}.ToType → W1.{u}.ToType := fun x =>
      Ordinal.enum (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop)
        ⟨β + 1 + Ordinal.typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) x, by
          rw [Ordinal.type_toType]
          exact add_lt_W1 (add_lt_W1 hβ one_lt_W1)
            (by simpa [Ordinal.type_toType] using
              Ordinal.typein_lt_type (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) x)⟩
    have htypein_shift : ∀ x : W1.{u}.ToType,
        Ordinal.typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) (shift x) =
          β + 1 + Ordinal.typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) x := fun x =>
      Ordinal.typein_enum (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) _
    have hb_lt_shift : ∀ x : W1.{u}.ToType, b < shift x := by
      intro x
      rw [← Ordinal.typein_lt_typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop)]
      change β < Ordinal.typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) (shift x)
      rw [htypein_shift x]
      calc β < Order.succ β := Order.lt_succ β
        _ = β + 1 := Order.succ_eq_add_one β
        _ = β + 1 + 0 := (add_zero _).symm
        _ ≤ β + 1 + Ordinal.typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) x :=
            (add_le_add_iff_left (β + 1)).mpr zero_le
    have hshift_mono : StrictMono shift := by
      intro x y hxy
      rw [← Ordinal.typein_lt_typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop)]
      change Ordinal.typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) (shift x) <
        Ordinal.typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop) (shift y)
      rw [htypein_shift x, htypein_shift y]
      exact (add_lt_add_iff_left (β + 1)).mpr
        ((Ordinal.typein_lt_typein (· < · : W1.{u}.ToType → W1.{u}.ToType → Prop)).mpr hxy)
    exact no_strictMono_W1 (fun x => g (shift x))
      (fun x y hxy => htail_mono (shift x) (shift y) (hb_lt_shift x) (hshift_mono hxy))

end Erdos70OmegaOneDisproof

theorem OMA.disproof : ¬ (type_of% @Erdos70.erdos_70.variants.omega_one) := by
  intro hram
  have h4 := hram 4 (by decide)
  have hmk : Cardinal.mk (Erdos70OmegaOneDisproof.C0.ord.ToType) = Cardinal.mk (ULift ℝ) := by
    rw [Cardinal.mk_toType, Cardinal.card_ord, Cardinal.mk_uLift, Cardinal.mk_real]
    exact Cardinal.lift_continuum.symm
  obtain ⟨φ0⟩ := Cardinal.eq.mp hmk
  let φ := φ0.trans Equiv.ulift
  rcases h4 (Erdos70OmegaOneDisproof.isRed φ) (Erdos70OmegaOneDisproof.isRed_symm φ) with hred | hblue
  · exact Erdos70OmegaOneDisproof.no_red_W1 φ hred
  · exact Erdos70OmegaOneDisproof.no_blue_four φ hblue
