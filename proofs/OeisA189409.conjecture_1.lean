import FormalConjectures.OEIS.«189409»

/-!
Disproof of `OeisA189409.conjecture_1`:
At `n = 9`, `p_9# = 223092870` and `a(9) = 223092870^2 + 1 = 29^2 * 59180057841661`,
which is not squarefree.
-/

theorem OMA.disproof : ¬ (type_of% @OeisA189409.conjecture_1) := by
  intro h
  have hsq : Squarefree (OeisA189409.a 9) := h 9
  have hprim : Nat.kthPrimorial 9 = 223092870 := by
    simp only [Nat.kthPrimorial_succ, Nat.kthPrimorial_five,
      Nat.nth_prime_five_eq_thirteen, Nat.nth_prime_six_eq_seventeen,
      Nat.nth_prime_seven_eq_nineteen, Nat.nth_prime_eight_eq_twentyThree]
    norm_num
  have hdvd : 29 * 29 ∣ OeisA189409.a 9 := by
    refine ⟨59180057841661, ?_⟩
    rw [OeisA189409.a, hprim]
    norm_num
  have hu : IsUnit (29 : ℕ) := hsq 29 hdvd
  norm_num at hu
