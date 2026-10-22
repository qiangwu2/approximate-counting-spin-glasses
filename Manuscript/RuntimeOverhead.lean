import Manuscript.LogRuntime

/-! Polynomial implementation overhead preserves the common-exponent bound.
The operational refinements supply the first inequality; this module only
performs the real inequalities needed to assemble their final bounds. -/

noncomputable section
namespace Manuscript.RuntimeOverhead

theorem enlarge_exponent {K C n epsilon delta : ℝ}
    (hK : 0 ≤ K) (hKC : K ≤ C) (hn : 1 ≤ n)
    (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1) :
    K * n ^ K * epsilon ^ (-K) * delta ^ (-K) ≤
      C * n ^ C * epsilon ^ (-C) * delta ^ (-C) := by
  have hC : 0 ≤ C := hK.trans hKC
  have hnp := Real.rpow_le_rpow_of_exponent_le hn hKC
  have hep := Real.rpow_le_rpow_of_exponent_ge he he1 (neg_le_neg hKC)
  have hdp := Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hKC)
  apply mul_le_mul
  · apply mul_le_mul
    · exact mul_le_mul hKC hnp (by positivity) hC
    · exact hep
    · positivity
    · positivity
  · exact hdp
  · positivity
  · positivity

theorem polynomial_overhead {A K n epsilon delta work : ℝ} (d : ℕ)
    (hA : 0 ≤ A) (hK : 1 ≤ K) (hn : 1 ≤ n) (hw0 : 0 ≤ work)
    (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hw : work ≤ K * n ^ K * epsilon ^ (-K) * delta ^ (-K)) :
    A * (n + work + 1) ^ d ≤
      max 1 (max (A * (K + 2) ^ d) ((K + 1) * d)) *
      n ^ (max 1 (max (A * (K + 2) ^ d) ((K + 1) * d))) *
      epsilon ^ (-max 1 (max (A * (K + 2) ^ d) ((K + 1) * d))) *
      delta ^ (-max 1 (max (A * (K + 2) ^ d) ((K + 1) * d))) := by
  let C := max 1 (max (A * (K + 2) ^ d) ((K + 1) * d))
  have hK0 : 0 ≤ K := by linarith
  have hn0 : 0 < n := by linarith
  have hnPow : n ≤ n ^ K := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn hK
  have hePow : 1 ≤ epsilon ^ (-K) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos he he1 (by linarith)
  have hdPow : 1 ≤ delta ^ (-K) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (by linarith)
  let F := n ^ K * epsilon ^ (-K) * delta ^ (-K)
  have hF : n ≤ F := by
    dsimp [F]
    calc
      n ≤ n ^ K := hnPow
      _ ≤ n ^ K * epsilon ^ (-K) := le_mul_of_one_le_right (by positivity) hePow
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hdPow
  have hF0 : 0 ≤ F := by dsimp [F]; positivity
  have hbase : n + work + 1 ≤ (K + 2) * F := by
    have hw' : work ≤ K * F := by simpa [F, mul_assoc] using hw
    nlinarith
  have hbase0 : 0 ≤ n + work + 1 := by linarith
  have hpow := pow_le_pow_left₀ hbase0 hbase d
  have hcoef : A * (K + 2) ^ d ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC : 1 ≤ C := le_max_left _ _
  have hKd : K * d ≤ C := by
    have hh : (K + 1) * d ≤ C := (le_max_right _ _).trans (le_max_right _ _)
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    nlinarith
  have hnp := Real.rpow_le_rpow_of_exponent_le hn hKd
  have hep := Real.rpow_le_rpow_of_exponent_ge he he1 (neg_le_neg hKd)
  have hdp := Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hKd)
  calc
    A * (n + work + 1) ^ d ≤ A * ((K + 2) * F) ^ d := mul_le_mul_of_nonneg_left hpow hA
    _ = (A * (K + 2) ^ d) * n ^ (K * d) *
        epsilon ^ (-(K * d)) * delta ^ (-(K * d)) := by
      dsimp [F]
      simp only [mul_pow, Real.rpow_mul_natCast hn0.le,
        show -(K * (d : ℝ)) = (-K) * (d : ℝ) by ring,
        Real.rpow_mul_natCast he.le, Real.rpow_mul_natCast hd.le]
      ring
    _ ≤ C * n ^ C * epsilon ^ (-C) * delta ^ (-C) := by
      apply mul_le_mul
      · apply mul_le_mul
        · exact mul_le_mul hcoef hnp (by positivity) (by linarith)
        · exact hep
        · positivity
        · positivity
      · exact hdp
      · positivity
      · positivity

theorem preserves_polynomial (A K : ℝ) (d : ℕ) (hA : 0 ≤ A) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N oldCost steps : ℕ) (epsilon delta : ℝ),
      1 ≤ N → 0 < epsilon → epsilon ≤ 1 → 0 < delta → delta ≤ 1 →
      (oldCost : ℝ) ≤ K * (N : ℝ) ^ K * epsilon ^ (-K) * delta ^ (-K) →
      (steps : ℝ) ≤ A * ((N : ℝ) + oldCost + 1) ^ d →
      (steps : ℝ) ≤ C * (N : ℝ) ^ C * epsilon ^ (-C) * delta ^ (-C) := by
  let K' := max 1 K
  let C := max 1 (max (A * (K' + 2) ^ d) ((K' + 1) * d))
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro N oldCost steps epsilon delta hN he he1 hd hd1 hold hsteps
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hb := hold.trans (enlarge_exponent hK.le (le_max_right 1 K) hNR he he1 hd hd1)
  exact hsteps.trans (polynomial_overhead d hA (le_max_left 1 K) hNR
    (Nat.cast_nonneg oldCost) he he1 hd hd1 hb)

end Manuscript.RuntimeOverhead
