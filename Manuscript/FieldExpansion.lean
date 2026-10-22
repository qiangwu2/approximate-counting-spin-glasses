import SpinGlass.Partition

/-!
# The exact mixed-hypergraph expansion in a homogeneous external field

This file proves equation (14) from the exponential partition function, for
arbitrary finite indexed hyperedges and arbitrary real field and couplings.
No probabilistic or high-temperature hypothesis is used.
-/

noncomputable section
open scoped BigOperators

namespace Manuscript.FieldExpansion

open SpinGlass.Expansion

variable {V E : Type*} [Fintype V] [DecidableEq V]

def spinWeight (h : ℝ) (b : Bool) : ℝ :=
  Real.exp (h * spinSign b) / (2 * Real.cosh h)

theorem spinWeight_pos (h : ℝ) (b : Bool) : 0 < spinWeight h b :=
  div_pos (Real.exp_pos _) (mul_pos (by norm_num) (Real.cosh_pos _))

theorem sum_spinWeight_pow (h : ℝ) (n : ℕ) :
    (∑ b : Bool, spinWeight h b * spinSign b ^ n) =
      if Even n then 1 else Real.tanh h := by
  have hc : Real.cosh h ≠ 0 := ne_of_gt (Real.cosh_pos h)
  rcases Nat.even_or_odd n with hn | hn
  · simp [spinWeight, spinSign, hn, hn.neg_one_pow, Real.cosh_eq]
    field_simp
    ring
  · simp [spinWeight, spinSign, Nat.not_even_iff_odd.mpr hn,
      hn.neg_one_pow, Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    field_simp
    ring

@[simp] theorem sum_spinWeight (h : ℝ) : (∑ b : Bool, spinWeight h b) = 1 := by
  simpa using sum_spinWeight_pow h 0

def fieldMean (h : ℝ) (f : (V → Bool) → ℝ) : ℝ :=
  ∑ σ, (∏ v, spinWeight h (σ v)) * f σ

def boundary (incidence : E → Finset V) (Γ : Finset E) : Finset V :=
  Finset.univ.filter (fun v => ¬ Even (degree incidence Γ v))

def graphWeight (incidence : E → Finset V) (h : ℝ) (w : E → ℝ)
    (Γ : Finset E) : ℝ :=
  Real.tanh h ^ (boundary incidence Γ).card * ∏ e ∈ Γ, w e

theorem fieldMean_character (incidence : E → Finset V) (h : ℝ) (Γ : Finset E) :
    fieldMean h (fun σ : V → Bool => ∏ e ∈ Γ, edgeCharacter incidence σ e) =
      Real.tanh h ^ (boundary incidence Γ).card := by
  classical
  unfold fieldMean
  simp_rw [character_eq_degree, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun v (b : Bool) =>
    spinWeight h b * spinSign b ^ degree incidence Γ v)]
  simp_rw [sum_spinWeight_pow]
  have hf : (∏ v : V, if Even (degree incidence Γ v) then (1 : ℝ) else Real.tanh h) =
      ∏ v ∈ boundary incidence Γ, Real.tanh h := by
    rw [boundary, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro v hv
    split_ifs <;> rfl
  rw [hf]
  simp

@[simp] theorem fieldMean_one (h : ℝ) : fieldMean (V := V) h (fun _ => 1) = 1 := by
  unfold fieldMean
  simp only [mul_one]
  rw [← Fintype.prod_sum (fun (_ : V) (b : Bool) => spinWeight h b)]
  simp only [sum_spinWeight, Finset.prod_const_one]

theorem graphical_expansion (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (w : E → ℝ) :
    fieldMean h (fun σ : V → Bool =>
      ∏ e ∈ edges, (1 + w e * edgeCharacter incidence σ e)) =
      ∑ Γ ∈ edges.powerset, graphWeight incidence h w Γ := by
  classical
  unfold fieldMean
  simp_rw [Finset.prod_one_add, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  simp_rw [Finset.prod_mul_distrib]
  calc
    (∑ σ : V → Bool, (∏ v, spinWeight h (σ v)) *
        ((∏ e ∈ Γ, w e) * ∏ e ∈ Γ, edgeCharacter incidence σ e)) =
        (∏ e ∈ Γ, w e) * fieldMean h
          (fun σ : V → Bool => ∏ e ∈ Γ, edgeCharacter incidence σ e) := by
      rw [fieldMean, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      ring
    _ = graphWeight incidence h w Γ := by
      rw [fieldMean_character]
      exact mul_comm _ _

def partitionFunction (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (x : E → ℝ) : ℝ :=
  ∑ σ : V → Bool,
    Real.exp ((∑ e ∈ edges, x e * edgeCharacter incidence σ e) +
      h * ∑ v, spinSign (σ v))

def prefactor (edges : Finset E) (h : ℝ) (x : E → ℝ) : ℝ :=
  (2 * Real.cosh h) ^ Fintype.card V * ∏ e ∈ edges, Real.cosh (x e)

def normalizedPartition (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (x : E → ℝ) : ℝ :=
  partitionFunction incidence edges h x / prefactor (V := V) edges h x

omit [DecidableEq V] in
theorem prefactor_pos (edges : Finset E) (h : ℝ) (x : E → ℝ) :
    0 < prefactor (V := V) edges h x := by
  apply mul_pos
  · exact pow_pos (mul_pos (by norm_num) (Real.cosh_pos h)) _
  · exact Finset.prod_pos (fun e he => Real.cosh_pos _)

theorem partition_pos (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (x : E → ℝ) : 0 < partitionFunction incidence edges h x := by
  exact Finset.sum_pos (fun σ hσ => Real.exp_pos _) Finset.univ_nonempty

theorem normalizedPartition_pos (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (x : E → ℝ) : 0 < normalizedPartition incidence edges h x :=
  div_pos (partition_pos incidence edges h x) (prefactor_pos edges h x)

theorem partition_eq_prefactor_mul_fieldMean
    (incidence : E → Finset V) (edges : Finset E) (h : ℝ) (x : E → ℝ) :
    partitionFunction incidence edges h x = prefactor (V := V) edges h x *
      fieldMean h (fun σ : V → Bool =>
        ∏ e ∈ edges, (1 + Real.tanh (x e) * edgeCharacter incidence σ e)) := by
  classical
  unfold partitionFunction fieldMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Real.exp_add, Finset.mul_sum, Real.exp_sum, Real.exp_sum]
  have he : (∏ e ∈ edges, Real.exp (x e * edgeCharacter incidence σ e)) =
      (∏ e ∈ edges, Real.cosh (x e)) *
        ∏ e ∈ edges, (1 + Real.tanh (x e) * edgeCharacter incidence σ e) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro e he
    exact SpinGlass.Partition.exp_spin_factor (abs_edgeCharacter incidence σ e) (x e)
  rw [he]
  have hc : (2 * Real.cosh h) ^ Fintype.card V ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (by norm_num) (ne_of_gt (Real.cosh_pos h)))
  simp only [prefactor, spinWeight, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ]
  field_simp

theorem normalizedPartition_eq_graph_sum
    (incidence : E → Finset V) (edges : Finset E) (h : ℝ) (x : E → ℝ) :
    normalizedPartition incidence edges h x =
      ∑ Γ ∈ edges.powerset, graphWeight incidence h (fun e => Real.tanh (x e)) Γ := by
  unfold normalizedPartition
  rw [partition_eq_prefactor_mul_fieldMean, graphical_expansion]
  exact mul_div_cancel_left₀ _ (ne_of_gt (prefactor_pos edges h x))

theorem log_partition_decomposition
    (incidence : E → Finset V) (edges : Finset E) (h : ℝ) (x : E → ℝ) :
    Real.log (partitionFunction incidence edges h x) =
      Real.log (prefactor (V := V) edges h x) +
        Real.log (normalizedPartition incidence edges h x) := by
  rw [normalizedPartition, Real.log_div
    (ne_of_gt (partition_pos incidence edges h x)) (ne_of_gt (prefactor_pos edges h x))]
  ring

end Manuscript.FieldExpansion
