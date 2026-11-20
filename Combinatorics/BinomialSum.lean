module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-!
# The sum of the binomial coefficients up to `k`

The standard estimate of a partial sum of a row of Pascal's triangle by the exponential:
`∑ i ≤ k, C(n, i) ≤ (e n / k) ^ k` for `0 < k ≤ n`. It follows from `C(n, i) ≤ n ^ i / i !`
(`Nat.choose_le_pow_div`) and the partial sums of the exponential series
(`Real.sum_le_exp_of_nonneg`), since `n / k ≥ 1` lets every power `n ^ i` with `i ≤ k` be
replaced by `n ^ k / k ^ (k - i)`.

## Main results

* `Nat.sum_range_succ_choose_le_exp_mul_div_pow` — the sum of the binomial coefficients `C(n, i)`
  for `i ≤ k` is at most `(e n / k) ^ k`, for `0 < k ≤ n`.
-/

@[expose] public section

/-- The sum of the binomial coefficients up to `k` is at most `(e n / k) ^ k`. -/
theorem Nat.sum_range_succ_choose_le_exp_mul_div_pow {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) ≤ (Real.exp 1 * n / k) ^ k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hr : (1 : ℝ) ≤ n / k := by rw [le_div_iff₀ hk']; linarith
  calc ∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)
      ≤ ∑ i ∈ Finset.range (k + 1), ((n : ℝ) / k) ^ k * ((k : ℝ) ^ i / (i.factorial : ℝ)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        calc (n.choose i : ℝ) ≤ (n : ℝ) ^ i / (i.factorial : ℝ) := Nat.choose_le_pow_div i n
          _ = ((n : ℝ) / k) ^ i * ((k : ℝ) ^ i / (i.factorial : ℝ)) := by
              rw [div_pow]; field_simp
          _ ≤ ((n : ℝ) / k) ^ k * ((k : ℝ) ^ i / (i.factorial : ℝ)) := by
              gcongr
    _ = ((n : ℝ) / k) ^ k * ∑ i ∈ Finset.range (k + 1), (k : ℝ) ^ i / (i.factorial : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ ((n : ℝ) / k) ^ k * Real.exp k :=
        mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hk'.le _) (by positivity)
    _ = (Real.exp 1 * n / k) ^ k := by
        have : Real.exp (k : ℝ) = Real.exp 1 ^ k := by
          rw [← Real.exp_nat_mul, mul_one]
        rw [this, ← mul_pow]
        congr 1
        ring
