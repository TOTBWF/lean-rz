namespace Nat

-- FIXME: This probably exists somewhere?
theorem eq_zero_of_max_eq_zero {m n : Nat} (h : max m n = 0) : m = 0 ∧ n = 0 := by
  match m, n with
  | 0, 0 => exact ⟨ rfl, rfl ⟩
  | 0, n+1 => contradiction
  | m+1, 0 => contradiction
  | m+1, n+1 =>
    rw [Nat.succ_max_succ] at h
    contradiction
