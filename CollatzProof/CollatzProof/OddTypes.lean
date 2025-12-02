import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases

namespace Collatz

/-- `TypeI n` means that `n` is congruent to `1` modulo `6`. -/
def TypeI (n : ℕ) : Prop :=
  n % 6 = 1

/-- `TypeII n` means that `n` is congruent to `3` modulo `6`. -/
def TypeII (n : ℕ) : Prop :=
  n % 6 = 3

/-- `TypeIII n` means that `n` is congruent to `5` modulo `6`. -/
def TypeIII (n : ℕ) : Prop :=
  n % 6 = 5

lemma typeI_iff_exists (n : ℕ) :
    TypeI n ↔ ∃ m : ℕ, n = 6 * m + 1 := by
  constructor
  · intro h
    refine ⟨n / 6, ?_⟩
    have hsplit := (Nat.mod_add_div n 6).symm
    have hmod : n % 6 = 1 := h
    have : n = 1 + 6 * (n / 6) := by
      simpa [hmod, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc, Nat.add_left_comm, Nat.add_assoc] using hsplit
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  · rintro ⟨m, rfl⟩
    simp [TypeI, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm]

lemma typeII_iff_exists (n : ℕ) :
    TypeII n ↔ ∃ m : ℕ, n = 6 * m + 3 := by
  constructor
  · intro h
    refine ⟨n / 6, ?_⟩
    have hsplit := (Nat.mod_add_div n 6).symm
    have hmod : n % 6 = 3 := h
    have : n = 3 + 6 * (n / 6) := by
      simpa [hmod, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc, Nat.add_left_comm, Nat.add_assoc] using hsplit
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  · rintro ⟨m, rfl⟩
    -- reduce the goal to a direct computation
    simp [TypeII, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm]

lemma typeIII_iff_exists (n : ℕ) :
    TypeIII n ↔ ∃ m : ℕ, n = 6 * m + 5 := by
  constructor
  · intro h
    refine ⟨n / 6, ?_⟩
    have hsplit := (Nat.mod_add_div n 6).symm
    have hmod : n % 6 = 5 := h
    have : n = 5 + 6 * (n / 6) := by
      simpa [hmod, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc, Nat.add_left_comm, Nat.add_assoc] using hsplit
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  · rintro ⟨m, rfl⟩
    simp [TypeIII, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm]

lemma odd_mod_six_cases {n : ℕ} (hodd : Odd n) :
    n % 6 = 1 ∨ n % 6 = 3 ∨ n % 6 = 5 := by
  classical
  have hmod₂ : n % 2 = 1 := (Nat.odd_iff.1 hodd)
  have hparity : (n % 6) % 2 = 1 := by
    have h := Nat.mod_mul_left_mod n 2 3
    simpa [Nat.mul_comm, hmod₂] using h
  have hlt : n % 6 < 6 := Nat.mod_lt _ (by decide : 0 < 6)
  set x : Fin 6 := ⟨n % 6, hlt⟩ with hxdef
  have hx_parity : x.val % 2 = 1 := by
    simpa [hxdef] using hparity
  have hcases :
      ∀ y : Fin 6, y.val % 2 = 1 → (y.val = 1 ∨ y.val = 3 ∨ y.val = 5) := by
    decide
  have hx_cases := hcases x hx_parity
  simpa [hxdef] using hx_cases

lemma odd_partition {n : ℕ} (hodd : Odd n) :
    TypeI n ∨ TypeII n ∨ TypeIII n := by
  have := odd_mod_six_cases hodd
  simpa [TypeI, TypeII, TypeIII] using this

lemma typeII_implies_three_dvd {n : ℕ} (h : TypeII n) :
    3 ∣ n := by
  rcases (typeII_iff_exists n).1 h with ⟨m, rfl⟩
  refine ⟨2 * m + 1, ?_⟩
  ring

lemma typeII_sub_one_mod_three {n : ℕ} (h : TypeII n) : (n - 1) % 3 = 2 := by
  rcases (typeII_iff_exists n).1 h with ⟨m, rfl⟩
  have hsub : 6 * m + 3 - 1 = 6 * m + 2 := by
    simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have hres : (6 * m + 2) % 3 = 2 := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using (Nat.add_mul_mod_self_left 2 3 (2 * m))
  simp [hsub, hres]

section TypeTransitions

lemma typeI_add_two {n : ℕ} (h : TypeI n) : TypeII (n + 2) := by
  unfold TypeI at h
  unfold TypeII
  have hmod' : (n + 2) % 6 = (n % 6 + 2) % 6 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.add_mod n 2 6
  simp [hmod', h, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

lemma typeII_add_two {n : ℕ} (h : TypeII n) : TypeIII (n + 2) := by
  unfold TypeII at h
  unfold TypeIII
  have hmod' : (n + 2) % 6 = (n % 6 + 2) % 6 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.add_mod n 2 6
  simp [hmod', h, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

lemma typeIII_add_two {n : ℕ} (h : TypeIII n) : TypeI (n + 2) := by
  unfold TypeIII at h
  unfold TypeI
  have hmod' : (n + 2) % 6 = (n % 6 + 2) % 6 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.add_mod n 2 6
  simp [hmod', h, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

lemma type_add_four_of_typeI {n : ℕ} (h : TypeI n) : TypeIII (n + 4) := by
  have := typeI_add_two (n := n) h
  have := typeII_add_two (n := n + 2) this
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

lemma type_add_four_of_typeII {n : ℕ} (h : TypeII n) : TypeI (n + 4) := by
  have := typeII_add_two (n := n) h
  have := typeIII_add_two (n := n + 2) this
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

lemma type_add_four_of_typeIII {n : ℕ} (h : TypeIII n) : TypeII (n + 4) := by
  have := typeIII_add_two (n := n) h
  have := typeI_add_two (n := n + 2) this
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

end TypeTransitions

end Collatz
