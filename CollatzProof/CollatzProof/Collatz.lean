import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import CollatzProof.OddTypes

namespace Collatz

/-- The forward Collatz step on natural numbers. -/
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

@[simp] lemma collatz_of_even {n : ℕ} (h : n % 2 = 0) :
    collatz n = n / 2 := by
  unfold collatz
  simp [h]

/-- Forward trajectory (orbit) of `n` under `collatz`.
`trajectory n t` is the value after `t` forward steps. -/
def trajectory (n : ℕ) : ℕ → ℕ
  | 0     => n
  | t+1   => collatz (trajectory n t)

@[simp] lemma trajectory_zero (n : ℕ) : trajectory n 0 = n := rfl
@[simp] lemma trajectory_succ (n t : ℕ) : trajectory n (t+1) = collatz (trajectory n t) := rfl

/-- A loop at `n` means `n` reappears after a positive number of forward steps. -/
def IsLoopAt (n : ℕ) : Prop := ∃ k > 0, trajectory n k = n

/-- Periodicity of the trajectory once a loop at `n` is found. -/
lemma loop_periodicity {n k : ℕ} (hloop : trajectory n k = n) :
    ∀ t, trajectory n (t + k) = trajectory n t := by
  intro t; induction t with
  | zero => simp [Nat.zero_add, hloop]
  | succ t ih =>
      simp [trajectory_succ, Nat.succ_add, ih]

/-- A `k`-cycle rooted at `m` (period `k>0`). -/
def IsCycle (m k : ℕ) : Prop := 0 < k ∧ trajectory m k = m

lemma IsCycle.isLoopAt {m k} (h : IsCycle m k) : IsLoopAt m :=
  ⟨k, h.1, h.2⟩

/-- Reachability-based loop notion: the orbit revisits a previous state. -/
def HasLoop (n : ℕ) : Prop := ∃ k > 0, ∃ t, trajectory n (t + k) = trajectory n t

lemma hasLoop_of_isLoopAt {n} (h : IsLoopAt n) : HasLoop n := by
  rcases h with ⟨k, hk, h⟩
  refine ⟨k, hk, 0, ?_⟩
  simp [trajectory_zero, h]

lemma trajectory_add (n t s : ℕ) :
    trajectory n (t + s) = trajectory (trajectory n t) s := by
  induction s with
  | zero => simp
  | succ s ih =>
      have hw : trajectory n (t + (s + 1)) = trajectory n ((t + s) + 1) := by
        simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      calc
        trajectory n (t + (s + 1))
            = trajectory n ((t + s) + 1) := hw
        _   = collatz (trajectory n (t + s)) := by
                simp [trajectory_succ]
        _   = collatz (trajectory (trajectory n t) s) := by
                rw [ih]

lemma hasLoop_of_reaches_cycle {n m k t : ℕ}
    (ht : trajectory n t = m) (hcyc : IsCycle m k) :
    HasLoop n := by
  refine ⟨k, hcyc.1, t, ?_⟩
  simpa [trajectory_add, ht, hcyc.2]

/-! The classical 1 → 4 → 2 → 1 cycle. -/
lemma collatz_one : collatz 1 = 4 := by simp [collatz]
lemma collatz_four : collatz 4 = 2 := by simp [collatz]
lemma collatz_two : collatz 2 = 1 := by simp [collatz]

lemma trajectory_1_3 : trajectory 1 3 = 1 := by
  simp [trajectory, collatz_one, collatz_four, collatz_two]

lemma loopAt_one : IsLoopAt 1 := by
  refine ⟨3, by decide, ?_⟩
  exact trajectory_1_3

@[simp] lemma collatz_of_odd {n : ℕ} (h : n % 2 = 1) :
    collatz n = 3 * n + 1 := by
  unfold collatz
  simp [h]

/-- A reverse Collatz step, restricted to positive naturals. The first branch is the
`x ↦ 2x`, the second corresponds to the usual reverse step `(x - 1)/3` when valid. -/
def collatzReverse (n : ℕ) : List ℕ :=
  if n = 0 then []
  else
    let evenChild := 2 * n
    let oddChild? :=
      if (n ≥ 1) ∧ ((n - 1) % 3 = 0) ∧ ((n - 1) / 3) % 2 = 1 then
        some ((n - 1) / 3)
      else none
    match oddChild? with
    | some m => [evenChild, m]
    | none => [evenChild]

/-- Convenience predicate describing when the reverse odd branch exists. -/
def ReverseOddBranch (n m : ℕ) : Prop :=
  m % 2 = 1 ∧ 3 * m + 1 = n

lemma reverseOddBranch_iff (n m : ℕ) :
    ReverseOddBranch n m ↔ (m % 2 = 1 ∧ 3 * m + 1 = n) := Iff.rfl

/-- Every solution to the reverse odd branch equation automatically produces an odd `m`. -/
lemma reverseOddBranch_odd {n m : ℕ} (h : ReverseOddBranch n m) :
    Odd m := by
  rcases h with ⟨hodd, _⟩
  exact Nat.odd_iff.mpr hodd

lemma reverseOddBranch_decompose {n m : ℕ} (h : ReverseOddBranch n m) :
    ∃ k, m = 2 * k + 1 ∧ n = 6 * k + 4 := by
  rcases h with ⟨hmOdd, hEq⟩
  obtain ⟨k, hk⟩ := reverseOddBranch_odd ⟨hmOdd, hEq⟩
  have hEq₁ : n = 3 * m + 1 := hEq.symm
  refine ⟨k, hk, ?_⟩
  calc
    n = 3 * m + 1 := hEq₁
    _ = 3 * (2 * k + 1) + 1 := by simp [hk]
    _ = 6 * k + 4 := by ring

lemma reverseOddBranch_even {n m : ℕ} (h : ReverseOddBranch n m) :
    Even n := by
  obtain ⟨k, _, hn⟩ := reverseOddBranch_decompose h
  refine ⟨3 * k + 2, ?_⟩
  have hEven : n = 2 * (3 * k + 2) := by
    calc
      n = 6 * k + 4 := hn
      _ = 2 * (3 * k + 2) := by ring
  have : n = (3 * k + 2) + (3 * k + 2) := by
    calc
      n = 2 * (3 * k + 2) := hEven
      _ = (3 * k + 2) + (3 * k + 2) := by
        simp [two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  exact this

lemma reverseOddBranch_mod_three {n m : ℕ} (h : ReverseOddBranch n m) :
    n % 3 = 1 := by
  rcases h with ⟨hmOdd, hEq⟩
  obtain ⟨k, hk⟩ := reverseOddBranch_odd ⟨hmOdd, hEq⟩
  have hEq' := hEq.symm
  simp [hk] at hEq'
  have hEq'' : n = 3 * (2 * k + 1) + 1 := hEq'
  simp [hEq'', Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

lemma reverseOddBranch_mod_six {n m : ℕ} (h : ReverseOddBranch n m) :
    n % 6 = 4 := by
  rcases h with ⟨hmOdd, hEq⟩
  obtain ⟨k, hk⟩ := reverseOddBranch_odd ⟨hmOdd, hEq⟩
  have hEq' : n = 6 * k + 4 := by
    calc
      n = 3 * m + 1 := hEq.symm
      _ = 3 * (2 * k + 1) + 1 := by simp [hk]
      _ = 6 * k + 4 := by ring
  simp [hEq', Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

lemma reverseOddBranch_exists_iff {n : ℕ} :
    (∃ m, ReverseOddBranch n m) ↔ n % 6 = 4 := by
  constructor
  · rintro ⟨m, h⟩
    exact reverseOddBranch_mod_six h
  · intro hmod
    have hn : n = 6 * (n / 6) + 4 := by
      calc
        n = n % 6 + 6 * (n / 6) := (Nat.mod_add_div n 6).symm
        _ = 4 + 6 * (n / 6) := by simp [hmod]
        _ = 6 * (n / 6) + 4 := by simp [Nat.add_comm]
    refine ⟨2 * (n / 6) + 1, ?_⟩
    constructor
    · simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    · have hcalc :
        3 * (2 * (n / 6) + 1) + 1 = 6 * (n / 6) + 4 := by ring
      exact hcalc.trans hn.symm

lemma collatzReverse_typeII {n : ℕ} (h : TypeII n) :
    collatzReverse n = [2 * n] := by
  obtain ⟨k, hk⟩ := (typeII_iff_exists _).1 h
  subst hk
  have h_ne : (6 * k + 3) ≠ 0 := by
    simp
  have hmod : ((6 * k + 3) - 1) % 3 ≠ 0 := by
    have hval : ((6 * k + 3) - 1) % 3 = 2 :=
      typeII_sub_one_mod_three (n := 6 * k + 3) h
    intro hzero
    exact Nat.succ_ne_zero (Nat.succ 0) ((Eq.symm hval).trans hzero)
  have hmod' := hmod
  simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] at hmod'
  have hoddBranch :
      ¬ ((1 ≤ 3 + k * 6) ∧ ((2 + k * 6) % 3 = 0) ∧ ((2 + k * 6) / 3) % 2 = 1) := by
    intro hcond
    exact hmod' hcond.2.1
  unfold collatzReverse
  simp [h_ne, hoddBranch, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

example : collatzReverse 10 = [20, 3] := by
  simp [collatzReverse]

example : ReverseOddBranch 10 3 := by
  simp [ReverseOddBranch]

example : 10 % 3 = 1 := by
  have h : ReverseOddBranch 10 3 := by
    simp [ReverseOddBranch]
  exact reverseOddBranch_mod_three (n := 10) (m := 3) h

example : 10 % 6 = 4 := by
  have h : ReverseOddBranch 10 3 := by
    simp [ReverseOddBranch]
  exact reverseOddBranch_mod_six (n := 10) (m := 3) h

example : ∃ m, ReverseOddBranch 10 m :=
  (reverseOddBranch_exists_iff (n := 10)).2 (by decide)

/-! Finite cycle container and minimal odd element -/

open Finset

/-- Values `trajectory m t` for `t = 0, …, k-1`, as a finite set. -/
def cycleFinset (m k : ℕ) : Finset ℕ := (Finset.range k).image (fun t => trajectory m t)

lemma mem_cycleFinset {x m k : ℕ} :
    x ∈ cycleFinset m k ↔ ∃ t, t < k ∧ trajectory m t = x := by
  classical
  unfold cycleFinset
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
    exact ⟨t, by simpa using ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact Finset.mem_image.mpr ⟨t, by simpa using ht, rfl⟩

/-- The odd elements among `cycleFinset`. -/
def oddCycleFinset (m k : ℕ) : Finset ℕ := (cycleFinset m k).filter (fun x => x % 2 = 1)

lemma collatz_zero : collatz 0 = 0 := by simp [collatz]

lemma trajectory_zero_all : ∀ s, trajectory 0 s = 0 := by
  intro s; induction s with
  | zero => rfl
  | succ s ih => simp [trajectory_succ, collatz_zero, ih]

lemma two_pow_pos (q : ℕ) : 0 < 2 ^ q := by
  induction q with
  | zero => decide
  | succ q ih =>
      have : 0 < (2 ^ q) * 2 := Nat.mul_pos ih (by decide)
      simpa [Nat.pow_succ, Nat.mul_comm] using this

lemma one_le_two_pow (q : ℕ) : 1 ≤ 2 ^ q := Nat.succ_le_of_lt (two_pow_pos q)

lemma one_lt_two_pow_of_pos {k : ℕ} (hk : 0 < k) : 1 < 2 ^ k := by
  classical
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have two_le : 2 ≤ 2 ^ (q + 1) := by
    have hle : 1 ≤ 2 ^ q := one_le_two_pow q
    have hle' : 2 * 1 ≤ 2 * (2 ^ q) := Nat.mul_le_mul_left 2 hle
    have : 2 ≤ 2 * (2 ^ q) := by simpa [Nat.one_mul] using hle'
    simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  exact lt_of_lt_of_le (by decide : 1 < 2) two_le

lemma trajectory_div_pow_two_of_all_even {m k : ℕ}
    (hAll : ∀ t < k, trajectory m t % 2 = 0) :
    trajectory m k = m / (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hkeven : trajectory m k % 2 = 0 := hAll k (Nat.lt_succ_self _)
      have hAll' : ∀ t < k, trajectory m t % 2 = 0 := by
        intro t ht; exact hAll t (lt_trans ht (Nat.lt_succ_self _))
      have ih' := ih hAll'
      have : trajectory m (k + 1) = (trajectory m k) / 2 := by
        simpa [trajectory_succ, collatz_of_even hkeven]
      simpa [ih', Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using this

lemma exists_odd_in_cycle {m k : ℕ}
    (hcyc : IsCycle m k) (hmpos : 0 < m) : ∃ t, t < k ∧ Odd (trajectory m t) := by
  classical
  have hkpos : 0 < k := hcyc.1
  by_contra hnone
  have hAllEven : ∀ t < k, trajectory m t % 2 = 0 := by
    intro t ht
    have hcases := Nat.mod_two_eq_zero_or_one (trajectory m t)
    cases hcases with
    | inl h0 => exact h0
    | inr h1 =>
        have : Odd (trajectory m t) := Nat.odd_iff.mpr h1
        exact (hnone ⟨t, ht, this⟩).elim
  have hdiv : trajectory m k = m / (2 ^ k) :=
    trajectory_div_pow_two_of_all_even hAllEven
  have heq : m / (2 ^ k) = m := by
    simpa [hdiv] using hcyc.2
  have hlt : m / (2 ^ k) < m := Nat.div_lt_self hmpos (one_lt_two_pow_of_pos hkpos)
  exact (ne_of_lt hlt) heq

lemma trajectory_ne_zero_of_cycle {m k t : ℕ}
    (hcyc : IsCycle m k) (hmpos : 0 < m) (hle : t ≤ k) : trajectory m t ≠ 0 := by
  classical
  intro h0
  have hadd : trajectory m k = trajectory m (t + (k - t)) := by
    have : t + (k - t) = k := Nat.add_sub_of_le hle
    simpa [this]
  have hcomp : trajectory m k = trajectory (trajectory m t) (k - t) := by
    simpa [trajectory_add] using hadd
  have hzero : trajectory m k = trajectory 0 (k - t) := by simpa [h0] using hcomp
  have hzero' : trajectory m k = 0 := by simpa [trajectory_zero_all] using hzero
  have hmzero : m = 0 := by simpa [hcyc.2] using hzero'
  exact (ne_of_gt hmpos) hmzero

def OddInCycle (m k x : ℕ) : Prop := ∃ t < k, trajectory m t = x ∧ x % 2 = 1

lemma oddCycleFinset_nonempty_of_exists {m k : ℕ}
    (hex : ∃ x, OddInCycle m k x) : (oddCycleFinset m k).Nonempty := by
  classical
  rcases hex with ⟨x, ⟨t, ht, rfl, hodd⟩⟩
  refine ⟨trajectory m t, ?_⟩
  have hin : trajectory m t ∈ cycleFinset m k := by
    exact (mem_cycleFinset.mpr ⟨t, ht, rfl⟩)
  simpa [oddCycleFinset, Finset.mem_filter, hin, hodd]

lemma exists_minOdd_in_cycle_of_exists {m k : ℕ}
    (hex : ∃ x, OddInCycle m k x) :
    ∃ x, OddInCycle m k x ∧
      ∀ y, OddInCycle m k y → x ≤ y := by
  classical
  have hne : (oddCycleFinset m k).Nonempty := oddCycleFinset_nonempty_of_exists hex
  let x := (oddCycleFinset m k).min' hne
  have hxmem : x ∈ oddCycleFinset m k := Finset.min'_mem _ _
  refine ⟨x, ?_, ?_⟩
  · rcases (Finset.mem_filter.mp hxmem) with ⟨hxIn, hodd⟩
    rcases (mem_cycleFinset.mp hxIn) with ⟨t, ht, htx⟩
    exact ⟨t, ht, htx, hodd⟩
  · intro y hy
    rcases hy with ⟨t, ht, htx, hodd⟩
    have hyodd : trajectory m t % 2 = 1 := by simpa [htx] using hodd
    have hymem : trajectory m t ∈ oddCycleFinset m k := by
      have hin : trajectory m t ∈ cycleFinset m k := (mem_cycleFinset.mpr ⟨t, ht, rfl⟩)
      simpa [oddCycleFinset, Finset.mem_filter, hin, hyodd]
    have hle : x ≤ trajectory m t := Finset.min'_le _ _ hymem
    simpa [htx] using hle

lemma exists_minOdd_in_cycle {m k : ℕ}
    (hcyc : IsCycle m k) (hmpos : 0 < m) :
    ∃ x, OddInCycle m k x ∧ ∀ y : ℕ, OddInCycle m k y → x ≤ y := by
  classical
  rcases exists_odd_in_cycle hcyc hmpos with ⟨t, ht, hott⟩
  have hex : ∃ x, OddInCycle m k x :=
    ⟨trajectory m t, ⟨t, ht, rfl, by simpa using (Nat.odd_iff.mp hott)⟩⟩
  exact exists_minOdd_in_cycle_of_exists hex

/-! Periodic rewrites and rotation invariance -/

lemma cycle_period_add_mul {m k : ℕ} (hcyc : IsCycle m k) :
    ∀ s t, trajectory m (t + s * k) = trajectory m t := by
  intro s; induction s with
  | zero => intro t; simp
  | succ s ih =>
      intro t
      have := loop_periodicity (n := m) (k := k) hcyc.2
      calc
        trajectory m (t + (Nat.succ s) * k)
            = trajectory m (t + s * k + k) := by
                simp [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        _   = trajectory m (t + s * k) := this _
        _   = trajectory m t := ih _

lemma trajectory_mod_period {m k t : ℕ} (hcyc : IsCycle m k) :
    trajectory m t = trajectory m (t % k) := by
  have h := cycle_period_add_mul (m := m) (k := k) hcyc (t / k) (t % k)
  have ht : t % k + (t / k) * k = t := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using (Nat.mod_add_div t k)
  simpa [ht] using h

lemma mem_cycleFinset_of_any_index {m k t : ℕ} (hcyc : IsCycle m k) :
    trajectory m t ∈ cycleFinset m k := by
  classical
  have hkpos : 0 < k := hcyc.1
  have hmodlt : t % k < k := Nat.mod_lt _ hkpos
  have : trajectory m t = trajectory m (t % k) := trajectory_mod_period (m := m) (k := k) (t := t) hcyc
  refine (mem_cycleFinset.mpr ?_)
  exact ⟨t % k, hmodlt, this.symm⟩

lemma cycle_image_collatz_eq {m k : ℕ} (hcyc : IsCycle m k) :
    (cycleFinset m k).image collatz = cycleFinset m k := by
  classical
  apply Finset.ext; intro y; constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rcases (mem_cycleFinset.mp hx) with ⟨t, ht, rfl⟩
    -- image element is `collatz (trajectory m t) = trajectory m (t+1)`
    have hmod : trajectory m (t + 1) = trajectory m ((t + 1) % k) :=
      trajectory_mod_period (m := m) (k := k) (t := t + 1) hcyc
    have hmod' : trajectory m ((t + 1) % k) = trajectory m (t + 1) := hmod.symm
    -- membership via the reduced index
    have hkpos : 0 < k := hcyc.1
    have hlt : (t + 1) % k < k := Nat.mod_lt _ hkpos
    exact (mem_cycleFinset.mpr ⟨(t + 1) % k, hlt, by simpa [trajectory_succ] using hmod'⟩)
  · intro hy
    rcases (mem_cycleFinset.mp hy) with ⟨t, ht, rfl⟩
    -- pick a preimage index s = t + k - 1
    let s := t + k - 1
    have hxmem : trajectory m s ∈ cycleFinset m k := mem_cycleFinset_of_any_index (m := m) (k := k) (t := s) hcyc
    have : collatz (trajectory m s) = trajectory m (s + 1) := by
      simp [trajectory_succ]
    -- show that `trajectory m (s+1) = trajectory m t`
    have hperiod : trajectory m (s + 1) = trajectory m t := by
      have hper := cycle_period_add_mul (m := m) (k := k) hcyc 1 t
      -- `s + 1 = t + k`
      have hkpos : 0 < k := hcyc.1
      have h1le : 1 ≤ t + k := by
        have : k ≤ t + k := Nat.le_add_left _ _
        exact le_trans (Nat.succ_le_of_lt hkpos) this
      have hs' : (t + k - 1) + 1 = t + k := Nat.sub_add_cancel h1le
      have hs : s + 1 = t + k := by
        change (t + k - 1 + 1) = t + k
        simpa using hs'
      simpa [hs, Nat.one_mul] using hper
    have hcoll : collatz (trajectory m s) = trajectory m t := by
      have hstep : collatz (trajectory m s) = trajectory m (s + 1) := by
        simp [trajectory_succ]
      exact hstep.trans hperiod
    exact Finset.mem_image.mpr ⟨trajectory m s, hxmem, hcoll⟩

section Cycle

variable {m k : ℕ} (hcyc : IsCycle m k)

@[simp] lemma trajectory_add_period (t : ℕ) :
    trajectory m (t + k) = trajectory m t :=
  (loop_periodicity (n := m) (k := k) hcyc.2) _

@[simp] lemma trajectory_add_mul_period (t s : ℕ) :
    trajectory m (t + s * k) = trajectory m t :=
  cycle_period_add_mul (m := m) (k := k) hcyc s t

@[simp] lemma trajectory_mod_period_simp (t : ℕ) :
    trajectory m t = trajectory m (t % k) :=
  trajectory_mod_period (m := m) (k := k) (t := t) hcyc

noncomputable def collatzOnCycle : ↥(cycleFinset m k) → ↥(cycleFinset m k) :=
  fun a => by
    classical
    refine ⟨collatz a.1, ?_⟩
    -- membership via rotation invariance
    have himg : collatz a.1 ∈ (cycleFinset m k).image collatz :=
      Finset.mem_image.mpr ⟨a.1, a.property, rfl⟩
    simpa [cycle_image_collatz_eq hcyc] using himg

lemma collatzOnCycle_apply {a : ↥(cycleFinset m k)} :
    (collatzOnCycle (m := m) (k := k) hcyc a).1 = collatz a.1 := rfl

lemma collatzOnCycle_surjective :
    Function.Surjective (collatzOnCycle (m := m) (k := k) hcyc) := by
  classical
  intro b
  -- since image(collatz) = cycle set, every element has a preimage in the set
  have hb' : b.1 ∈ (cycleFinset m k).image collatz := by
    simpa [cycle_image_collatz_eq hcyc] using b.property
  rcases Finset.mem_image.mp hb' with ⟨x, hx, hfx⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  ext; simpa [collatzOnCycle, hfx]

noncomputable def permOnCycle : Equiv.Perm (Subtype fun x => x ∈ cycleFinset m k) := by
  classical
  -- On a finite type, surjective ⇔ injective
  have hinj : Function.Injective (collatzOnCycle (m := m) (k := k) hcyc) :=
    (Finite.injective_iff_surjective (f := collatzOnCycle (m := m) (k := k) hcyc)).2
      (collatzOnCycle_surjective (m := m) (k := k) hcyc)
  exact Equiv.ofBijective (collatzOnCycle (m := m) (k := k) hcyc)
      ⟨hinj, collatzOnCycle_surjective (m := m) (k := k) hcyc⟩

@[simp] lemma permOnCycle_apply_val (a : Subtype fun x => x ∈ cycleFinset m k) :
    ((permOnCycle (m := m) (k := k) hcyc) a).1 = collatz a.1 := by
  simp [permOnCycle, collatzOnCycle_apply]

/-! Semiconjugacy with the (mod-`k`) successor on `Fin k`. -/

def rotate (m k : ℕ) (hcyc : IsCycle m k) (i : Fin k) : Fin k :=
  ⟨(i.val + 1) % k, by simpa using Nat.mod_lt _ hcyc.1⟩

def phi (m k : ℕ) (hcyc : IsCycle m k) (i : Fin k) :
    Subtype (fun x => x ∈ cycleFinset m k) :=
  ⟨trajectory m i.val, by
    exact (mem_cycleFinset.mpr ⟨i.val, by simpa using i.is_lt, rfl⟩)⟩

lemma semiconj_phi_rotate (i : Fin k) :
    collatzOnCycle (m := m) (k := k) hcyc (phi m k hcyc i)
      = phi m k hcyc (rotate m k hcyc i) := by
  apply Subtype.ext
  -- compare underlying values via `trajectory_mod_period`
  have hmod : trajectory m (i.val + 1) = trajectory m ((i.val + 1) % k) :=
    (trajectory_mod_period (m := m) (k := k) (t := i.val + 1) hcyc)
  have hstep : collatz (trajectory m i.val) = trajectory m (i.val + 1) := by
    simpa [trajectory_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using (trajectory_succ (n := m) (t := i.val)).symm
  simpa [phi, rotate, collatzOnCycle_apply]
    using hstep.trans hmod


/-! Rotation-by-one action and period-`k` property -/

-- Further work: show `(permOnCycle hcyc)` is conjugate to the rotation
-- `i ↦ i+1` on `Fin k` via the map `i ↦ ⟨trajectory m i, _⟩`, and deduce
-- `((permOnCycle hcyc) ^ k) = Equiv.refl _`.

end Cycle

/-! Minimal odd element constraints: type classification and reverse-branch facts -/

section MinOddConstraints

open Collatz

lemma reverseOddBranch_self_of_odd {x : ℕ} (hodd : x % 2 = 1) :
    ReverseOddBranch (3 * x + 1) x := by
  constructor
  · exact hodd
  · simp


lemma odd_in_cycle_type_partition {m k x : ℕ}
    (hodd : x % 2 = 1) (hx : x ∈ cycleFinset m k) :
    TypeI x ∨ TypeII x ∨ TypeIII x := by
  have : Odd x := Nat.odd_iff.mpr hodd
  simpa [TypeI, TypeII, TypeIII] using odd_partition (n := x) this

lemma minOdd_in_cycle_type_partition {m k : ℕ}
    (hcyc : IsCycle m k) (hmpos : 0 < m) :
    ∃ x, (OddInCycle m k x ∧ ∀ y, OddInCycle m k y → x ≤ y) ∧
      (TypeI x ∨ TypeII x ∨ TypeIII x) ∧ ((3 * x + 1) % 6 = 4) := by
  classical
  rcases exists_minOdd_in_cycle hcyc hmpos with ⟨x, hxmin, hmin⟩
  rcases hxmin with ⟨t, ht, htx, hoddx⟩
  have htype : TypeI x ∨ TypeII x ∨ TypeIII x := by
    have hxmem : x ∈ cycleFinset m k := (mem_cycleFinset.mpr ⟨t, ht, htx⟩)
    exact odd_in_cycle_type_partition (m := m) (k := k) (x := x) hoddx hxmem
  have hmod6 : (3 * x + 1) % 6 = 4 := by
    simpa using reverseOddBranch_mod_six (n := 3 * x + 1) (m := x)
      (h := reverseOddBranch_self_of_odd (x := x) hoddx)
  exact ⟨x, ⟨⟨t, ht, htx, hoddx⟩, hmin⟩, htype, hmod6⟩

end MinOddConstraints

end Collatz
