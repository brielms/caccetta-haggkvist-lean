import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace LeanCH.BR.TripleBank

private theorem six_choose_three (n : ℕ) (hn : 2 ≤ n) :
    (6 : ℤ) * (n.choose 3 : ℤ) = (n : ℤ) * (n - 1 : ℤ) * (n - 2 : ℤ) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 3
  norm_num [Nat.descFactorial_succ, Nat.descFactorial_one, Nat.factorial] at h
  have hz := congrArg (fun a : ℕ => (a : ℤ)) h
  push_cast [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub hn] at hz
  calc
    _ = ((n : ℤ) - 2) * (((n : ℤ) - 1) * n) := hz.symm
    _ = _ := by ring

private theorem two_choose_two (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℤ) * (n.choose 2 : ℤ) = (n : ℤ) * (n - 1 : ℤ) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 2
  norm_num [Nat.descFactorial_succ, Nat.descFactorial_one, Nat.factorial] at h
  have hz := congrArg (fun a : ℕ => (a : ℤ)) h
  push_cast [Nat.cast_sub hn] at hz
  calc
    _ = ((n : ℤ) - 1) * n := hz.symm
    _ = _ := by ring

theorem moment_gap {l m : ℕ} (hm : 2 ≤ m) (hl : 3*m ≤ l) :
    m * l.choose 3 < l * ((m+1).choose 3 + (l-m).choose 3) + m * (l-m).choose 2 := by
  have hml : m ≤ l := by omega
  let u : ℤ := (m : ℤ) - 2
  let r : ℤ := (l : ℤ) - 3 * m
  have hu : 0 ≤ u := by dsimp [u]; exact sub_nonneg.mpr (by exact_mod_cast hm)
  have hr : 0 ≤ r := by dsimp [r]; apply sub_nonneg.mpr; exact_mod_cast hl
  have mu : (m : ℤ) = u + 2 := by dsimp [u]; ring
  have lr : (l : ℤ) = 3*(u+2)+r := by dsimp [u,r]; ring
  have h₁ := six_choose_three l (by omega)
  have h₂ := six_choose_three (m+1) (by omega)
  have h₃ := six_choose_three (l-m) (by omega)
  have h₄ := two_choose_two (l-m) (by omega)
  push_cast [Nat.cast_sub hml] at h₂ h₃ h₄
  have gap :
      0 < (l : ℤ) * (((m : ℤ)+1)*m*((m : ℤ)-1) +
        ((l : ℤ)-m)*((l : ℤ)-m-1)*((l : ℤ)-m-2)) +
        3*m*((l : ℤ)-m)*((l : ℤ)-m-1) -
        m*(l : ℤ)*((l : ℤ)-1)*((l : ℤ)-2) := by
    rw [lr, mu]
    have positive :
        0 < 12 + 24*u + 15*u^2 + 3*u^3 +
          (80 + 148*u + 90*u^2 + 18*u^3)*r +
          (56 + 69*u + 21*u^2)*r^2 + (13 + 8*u)*r^3 + r^4 := by positivity
    convert positive using 1
    ring
  have scaled :
      (6 : ℤ) * ((m : ℤ) * (l.choose 3 : ℤ)) <
        (6 : ℤ) * ((l : ℤ) * (((m+1).choose 3 : ℤ) + ((l-m).choose 3 : ℤ)) +
          (m : ℤ) * ((l-m).choose 2 : ℤ)) := by
    calc
      _ = (m : ℤ) * ((6 : ℤ) * (l.choose 3 : ℤ)) := by ring
      _ = _ := by rw [h₁]
      _ < (l : ℤ) * (((m : ℤ)+1)*m*((m : ℤ)-1) +
          ((l : ℤ)-m)*((l : ℤ)-m-1)*((l : ℤ)-m-2)) +
          3*m*((l : ℤ)-m)*((l : ℤ)-m-1) := by linarith only [gap]
      _ = (l : ℤ) * ((6 : ℤ) * ((m+1).choose 3 : ℤ) + (6 : ℤ) * ((l-m).choose 3 : ℤ)) +
          (3 : ℤ) * m * (2 * ((l-m).choose 2 : ℤ)) := by rw [h₂,h₃,h₄]; ring
      _ = _ := by ring
  exact_mod_cast (mul_lt_mul_iff_right₀ (show (0 : ℤ) < 6 by decide)).mp scaled

/-- The two column moments exclude a common-head set of size below four,
and bound the column height in terms of that set. -/
theorem moment_frontier {l m x y A B : ℕ}
    (hl : 7 ≤ l+1) (hm : 2 ≤ m) (mass : l*(l+1)+m ≤ x+y)
    (head : x ≤ l*(m+1)) (internal : 2*x ≤ l*(l-1))
    (cap : A+B ≤ m*l.choose 3)
    (inside : ∀ k : ℕ, l*k.choose 3+x*k.choose 2 ≤ A+l*(k*k.choose 2))
    (outside : ∀ k : ℕ, l*k.choose 3+y*k.choose 2 ≤ B+l*(k*k.choose 2)) :
    l+1 ≤ 3*m ∧ 4 ≤ m := by
  have height : l+1 ≤ 3*m := by
    by_contra! high
    let a := m+1
    let b := l-m
    have part : a+b = l+1 := by dsimp [a,b]; omega
    have ordered : a ≤ b := by dsimp [a,b]; omega
    have weights : a.choose 2 ≤ b.choose 2 := Nat.choose_le_choose 2 ordered
    have remain := Nat.sub_add_cancel weights
    have weightedHead := Nat.mul_le_mul_right (b.choose 2 - a.choose 2) head
    have weightedMass := Nat.mul_le_mul_right (b.choose 2) mass
    have f := inside a
    have g := outside b
    have step := moment_gap hm (by omega : 3*m ≤ l)
    have combine :
        l*(a.choose 3+b.choose 3)+m*b.choose 2 ≤ A+B := by
      change x * (b.choose 2 - a.choose 2) ≤ (l*a) * (b.choose 2 - a.choose 2) at weightedHead
      have weightedX : x*(b.choose 2-a.choose 2) + x*a.choose 2 = x*b.choose 2 := by
        rw [← Nat.mul_add, remain]
      have weightedA : (l*a)*(b.choose 2-a.choose 2) + (l*a)*a.choose 2 = (l*a)*b.choose 2 := by
        rw [← Nat.mul_add, remain]
      have split : l*(l+1) = l*a + l*b := by rw [← part, Nat.mul_add]
      rw [split] at weightedMass
      nlinarith only [f,g,weightedHead,weightedMass,weightedX,weightedA]
    change l*((m+1).choose 3+(l-m).choose 3)+m*(l-m).choose 2 ≤ A+B at combine
    exact (not_lt_of_ge (combine.trans cap)) step
  refine ⟨height, ?_⟩
  by_contra! small
  have m3 : m = 3 := by omega
  subst m
  have cases : l = 6 ∨ l = 7 ∨ l = 8 := by omega
  rcases cases with rfl | rfl | rfl
  · have f := inside 2
    have g := outside 5
    norm_num [Nat.choose] at f g cap internal mass
    omega
  · have f := inside 3
    have g := outside 5
    norm_num [Nat.choose] at f g cap internal mass
    omega
  · have f := inside 3
    have g := outside 5
    norm_num [Nat.choose] at f g cap internal mass
    omega

#print axioms moment_gap
#print axioms moment_frontier
end LeanCH.BR.TripleBank
