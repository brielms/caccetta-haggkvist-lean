import checkpoints.shen_extension.CriticalReturnPool

namespace LeanCH.BR.WalkReturn
open Finset BRq2 BRq3 BR45
open scoped BigOperators

private abbrev bit (b : Bool) : ℕ := if b then 1 else 0
private abbrev o (D : CH.Digraph) (u v i : ℕ) := bit (D u i && D v i)
private abbrev r (D : CH.Digraph) (u w i : ℕ) := bit (D u i && D i w)
private abbrev e (D : CH.Digraph) (u v w i : ℕ) := bit (D u i && D w i && !D v i && !D i v)
private def f (D : CH.Digraph) (u v i : ℕ) := o D u v i + bit (D i v && !D u i)

def overlap (D : CH.Digraph) (U : Finset ℕ) (u v : ℕ) := ∑ i∈U, o D u v i
def middles (D : CH.Digraph) (U : Finset ℕ) (u w : ℕ) := ∑ i∈U, r D u w i
def witnesses (D : CH.Digraph) (U : Finset ℕ) (u v w : ℕ) := ∑ i∈U, e D u v w i
/-- On an arc the in-neighbour term includes the initial vertex.
This adds one to both potentials in the two-path difference. -/
def potential (D : CH.Digraph) (U : Finset ℕ) (u v : ℕ) := ∑ i∈U, f D u v i

private theorem table : ∀ a b c l k : Bool, ¬(b=true ∧ l=true) →
    ¬(c=true ∧ l=true) → ¬(c=true ∧ k=true) →
    bit a + bit b + bit c + (bit (a && b) + bit (l && !a)) + bit (a && k) ≤
      1+3*bit (a && b)+bit (a && c && !b && !l)+(bit (b && c)+bit (k && !b)) := by decide

private theorem point {D : CH.Digraph} {U : Finset ℕ} {u v w i : ℕ}
    (safe : QFree D U 3) (uu : u∈U) (vu : v∈U) (wu : w∈U) (iu : i∈U)
    (uv : D u v=true) (vw : D v w=true) :
    bit (D u i)+bit (D v i)+bit (D w i)+f D u v i+r D u w i+
      (if i=u then bit (D u w) else 0)+(if i=w then bit (D u w) else 0) ≤
    1+3*o D u v i+e D u v w i+f D v w i := by
  have rev : D w u=false := Bool.eq_false_iff.mpr (fun h => safe u 3 (by decide) (by decide)
    (.step vu uv (.step wu vw (.step uu h (.refl _)))))
  have neq : u≠w := fun h => digonfree safe (by decide) uu vu uv (h ▸ vw)
  have vu' := Bool.eq_false_iff.mpr (digonfree safe (by decide) uu vu uv)
  have wv' := Bool.eq_false_iff.mpr (digonfree safe (by decide) vu wu vw)
  by_cases a : i=u
  · subst i
    have loop := Bool.eq_false_iff.mpr (loopfree safe (by decide) uu)
    cases h : D u w <;> simp [o,r,e,f,bit,uv,vu',rev,loop,h,neq]
  by_cases b : i=w
  · subst i
    have loop := Bool.eq_false_iff.mpr (loopfree safe (by decide) wu)
    cases h : D u w <;> simp [o,r,e,f,bit,vw,wv',loop,h,neq.symm]
  simp only [ite_eq_right a,ite_eq_right b,Nat.add_zero]
  exact table _ _ _ _ _
    (fun h => digonfree safe (by decide) vu iu h.1 h.2)
    (fun h => safe v 3 (by decide) (by decide) (.step wu vw (.step iu h.1 (.step vu h.2 (.refl _)))))
    (fun h => digonfree safe (by decide) wu iu h.1 h.2)

private theorem degree_sum (D : CH.Digraph) (U : Finset ℕ) (u : ℕ) :
    (∑ i∈U, bit (D u i)) = (outN D U u).card := by
  simp only [bit,Finset.sum_boole,Nat.cast_id]
  congr 1

theorem two_path {D : CH.Digraph} {U : Finset ℕ} {u v w : ℕ}
    (safe : QFree D U 3) (uu : u∈U) (vu : v∈U) (wu : w∈U) (uv : D u v=true) (vw : D v w=true) :
    (outN D U u).card+(outN D U v).card+(outN D U w).card+
      potential D U u v+middles D U u w+2*(D u w).toNat ≤
      U.card+3*overlap D U u v+witnesses D U u v w+potential D U v w := by
  classical
  have bound := sum_le_sum (fun i (hi : i∈U) => point safe uu vu wu hi uv vw)
  simp only [sum_add_distrib, ←mul_sum, sum_const, smul_eq_mul, mul_one,
    degree_sum, sum_ite_eq', uu, wu, ite_true] at bound
  change _ + potential D U u v + middles D U u w + bit (D u w) + bit (D u w) ≤
    _ + 3*overlap D U u v + witnesses D U u v w + potential D U v w at bound
  have corr : bit (D u w)=(D u w).toNat := by cases D u w <;> rfl
  omega

/-- Summing over a permutation of positions includes closed walks with
repeated labels. Each orbit of the permutation is a closed walk. -/
theorem closed_walk {ι : Type*} [Fintype ι] (next : Equiv.Perm ι) (v : ι → ℕ)
    {D : CH.Digraph} {U : Finset ℕ} {s : ℕ} (safe : QFree D U 3)
    (live : ∀ i, v i∈U) (step : ∀ i, D (v i) (v (next i))=true)
    (floor : ∀ i,s≤(outN D U (v i)).card) :
    Fintype.card ι*(3*s) + (∑ i, middles D U (v i) (v (next (next i)))) +
      2* ∑ i, (D (v i) (v (next (next i)))).toNat ≤
    Fintype.card ι*U.card + 3* ∑ i, overlap D U (v i) (v (next i)) +
      ∑ i, witnesses D U (v i) (v (next i)) (v (next (next i))) := by
  classical
  let F (i : ι) := potential D U (v i) (v (next i))
  have shift : (∑ i, F (next i)) = ∑ i, F i := Equiv.sum_comp next F
  have localBound (i : ι) : 3*s + F i + middles D U (v i) (v (next (next i))) +
      2*(D (v i) (v (next (next i)))).toNat ≤
      U.card+3*overlap D U (v i) (v (next i))+
      witnesses D U (v i) (v (next i)) (v (next (next i)))+F (next i) := by
    have h := two_path safe (live i) (live (next i)) (live (next (next i))) (step i) (step (next i))
    have h₀ := floor i
    have h₁ := floor (next i)
    have h₂ := floor (next (next i))
    dsimp [F]
    omega
  have sum := sum_le_sum (fun i (_ : i∈(univ : Finset ι)) => localBound i)
  simp only [sum_add_distrib,←mul_sum,sum_const,card_univ,smul_eq_mul,shift] at sum
  rw [show Fintype.card ι*(3*s) = 3*(Fintype.card ι*s) by ring]
  omega

#print axioms two_path
#print axioms closed_walk
end LeanCH.BR.WalkReturn
