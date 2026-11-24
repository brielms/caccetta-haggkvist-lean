import LeanCH.BR.BRWeightedStrictPrime

/-! The actual one-sided quotient: every exterior parent of any member
is redirected to the representative, with no incoming-uniformity premise. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

open Classical in
noncomputable def outContract (D : CH.Digraph) (M : Finset ℕ) (r : ℕ) : CH.Digraph :=
  fun x y => if x=r then (if y=r then false else D r y)
    else if y=r then decide (∃ m∈M, D x m=true) else D x y

theorem representativeFiber_subset {V M : Finset ℕ} {r i : ℕ}
    (hMV : M ⊆ V) (hr : r∈M) (hi : i∈representativeSet V M r) :
    representativeFiber M r i ⊆ V := by
  intro x hx
  by_cases he : i=r
  · subst i
    exact hMV (by simpa [representativeFiber] using hx)
  · have hx' : x=i := by simpa [representativeFiber,he] using hx
    subst x
    exact representative_subset hMV hr hi

theorem outContract_edge_lift {D : CH.Digraph} {V M : Finset ℕ} {r a b x : ℕ}
    (hr : r∈M) (hout : OutUniform D V M)
    (hb : b∈representativeSet V M r)
    (hab : outContract D M r a b=true) (hx : x∈representativeFiber M r a) :
    ∃ y∈representativeFiber M r b, D x y=true := by
  classical
  by_cases har : a=r
  · subst a
    have hbr : b≠r := by intro he; simp [he,outContract] at hab
    have hxM : x∈M := by simpa [representativeFiber] using hx
    have hdb : D r b=true := by simpa [outContract,hbr] using hab
    refine ⟨b,by simp [representativeFiber,hbr],?_⟩
    rw [hout x hxM r hr b (representative_outside hb hbr).1 (representative_outside hb hbr).2]
    exact hdb
  · have hxa : x=a := by simpa [representativeFiber,har] using hx
    subst x
    by_cases hbr : b=r
    · subst b
      obtain ⟨y,hy,hdy⟩ : ∃ y∈M, D a y=true := by simpa [outContract,har] using hab
      exact ⟨y,by simpa [representativeFiber] using hy,hdy⟩
    · exact ⟨b,by simp [representativeFiber,hbr],by simpa [outContract,har,hbr] using hab⟩

/-- Every quotient walk lifts from any supplied vertex of its starting
fiber, preserving its exact length. The ending fiber is retained. -/
theorem outContract_walk_lift {D : CH.Digraph} {V M : Finset ℕ} {r a b l x : ℕ}
    (hMV : M ⊆ V) (hr : r∈M) (hout : OutUniform D V M)
    (p : Walk (outContract D M r) (representativeSet V M r) a b l)
    (hx : x∈representativeFiber M r a) :
    ∃ y∈representativeFiber M r b, Walk D V x y l := by
  induction p generalizing x with
  | refl a => exact ⟨x,hx,.refl x⟩
  | @step a b c l hb hab rest ih =>
    obtain ⟨y,hy,hxy⟩ := outContract_edge_lift hr hout hb hab hx
    obtain ⟨z,hz,wyz⟩ := ih hy
    exact ⟨z,hz,.step (representativeFiber_subset hMV hr hb hy) hxy wyz⟩

/-- A positive closed quotient walk lifts to a closed original walk of
exactly the same length, including when the quotient start is the root. -/
theorem outContract_closed_walk_lift {D : CH.Digraph} {V M : Finset ℕ} {r a l : ℕ}
    (hMV : M ⊆ V) (hr : r∈M) (hout : OutUniform D V M)
    (p : Walk (outContract D M r) (representativeSet V M r) a a l)
    (hl : 0<l) (ha : a∈representativeSet V M r) :
    ∃ x∈V, Walk D V x x l := by
  by_cases har : a=r
  · subst a
    cases p with
    | refl => omega
    | @step a b c k hb hab rest =>
      have hbr : b≠r := by intro he; simp [he,outContract] at hab
      obtain ⟨z,hz,wp⟩ := outContract_walk_lift hMV hr hout rest
        (by simp [representativeFiber,hbr] : b∈representativeFiber M r b)
      have hzM : z∈M := by simpa [representativeFiber] using hz
      have hdb : D r b=true := by simpa [outContract,hbr] using hab
      have hzb : D z b=true := by
        rw [hout z hzM r hr b (representative_outside hb hbr).1 (representative_outside hb hbr).2]
        exact hdb
      exact ⟨z,hMV hzM,.step (representative_subset hMV hr hb) hzb wp⟩
  · obtain ⟨y,hy,wp⟩ := outContract_walk_lift hMV hr hout p
      (by simp [representativeFiber,har] : a∈representativeFiber M r a)
    have hya : y=a := by simpa [representativeFiber,har] using hy
    subst y
    exact ⟨a,representative_subset hMV hr ha,wp⟩

theorem outContract_qfree {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ} {r : ℕ}
    (hf : QFree D V q) (hMV : M ⊆ V) (hr : r∈M) (hout : OutUniform D V M) :
    QFree (outContract D M r) (representativeSet V M r) q := by
  intro a l hl hq p
  have ha : a∈representativeSet V M r := by
    cases p with
    | refl => omega
    | @step a b c k hb hab rest =>
      exact rest.end_mem_or.elim (fun he => he.symm ▸ hb) id
  obtain ⟨x,_,wp⟩ := outContract_closed_walk_lift hMV hr hout p (by omega) ha
  exact hf x l hl hq wp

end LeanCH.BR.WeightedSD
