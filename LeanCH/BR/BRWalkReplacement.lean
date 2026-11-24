import LeanCH.BR.BRUnionCrossIncidence

/-! Short-walk replacement in a union. The comparison is only needed up to
the actual cutoff; an edge of the replacing graph preserves positive length. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem union_walk_prefix {R E : CH.Digraph} {V M : Finset ℕ} {q : ℕ}
    (hs : ∀ x∈V, ∀ y∈V, E x y=true → ¬R x y=true → x∈M ∧ y∈M)
    (hr : ∀ x∈M, ∀ y∈M, ∀ n, n≤q → Walk R V x y n →
      ∃ m, m≤n ∧ Walk E V x y m)
    {a b n : ℕ} (w : Walk (arcUnion R E) V a b n)
    (ha : a∈V) (hb : b∈M) (hn : n≤q) :
    ∃ x k l, x∈M ∧ Walk R V a x k ∧ Walk E V x b l ∧ k+l≤n := by
  induction w with
  | refl a => exact ⟨a,0,0,hb,.refl _,.refl _,by omega⟩
  | @step a c b n hc hac w ih =>
    obtain ⟨x,k,l,hx,wk,wl,hkl⟩ := ih hc hb (by omega)
    by_cases hR : R a c=true
    · exact ⟨x,k+1,l,hx,.step hc hR wk,wl,by omega⟩
    · have hE : E a c=true := by simpa [arcUnion,hR] using hac
      obtain ⟨haM,hcM⟩ := hs a ha c hc hE hR
      obtain ⟨m,hm,wm⟩ := hr c hcM x hx k (by omega) wk
      exact ⟨a,0,m+l+1,haM,.refl _,.step hc hE (wm.append wl),by omega⟩

theorem union_walk_replacement {R E : CH.Digraph} {V M : Finset ℕ} {q : ℕ}
    (hs : ∀ x∈V, ∀ y∈V, E x y=true → ¬R x y=true → x∈M ∧ y∈M)
    (hr : ∀ x∈M, ∀ y∈M, ∀ n, n≤q → Walk R V x y n →
      ∃ m, m≤n ∧ Walk E V x y m)
    {a b n : ℕ} (w : Walk (arcUnion R E) V a b n)
    (ha : a∈V) (haM : a∈M) (hb : b∈M) (hn : n≤q) :
    ∃ m, m≤n ∧ Walk E V a b m := by
  obtain ⟨x,k,l,hx,wk,wl,hkl⟩ := union_walk_prefix hs hr w ha hb hn
  obtain ⟨m,hm,wm⟩ := hr a haM x hx k (by omega) wk
  exact ⟨m+l,by omega,wm.append wl⟩

theorem union_walk_first_new {R E : CH.Digraph} {V : Finset ℕ}
    {a b n : ℕ} (w : Walk (arcUnion R E) V a b n) :
    Walk R V a b n ∨ ∃ x y k l, k+1+l=n ∧ Walk R V a x k ∧
      E x y=true ∧ ¬R x y=true ∧ y∈V ∧ Walk (arcUnion R E) V y b l := by
  induction w with
  | refl a => exact Or.inl (.refl a)
  | @step a c b n hc hac w ih =>
    by_cases hR : R a c=true
    · rcases ih with old | ⟨x,y,k,l,hlen,wk,hE,hnot,hy,wl⟩
      · exact Or.inl (.step hc hR old)
      · exact Or.inr ⟨x,y,k+1,l,by omega,.step hc hR wk,hE,hnot,hy,wl⟩
    · have hE : E a c=true := by simpa [arcUnion,hR] using hac
      exact Or.inr ⟨a,c,0,n,by omega,.refl _,hE,hR,hc,w⟩

/-- Short segments, rather than all walks, suffice. No positivity assumption
on the cutoff, cardinality, or cycle structure is needed. -/
theorem qfree_union_of_short_replacement {R E : CH.Digraph} {V M : Finset ℕ} {q : ℕ}
    (hR : QFree R V q) (hE : QFree E V q)
    (hs : ∀ x∈V, ∀ y∈V, E x y=true → ¬R x y=true → x∈M ∧ y∈M)
    (hr : ∀ x∈M, ∀ y∈M, ∀ n, n≤q → Walk R V x y n →
      ∃ m, m≤n ∧ Walk E V x y m) : QFree (arcUnion R E) V q := by
  intro a n hn hnq w
  have ha : a∈V := by
    cases n with
    | zero => omega
    | succ n => exact (w.unsnoc).choose_spec.2.1
  rcases union_walk_first_new w with old | ⟨x,y,k,l,hlen,wk,hxy,hnot,hy,wl⟩
  · exact hR a n hn hnq old
  have hx : x∈V := wk.end_mem_or.elim (fun h => h ▸ ha) id
  obtain ⟨hxM,hyM⟩ := hs x hx y hy hxy hnot
  have wkU : Walk (arcUnion R E) V a x k :=
    walk_sub (fun i j hij => by simp [arcUnion,hij]) wk
  obtain ⟨m,hm,wm⟩ := union_walk_replacement hs hr (wl.append wkU) hy hyM hxM (by omega)
  exact hE x (m+1) (by omega) (by omega) (.step hy hxy wm)

end LeanCH.BR.WeightedSD
