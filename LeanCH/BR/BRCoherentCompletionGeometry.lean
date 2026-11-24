import LeanCH.BR.BRSaturatedFreshExchange
import LeanCH.BR.BRAdjacentRelay

namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

/-- Two individually safe additions sharing a tail or a head are jointly safe.
No saturation, degree condition, or fixed cutoff is used. -/
theorem qfree_two_insertions_shared_endpoint {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (i j k l : ℕ) (hshare : i=k ∨ j=l)
    (h1 : QFree (insertArc D i j) V q) (h2 : QFree (insertArc D k l) V q) :
    QFree (insertArc (insertArc D i j) k l) V q := by
  have hc : CrossIncidence (insertArc D i j) (insertArc D k l) V := by
    intro a ha b hb c hcv d hd eab nab ecd ncd
    have hab : a=i ∧ b=j := by
      by_contra hn
      have he : D a b=true := by simpa only [insertArc,hn,ite_false] using eab
      exact nab (insertArc_mono D k l a b he)
    have hcd : c=k ∧ d=l := by
      by_contra hn
      have he : D c d=true := by simpa only [insertArc,hn,ite_false] using ecd
      exact ncd (insertArc_mono D i j c d he)
    rcases hab with ⟨rfl,rfl⟩
    rcases hcd with ⟨rfl,rfl⟩
    exact hshare
  apply qfree_sub (E := arcUnion (insertArc D i j) (insertArc D k l)) ?_
    (qfree_union_cross_incidence h1 h2 hc)
  intro a b he
  by_cases hn : a=k ∧ b=l
  · simp [arcUnion,insertArc,hn.1,hn.2]
  · have hh : insertArc D i j a b=true := by simpa only [insertArc,hn,ite_false] using he
    simp [arcUnion,hh]

theorem old_head_avoids_shared_insertions {D : CH.Digraph} {i j k l h : ℕ}
    (hshare : i=k ∨ j=l) (h1 : ¬D i j=true) (h2 : ¬D k l=true)
    (he : D i h=true) : h≠j ∧ h≠l := by
  refine ⟨fun e=>h1 (e ▸ he),?_⟩
  intro e
  rcases hshare with hk|hl
  · exact h2 (by simpa only [←hk,←e] using he)
  · exact h1 (by simpa only [hl,e] using he)

namespace AdjacentRelay.Base
open RelayFold

/-- The COMPLETE singleton bank clears every return of length at most two. -/
theorem singleton_bank_completion {D : CH.Digraph} {V : Finset ℕ} {u h t c e : ℕ}
    (B : AdjacentRelay.Base D V u h t) (hC : C D V u h t={c})
    (he : e∈X0 D V u h t) :
    ¬D e u=true ∧ QFree (insertArc (eraseArc D u c) e u) V 3 := by
  have heV := (mem_X0.mp he).1
  have heu := (B.X_ne (RelayFold.Base.X0_X he)).1
  refine ⟨(mem_X0.mp he).2.2.2,?_⟩
  apply qfree_insertArc (qfree_sub (eraseArc_sub D u c) B.free) ⟨e,heV⟩ ⟨u,B.umem⟩
  change e∉ball (eraseArc D u c) V u 2
  rintro hb
  obtain ⟨_,n,hn,w⟩ := mem_ball.mp hb
  have hc (x : ℕ) (hx : x∈C D V u h t) : x=c := by simpa only [hC,mem_singleton] using hx
  have nret : ∀x∈V,eraseArc D u c u x=true → x≠e ∧ ¬D x e=true := by
    intro x hx eux
    have ed := eraseArc_sub D u c u x eux
    have nxc : x≠c := by intro eq; subst x; simp [eraseArc] at eux
    constructor
    · intro eq
      exact nxc (hc x (mem_C.mpr ⟨hx,ed,Or.inl (eq.symm ▸ he)⟩))
    · intro exe
      exact nxc (hc x (mem_C.mpr ⟨hx,ed,Or.inr ⟨e,he,exe⟩⟩))
  have hn2 : n≤2 := hn
  have hcases : n=0 ∨ n=1 ∨ n=2 := by omega
  rcases hcases with rfl|rfl|rfl
  · cases w
    exact heu rfl
  · cases w with
    | step hx eux wx =>
      cases wx
      exact (nret e hx eux).1 rfl
  · cases w with
    | step hx eux wx =>
      cases wx with
      | step hy exy wy =>
        cases wy
        exact (nret _ hx eux).2 (eraseArc_sub D u c _ e exy)


/-- Saturation supplies an actual member of the complete bank from each
independent X0 receiver, retaining its edge into that receiver. -/
theorem bank_nonempty_of_independent {D : CH.Digraph} {V : Finset ℕ} {u h t p : ℕ}
    (B : AdjacentRelay.Base D V u h t) (hsat : Sat 3 D V)
    (hp : p∈X0 D V u h t) (hup : ¬D u p=true) :
    ∃c∈C D V u h t,D c p=true := by
  obtain ⟨_,n,hn,w⟩ := mem_ball.mp (hsat u B.umem p (mem_X0.mp hp).1 (mem_X0.mp hp).2.2.2)
  have hpu := (B.X_ne (RelayFold.Base.X0_X hp)).1
  have hn2 : n≤2 := hn
  have hcases : n=0 ∨ n=1 ∨ n=2 := by omega
  rcases hcases with rfl|rfl|rfl
  · cases w
    exact False.elim (hpu rfl)
  · cases w with
    | step hx eux wx =>
      cases wx
      exact False.elim (hup eux)
  · cases w with
    | step hx eux wx =>
      cases wx with
      | step hy exp wy =>
        cases wy
        exact ⟨_,mem_C.mpr ⟨hx,eux,Or.inr ⟨p,hp,exp⟩⟩,exp⟩


end AdjacentRelay.Base
end LeanCH.BR.WeightedSD

