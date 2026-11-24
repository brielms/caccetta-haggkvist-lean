import LeanCH.BR.BRWeightedExtremalCompetitors

/-! Actual single-tail exchanges on a globally selected native source.
The final graph's q-freeness is a premise, never inferred from separate moves. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem arcSet_insert {D : CH.Digraph} {V : Finset ℕ} {u t : ℕ}
    (hu : u∈V) (ht : t∈V) :
    arcSet (insertArc D u t) V=insert (u,t) (arcSet D V) := by
  ext e
  rcases e with ⟨x,y⟩
  by_cases h : x=u ∧ y=t
  · rcases h with ⟨rfl,rfl⟩
    simp [arcSet,insertArc,hu,ht]
  · simp [arcSet,insertArc,h,Prod.mk.injEq]

theorem arcSet_same_tail_card {D : CH.Digraph} {V : Finset ℕ} {u v t : ℕ}
    (hu : u∈V) (hv : v∈V) (ht : t∈V) (huv : D u v=true) (hut : ¬D u t=true) :
    (arcSet (insertArc (eraseArc D u v) u t) V).card=(arcSet D V).card := by
  have hmem : (u,v)∈arcSet D V := mem_filter.mpr ⟨mem_product.mpr ⟨hu,hv⟩,huv⟩
  have hnot : (u,t)∉arcSet (eraseArc D u v) V := by
    intro hh
    exact hut (eraseArc_sub D u v u t (mem_filter.mp hh).2)
  rw [arcSet_insert hu ht,card_insert_of_notMem hnot,arcSet_erase,card_erase_of_mem hmem]
  have hp := card_pos.mpr ⟨(u,v),hmem⟩
  omega

theorem row_same_tail_exchange (q : ℕ) {D : CH.Digraph} {V : Finset ℕ}
    {u v t : ℕ} (hv : v∈V) (ht : t∈V) (huv : D u v=true)
    (hut : ¬D u t=true) (a : ℕ→ℚ) (x : ℕ) :
    row q (insertArc (eraseArc D u v) u t) V a x=
      row q D V a x + if x=u then (q:ℚ)*(a t-a v) else 0 := by
  have htv : t≠v := fun hh => hut (by simpa [hh] using huv)
  have hs : outW (insertArc (eraseArc D u v) u t) V a x =
      outW D V a x + (if x=u then a t else 0) - (if x=u then a v else 0) := by
    unfold outW
    have he : (∑ y∈V,if insertArc (eraseArc D u v) u t x y=true then a y else 0)=
        (∑ y∈V,if D x y=true then a y else 0) +
        (∑ y∈V,if x=u ∧ y=t then a t else 0) -
        (∑ y∈V,if x=u ∧ y=v then a v else 0) := by
      rw [← sum_add_distrib,← sum_sub_distrib]
      apply sum_congr rfl
      intro y hy
      by_cases hxu : x=u <;> by_cases hyt : y=t <;> by_cases hyv : y=v <;>
        simp_all [insertArc,eraseArc]
    rw [he]
    by_cases hxu : x=u <;> simp [hxu,hv,ht]
  rw [row,hs,row]
  by_cases hxu : x=u <;> simp only [hxu,ite_true,ite_false] <;> ring

theorem NativeExtremal.same_tail_weight_le {q : ℕ} (hq : 0<q)
    {D : CH.Digraph} {V : Finset ℕ} {c : ℚ}
    (h : NativeExtremal q D V c) (hsmall : SmallerSmallRow q V.card)
    (hc : 1<c) (a : ℕ→ℚ) (ha : ∀ x∈V,0<a x) (hm : mass V a=1)
    (hr : ∀ x∈V,row q D V a x=c) {u v t : ℕ}
    (hu : u∈V) (hv : v∈V) (ht : t∈V) (huv : D u v=true) (hut : ¬D u t=true)
    (hfree : QFree (insertArc (eraseArc D u v) u t) V q) : a t≤a v := by
  by_contra hh
  have hlt : a v<a t := lt_of_not_ge hh
  have hq' : (0:ℚ)<q := by exact_mod_cast hq
  have hgain : ∀ x∈V,c≤row q (insertArc (eraseArc D u v) u t) V a x := by
    intro x hx
    rw [row_same_tail_exchange q hv ht huv hut,hr x hx]
    split_ifs <;> nlinarith
  have he := (h.competitor_rows hsmall hc a ha hm hfree
    (arcSet_same_tail_card hu hv ht huv hut) hgain).1 u hu
  rw [row_same_tail_exchange q hv ht huv hut,hr u hu,ite_eq_left rfl] at he
  nlinarith

theorem NativeExtremal.same_tail_neutral {q : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V : Finset ℕ} {c : ℚ}
    (h : NativeExtremal q D V c) (hsmall : SmallerSmallRow q V.card)
    (hc : 1<c) (a : ℕ→ℚ) (ha : ∀ x∈V,0<a x) (hm : mass V a=1)
    (hr : ∀ x∈V,row q D V a x=c) {u v t : ℕ}
    (hu : u∈V) (hv : v∈V) (ht : t∈V) (huv : D u v=true) (hut : ¬D u t=true)
    (hfree : QFree (insertArc (eraseArc D u v) u t) V q) (htie : a t=a v) :
    (∀ x∈V,row q (insertArc (eraseArc D u v) u t) V a x=c) ∧
    ∃ p' : ℕ→ℚ, (∀ x∈V,0<p' x) ∧ mass V p'=1 ∧
      (∀ x∈V,col q (insertArc (eraseArc D u v) u t) V p' x=c) ∧
      ∀ b : ℕ→ℚ, (∀ x∈V,row q (insertArc (eraseArc D u v) u t) V b x=c) →
        ∀ x∈V,b x=a x := by
  apply h.competitor_preserves_primal hq hsmall hc a ha hm hfree
    (arcSet_same_tail_card hu hv ht huv hut)
  intro x hx
  rw [row_same_tail_exchange q hv ht huv hut,htie,sub_self,mul_zero,ite_self,add_zero,hr x hx]

theorem NativeExtremal.same_head_weight_le {q : ℕ} (hq : 0<q)
    {D : CH.Digraph} {V : Finset ℕ} {c : ℚ}
    (h : NativeExtremal q D V c) (hsmall : SmallerSmallRow q V.card)
    (hc : 1<c) (p : ℕ→ℚ) (hp : ∀ x∈V,0<p x) (hm : mass V p=1)
    (hr : ∀ x∈V,col q D V p x=c) {u v t : ℕ}
    (hu : u∈V) (hv : v∈V) (ht : t∈V) (hvu : D v u=true) (htu : ¬D t u=true)
    (hfree : QFree (insertArc (eraseArc D v u) t u) V q) : p t≤p v := by
  apply (h.reverse hsmall).same_tail_weight_le hq hsmall hc p hp hm hr hu hv ht hvu htu
  have he : (fun x y => insertArc (eraseArc D v u) t u y x)=
      insertArc (eraseArc (fun x y => D y x) u v) u t := by
    funext x y
    simp only [insertArc,eraseArc,and_comm]
  rw [←he]
  exact hfree.reverse

end LeanCH.BR.WeightedSD
