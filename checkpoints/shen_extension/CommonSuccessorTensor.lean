import checkpoints.shen_extension.LabelledReachTensor

namespace LeanCH.BR.ShenCommonSuccessor
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

/-- Many different roots with large r-balls force their union to grow:
on the roots themselves, r-reach has no reciprocal off-diagonal pair. -/
theorem common_ball_capacity {D : CH.Digraph} {V C K : Finset ℕ} {q r B : ℕ}
    (hf : QFree D V q) (hr : 2*r≤q) (hCV : C⊆V) (hne : C.Nonempty)
    (hK : ∀ h∈C, ball D V h r⊆K) (hB : ∀ h∈C, B≤(ball D V h r).card) :
    C.card+2*B≤2*K.card+1 := by
  let E : CH.Digraph := fun x y => decide (x≠y ∧ y∈ball D V x r)
  have hE : QFree E C 2 := by
    apply DotTwoPassShellTransport.qfree_of_bounded_arc_lift hf (show r*2≤q by omega)
    intro x hx y hy hxy
    obtain ⟨hne',hb⟩ := of_decide_eq_true hxy
    obtain ⟨_,l,hl,w⟩ := mem_ball.mp hb
    refine ⟨l,?_,hl,w⟩
    cases l with
    | zero => cases w; exact (hne' rfl).elim
    | succ l => omega
  let e := K.card-B
  have hCK : C⊆K := fun h hh => hK h hh (self_mem_ball (hCV hh))
  have hmin (h) (hh : h∈C) : C.card-e≤(ball E C h 1).card := by
    have sub : C \ ball E C h 1 ⊆ K \ ball D V h r := by
      intro y hy
      obtain ⟨hyC,hout⟩ := Finset.mem_sdiff.mp hy
      refine Finset.mem_sdiff.mpr ⟨hCK hyC,?_⟩
      intro hb
      apply hout
      by_cases he : h=y
      · subst y; exact self_mem_ball hh
      · exact ball_of_adj hyC (by simp [E,he,hb] : E h y=true)
    have H := Finset.card_le_card sub
    rw [Finset.card_sdiff_of_subset ball_subset,Finset.card_sdiff_of_subset (hK h hh)] at H
    have := hB h hh; dsimp [e]; omega
  have hc := card_ge_of_two_balls hE (by decide : 1+1≤2) hmin hmin hne
  obtain ⟨v,hv⟩ := hne
  have := (hB v hv).trans (Finset.card_le_card (hK v hv))
  dsimp [e] at hc; omega

private theorem first_in_order {A : Finset ℕ} {P : ℕ → ℕ → Prop}
    (hne : A.Nonempty) (refl : ∀ x∈A, P x x)
    (total : ∀ x∈A, ∀ y∈A, P x y ∨ P y x)
    (trans : ∀ x∈A, ∀ y∈A, ∀ z∈A, P x y → P y z → P x z) :
    ∃ x∈A, ∀ y∈A, P x y := by
  have aux (U : Finset ℕ) : U⊆A → U.Nonempty → ∃ x∈U, ∀ y∈U, P x y := by
    induction U using Finset.induction_on with
    | empty => simp
    | @insert v U hv ih =>
      intro hsub _
      have hvA := hsub (Finset.mem_insert_self v U)
      by_cases hU : U.Nonempty
      · have subU : U⊆A := (Finset.subset_insert v U).trans hsub
        obtain ⟨x,hx,hall⟩ := ih subU hU
        rcases total v hvA x (subU hx) with hvx|hxv
        · refine ⟨v,Finset.mem_insert_self _ _,?_⟩
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl|hy
          · exact refl _ hvA
          · exact trans _ hvA _ (subU hx) _ (subU hy) hvx (hall y hy)
        · refine ⟨x,Finset.mem_insert_of_mem hx,?_⟩
          intro y hy
          exact (Finset.mem_insert.mp hy).elim (fun he => he ▸ hxv) (hall y)
      · have hz := Finset.not_nonempty_iff_eq_empty.mp hU
        subst U
        exact ⟨v,by simp,by simpa using refl v hvA⟩
  exact aux A (Finset.Subset.refl _) hne

/-- Pairwise close rows of a semicomplete reach relation must be few. Their
short paths forbid directed triangles, so the first row reaches everyone
and the last reaches only itself. Their difference then pays for the bank. -/
theorem ordered_row_capacity {D : CH.Digraph} {V A : Finset ℕ} {q l e : ℕ}
    (hf : QFree D V q) (hAV : A⊆V) (ha : A.Nonempty)
    (hr : l+e+1≤q) (htri : 3*e≤q)
    (total : ∀ x∈A, ∀ y∈A, y∈ball D V x l ∨ x∈ball D V y l)
    (diff : ∀ x∈A, ∀ y∈A, (ball D V x l \ ball D V y l).card≤e) : A.card≤e+1 := by
  let P := fun x y => y∈ball D V x l
  have small (x) (hx : x∈A) (y) (hy : y∈A) (hxy : P x y) :
      ∃ i, i≤e ∧ Walk D V x y i := by
    obtain ⟨_,i,hi,wi⟩ := mem_ball.mp hxy
    exact ⟨i,ShenContainerTransfer.walk_length_le_omissions hf (hAV hx)
      (Finset.Subset.refl _) hi wi hr (diff x hx y hy),wi⟩
  have pos {x y i} (hne : x≠y) (w : Walk D V x y i) : 0<i := by
    cases i with
    | zero => cases w; exact (hne rfl).elim
    | succ i => omega
  have antisym (x) (hx : x∈A) (y) (hy : y∈A) (hxy : P x y) (hyx : P y x) : x=y := by
    by_contra hne
    obtain ⟨i,hi,wi⟩ := small x hx y hy hxy
    obtain ⟨j,hj,wj⟩ := small y hy x hx hyx
    have := pos hne wi
    exact hf x (i+j) (by omega) (by omega) (wi.append wj)
  have trans (x) (hx : x∈A) (y) (hy : y∈A) (z) (hz : z∈A)
      (hxy : P x y) (hyz : P y z) : P x z := by
    by_contra hbad
    have hzx := (total x hx z hz).resolve_left hbad
    have hne : x≠z := fun he => hbad (he ▸ self_mem_ball (hAV hx))
    obtain ⟨i,hi,wi⟩ := small x hx y hy hxy
    obtain ⟨j,hj,wj⟩ := small y hy z hz hyz
    obtain ⟨k,hk,wk⟩ := small z hz x hx hzx
    have := pos hne.symm wk
    exact hf x (i+j+k) (by omega) (by omega) ((wi.append wj).append wk)
  have refl (x) (hx : x∈A) : P x x := self_mem_ball (hAV hx)
  obtain ⟨x,hx,hfirst⟩ := first_in_order (P:=P) ha refl total trans
  obtain ⟨z,hz,hlast⟩ := first_in_order (P:=fun x y => P y x) ha refl
    (fun x hx y hy => total y hy x hx)
    (fun x hx y hy w hw hyx hwy => trans w hw y hy x hx hwy hyx)
  have sub : A.erase z ⊆ ball D V x l \ ball D V z l := by
    intro y hy
    obtain ⟨hnez,hy'⟩ := Finset.mem_erase.mp hy
    exact Finset.mem_sdiff.mpr ⟨hfirst y hy',fun hzy =>
      hnez (antisym y hy' z hz (hlast y hy') hzy)⟩
  have hc := (Finset.card_le_card sub).trans (diff x hx z hz)
  have := Finset.card_erase_add_one hz
  omega

#print axioms common_ball_capacity
#print axioms ordered_row_capacity

/-- Compare two named rows through their common successors. Only the
enlarged first row needs a size bound, and the two hole bounds are local. -/
theorem pair_row_diff {D : CH.Digraph} {V T : Finset ℕ} {q r b N g e x y : ℕ}
    (hf : QFree D V q) (hTV : T⊆V) (hhalf : 2*r≤q)
    (hB : ∀ z∈T,b≤(ball D V z r).card) (hN : (ball D V x (r+1)).card≤N)
    (hx : (T \ outN D T x).card≤g) (hy : (T \ outN D T y).card≤g)
    (hT : 2*g<T.card) (hcut : 2*N+1+2*g<T.card+2*b+2*(e+1)) :
    (ball D V x (r+1) \ ball D V y (r+1)).card≤e := by
  let C := outN D T x ∩ outN D T y
  let K := ball D V x (r+1) ∩ ball D V y (r+1)
  have hCT : C⊆T := Finset.inter_subset_left.trans outN_subset
  have hXY : T \ C ⊆ (T \ outN D T x) ∪ (T \ outN D T y) := by
    intro z hz
    obtain ⟨hzT,hn⟩ := Finset.mem_sdiff.mp hz
    by_cases hx' : z∈outN D T x
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hzT,fun hy' => hn (Finset.mem_inter.mpr ⟨hx',hy'⟩)⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hzT,hx'⟩)
  have diff := (Finset.card_le_card hXY).trans (Finset.card_union_le _ _)
  have hsplit := Finset.card_sdiff_add_card_eq_card hCT
  have cover : ∀ z∈C, ball D V z r⊆K := by
    intro z hz w hw
    obtain ⟨hzx,hzy⟩ := Finset.mem_inter.mp hz
    have path (v) (hzv : z∈outN D T v) : w∈ball D V v (r+1) := by
      obtain ⟨_,m,hm,wm⟩ := mem_ball.mp hw
      exact mem_ball.mpr ⟨ball_subset hw,m+1,by omega,.step (hTV (outN_subset hzv))
        (mem_outN.mp hzv).2 wm⟩
    exact Finset.mem_inter.mpr ⟨path x hzx,path y hzy⟩
  have hbank := common_ball_capacity hf hhalf (hCT.trans hTV)
    (Finset.card_pos.mp (by omega)) cover (fun z hz => hB z (hCT hz))
  have hparts : (ball D V x (r+1) \ ball D V y (r+1)).card+K.card=
      (ball D V x (r+1)).card := Finset.card_sdiff_add_card_inter _ _
  omega

/-- Dense S-to-T incidence forces pairwise overlapping enlarged reach rows.
At complementary saturation their compressed comparisons are transitive.
The resulting bound charges every discarded row to its own missing cells. -/
theorem dense_table_bound {D : CH.Digraph} {V S T : Finset ℕ} {q r b N g e : ℕ}
    (hf : QFree D V q) (hSV : S⊆V) (hTV : T⊆V) (hhalf : 2*r≤q)
    (hB : ∀ z∈T, b≤(ball D V z r).card)
    (hN : ∀ x∈S, (ball D V x (r+1)).card≤N)
    (total : ∀ x∈S, ∀ y∈S, y∈ball D V x (r+1) ∨ x∈ball D V y (r+1))
    (hT : 2*g<T.card) (hcut : 2*N+1+2*g<T.card+2*b+2*(e+1))
    (hret : r+1+e+1≤q) (htri : 3*e≤q) :
    (g+1)*S.card≤(g+1)*(e+1)+∑ x∈S, (T \ outN D T x).card := by
  let miss := fun x => (T \ outN D T x).card
  let A := S.filter (fun x => miss x≤g)
  have hAS : A⊆S := Finset.filter_subset _ _
  have close (x) (hx : x∈A) (y) (hy : y∈A) :=
    pair_row_diff hf hTV hhalf hB (hN x (hAS hx)) (Finset.mem_filter.mp hx).2
      (Finset.mem_filter.mp hy).2 hT hcut
  have small : A.card≤e+1 := by
    rcases A.eq_empty_or_nonempty with hz|hn
    · simp [hz]
    exact ordered_row_capacity hf (hAS.trans hSV) hn hret htri
      (fun x hx y hy => total x (hAS hx) y (hAS hy)) close
  have hbad (x) (hx : x∈S \ A) : g+1≤miss x := by
    obtain ⟨hxS,hn⟩ := Finset.mem_sdiff.mp hx
    by_contra! h
    exact hn (Finset.mem_filter.mpr ⟨hxS,by omega⟩)
  have badsum := Finset.sum_le_sum hbad
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at badsum
  have subsum := Finset.sum_le_sum_of_subset_of_nonneg (f:=miss)
    (Finset.sdiff_subset (s:=S) (t:=A)) (fun _ _ _ => Nat.zero_le _)
  have eqS := Finset.card_sdiff_add_card_eq_card hAS
  change (g+1)*S.card≤(g+1)*(e+1)+∑ x∈S, miss x
  nlinarith only [badsum,subsum,Nat.mul_le_mul_left (g+1) small,
    congrArg (fun n : ℕ => n*(g+1)) eqS]

#print axioms dense_table_bound
end LeanCH.BR.ShenCommonSuccessor
