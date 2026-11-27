import checkpoints.shen_extension.CommonCoreCompression

namespace LeanCH.BR.CommonCoreCompression
open Finset BRq2 BRq3 BypassRepair
open scoped Classical

/-- The ball grown from the common heads cannot touch the block or its
common parents in the first q-2 steps. Compression bounds the space in
which this ball can grow, while the induction on degree forces its growth. -/
theorem no_near_rectangle {D V T P q t} (free : QFree D V q) (hq : 3≤q) (ht : 2≤t)
    (reg : OutEq (t+1) D V) (order : V.card=q*t+2) (lower : ∀ k,k<t+1 → NoHost q k)
    (tv : T⊆V) (pv : P⊆V) (large : t-1≤T.card) (size : t≤P.card)
    (core : ∀ a∈T,∀ b∈P,D a b=true) : False := by
  classical
  obtain ⟨C,ct,cc⟩ := exists_subset_card_eq large
  obtain ⟨B,bp,bc⟩ := exists_subset_card_eq size
  have cv := ct.trans tv
  have bv := bp.trans pv
  have hit (a) (ac : a∈C) (p) (pb : p∈B) := core a (ct ac) p (bp pb)
  have cl : C.Nonempty := card_pos.mp (by omega)
  obtain ⟨a,ac⟩ := cl
  have bl : B.Nonempty := card_pos.mp (by omega)
  let H := parents D V C
  let A (j : ℕ) := B.biUnion (fun p => ball D V p j)
  have av (j) : A j⊆V := biUnion_subset.mpr (fun _ _ => ball_subset)
  have start (j) : B⊆A j := fun p pb => mem_biUnion.mpr ⟨p,pb,self_mem_ball (bv pb)⟩
  have cap := capacity free (by omega) (by omega) reg order (lower t (by omega)) cv bv
    (show C.Nonempty from ⟨a,ac⟩) bc.ge hit
  have cb : Disjoint C B := disjoint_left.mpr (fun _ xc xb => loopfree free (by omega) (cv xc) (hit _ xc _ xb))
  rw [card_sdiff_of_subset (union_subset cv bv),card_union_of_disjoint cb,cc,bc] at cap
  change V.card-(t-1+t)≤H.card*(t+1-(t-1)) at cap
  rw [show t+1-(t-1)=2 by omega] at cap
  have hc : Disjoint C H := by
    apply disjoint_left.mpr
    intro x xc xh
    exact loopfree free (by omega) (cv xc) (mem_outN.mp ((mem_filter.mp xh).2 xc)).2
  have hs : H⊆V := filter_subset _ _
  have room (j) (jq : j≤q-2) : 2*(A j).card≤q*t+3 := by
    have dis : Disjoint (A j) (C ∪ H) := by
      apply disjoint_left.mpr
      intro x xm ys
      obtain ⟨p,pb,ballx⟩ := mem_biUnion.mp xm
      obtain ⟨_,k,kj,w⟩ := mem_ball.mp ballx
      rcases mem_union.mp ys with xc|xh
      · exact free p _ (by omega) (by omega) (w.snoc (bv pb) (hit x xc p pb))
      · have xa := (mem_outN.mp ((mem_filter.mp xh).2 ac)).2
        exact free p _ (by omega) (by omega) ((w.snoc (cv ac) xa).snoc (bv pb) (hit a ac p pb))
    have bound := card_le_card (union_subset (av j) (union_subset cv hs))
    rw [card_union_of_disjoint dis,card_union_of_disjoint hc,cc] at bound
    omega
  have qt : 3≤q*t := by nlinarith
  have step (j) (jq : j<q-2) : ∃ d, q*d+1≤(A j).card ∧ (A j).card+(t+1)≤(A (j+1)).card+d := by
    obtain ⟨x,xm,least⟩ := (A j).exists_min_image (fun v => (outN D (A j) v).card)
      (bl.mono (start j))
    let d := (outN D (A j) x).card
    have capj := room j jq.le
    have safe := free.mono_set (av j)
    have small : d<t := by
      by_contra! heavy
      exact lower t (by omega) D (A j) (bl.mono (start j)) (by omega) safe
        (fun v vm => heavy.trans (least v vm))
    have light : q*d+1≤(A j).card := by
      by_contra! heavy
      exact lower d (by omega) D (A j) (bl.mono (start j)) (by omega) safe least
    have oldsub : A j ⊆ A (j+1) := by
      intro v vm
      obtain ⟨p,pb,hit⟩ := mem_biUnion.mp vm
      obtain ⟨vv,k,le,w⟩ := mem_ball.mp hit
      exact mem_biUnion.mpr ⟨p,pb,mem_ball.mpr ⟨vv,k,by omega,w⟩⟩
    have more : outN D V x ⊆ A (j+1) := by
      intro y ym
      obtain ⟨p,pb,px⟩ := mem_biUnion.mp xm
      obtain ⟨_,k,le,w⟩ := mem_ball.mp px
      obtain ⟨yv,xy⟩ := mem_outN.mp ym
      exact mem_biUnion.mpr ⟨p,pb,mem_ball.mpr ⟨yv,k+1,by omega,w.snoc yv xy⟩⟩
    have joint := card_le_card (union_subset more oldsub)
    have sz := card_union_add_card_inter (outN D V x) (A j)
    have inter : outN D V x ∩ A j = outN D (A j) x := by
      ext y
      simp only [mem_outN,mem_inter]
      constructor
      · rintro ⟨⟨_,e⟩,m⟩; exact ⟨m,e⟩
      · rintro ⟨m,e⟩; exact ⟨⟨av j m,e⟩,m⟩
    rw [reg x (av j xm),inter] at sz
    exact ⟨d,light,by dsimp [d]; omega⟩
  have base : A 0=B := by
    apply Subset.antisymm _ (start 0)
    intro v vm
    obtain ⟨p,pb,m⟩ := mem_biUnion.mp vm
    obtain ⟨_,k,le,w⟩ := mem_ball.mp m
    obtain rfl : k=0 := by omega
    cases w
    exact pb
  obtain ⟨d,ld,gd⟩ := step 0 (by omega)
  rw [base,bc] at ld gd
  change t+(t+1)≤(A 1).card+d at gd
  have first : 2*d+2≤t := by
    by_cases dz : d=0
    · omega
    · have mul := Nat.mul_le_mul_right d hq
      omega
  have grow (j) (pos : 1≤j) (le : j≤q-2) :
      2*t+j*(t+2)+2≤2*(A j).card := by
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases jz : j=0
      · subst j; simp only [Nat.zero_add,Nat.one_mul]; omega
      · have prior := ih (by omega) (by omega)
        obtain ⟨d,ld,gd⟩ := step j (by omega)
        have capj := room j (by omega)
        have thin : 2*d≤t := by
          by_contra! high
          have m := Nat.mul_le_mul_left q (show t+1≤2*d by omega)
          nlinarith
        rw [Nat.succ_mul j (t+2)]
        omega
  have far := grow (q-2) (by omega) (by omega)
  have endcap := room (q-2) (by omega)
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hq
  simp only [show 3+l-2=1+l by omega] at far
  have same : 3+l-2=1+l := by omega
  rw [same] at endcap
  nlinarith

#print axioms no_near_rectangle
end LeanCH.BR.CommonCoreCompression
