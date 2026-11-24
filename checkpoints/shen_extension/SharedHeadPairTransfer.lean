import checkpoints.shen_extension.SharedHeadNonedges

namespace LeanCH.BR.ShenSharedHead
open BRq2 BRq3 BR45
open Classical

/-- The two labelled heads have their entire union of successors in the
parent's endpoint container. Common parents reached by v occupy separate
places there, as do i and j if they are mutually nonadjacent. -/
theorem pair_transfer {D : CH.Digraph} {V : Finset ℕ} {s u v i j}
    (hf : QFree D V 3) (hm : OutEq s D V) (hv : v∈V)
    (hi : i∈commonOut D V u v) (hj : j∈commonOut D V u v)
    (aij : absent D i j=true) :
    s+2+(commonIn D (outN D V v) i j).card≤
      (endpoints D V u v).card+(commonOut D V i j).card := by
  let O := outN D V v
  let S := outN D V i ∪ outN D V j
  let P := commonIn D O i j
  have io := (Finset.mem_inter.mp hi).2
  have jo := (Finset.mem_inter.mp hj).2
  have iV := (mem_outN.mp io).1
  have jV := (mem_outN.mp jo).1
  obtain ⟨diff,ij,ji⟩ := of_decide_eq_true aij
  have freeI := loopfree hf (by decide) iV
  have freeJ := loopfree hf (by decide) jV
  have outside (w) (hw : w∈commonOut D V u v) : outN D V w⊆O∪endpoints D V u v := by
    intro z hz
    by_cases zo : z∈O
    · exact Finset.mem_union_left _ zo
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨(mem_outN.mp hz).1,zo,w,hw,(mem_outN.mp hz).2⟩)
  have all : S⊆O∪endpoints D V u v := Finset.union_subset (outside i hi) (outside j hj)
  have reserve : insert i (insert j P)⊆O \ S := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl|hz
    · exact Finset.mem_sdiff.mpr ⟨io,fun h => (Finset.mem_union.mp h).elim
        (fun e => freeI (mem_outN.mp e).2) (fun e => ji (mem_outN.mp e).2)⟩
    rcases Finset.mem_insert.mp hz with rfl|hz
    · exact Finset.mem_sdiff.mpr ⟨jo,fun h => (Finset.mem_union.mp h).elim
        (fun e => ij (mem_outN.mp e).2) (fun e => freeJ (mem_outN.mp e).2)⟩
    obtain ⟨zi,zj⟩ := Finset.mem_inter.mp hz
    have zO := (mem_inN.mp zi).1
    have zV := (mem_outN.mp zO).1
    exact Finset.mem_sdiff.mpr ⟨zO,fun h => (Finset.mem_union.mp h).elim
      (fun e => digonfree hf (by decide) iV zV (mem_outN.mp e).2 (mem_inN.mp zi).2)
      (fun e => digonfree hf (by decide) jV zV (mem_outN.mp e).2 (mem_inN.mp zj).2)⟩
  have noI : i∉P := fun h => freeI (mem_inN.mp (Finset.mem_inter.mp h).1).2
  have noJ : j∉P := fun h => freeJ (mem_inN.mp (Finset.mem_inter.mp h).2).2
  have count := Finset.card_le_card reserve
  rw [Finset.card_insert_of_notMem (by simpa [diff] using noI),Finset.card_insert_of_notMem noJ] at count
  have inc : S ∪ (O \ S)⊆O∪endpoints D V u v := Finset.union_subset all (Finset.sdiff_subset.trans Finset.subset_union_left)
  have room := (Finset.card_le_card inc).trans (Finset.card_union_le _ _)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_sdiff)] at room
  have size : S.card+(commonOut D V i j).card=s+s := (Finset.card_union_add_card_inter _ _).trans
    (congrArg₂ (·+·) (hm i iV) (hm j jV))
  have card : O.card=s := hm v hv
  change s+2+P.card≤_+_
  omega

/-- If each active bank at this root supplies even one missing pair with
the given adjusted codegree cap, its total residual is quadratically bounded.
The same active set is used for the orientation count and the row bills. -/
theorem parent_pair_bill {D : CH.Digraph} {V : Finset ℕ} {s u k}
    (hf : QFree D V 3) (hm : OutEq s D V) (hu : u∈V)
    (test : ∀ v∈activeParents D V u,∃ i∈commonOut D V u v,∃ j∈commonOut D V u v,
      absent D i j=true ∧ (commonOut D V i j).card≤k+(commonIn D (outN D V v) i j).card) :
    let P := activeParents D V u
    2*(∑ v∈outN D V u,residual D V u v)+P.card*(P.card+5)+missingPairs D P≤2*P.card*k := by
  intro P
  let U := outN D V u
  let f := residual D V u
  have sub : P⊆U := Finset.filter_subset _ _
  have size : U.card=s := hm u hu
  have split := Finset.card_sdiff_add_card_eq_card sub
  have one (v) (hv : v∈P) : f v+s+2≤(outN D P v).card+(U \ P).card+k := by
    obtain ⟨i,hi,j,hj,absentPair,cheap⟩ := test v hv
    have pay := pair_transfer hf hm (mem_outN.mp (sub hv)).1 hi hj absentPair
    have pos := (Finset.mem_filter.mp hv).2
    change 0<(commonOut D V u v).card-(endpoints D V u v).card at pos
    have equal : commonOut D V u v=outN D U v := by ext z; simp [commonOut,U,outN]; tauto
    have pieces := card_outN_union (D:=D) (show Disjoint P (U \ P) from Finset.disjoint_sdiff) v
    rw [Finset.union_sdiff_of_subset sub] at pieces
    have outCap := Finset.card_le_card (Finset.filter_subset _ _ : outN D (U \ P) v⊆U \ P)
    change (outN D (U \ P) v).card≤(U \ P).card at outCap
    change (commonOut D V u v).card-(endpoints D V u v).card+s+2≤_
    rw [equal] at pos ⊢
    omega
  have sum := Finset.sum_le_sum one
  simp only [Finset.sum_add_distrib,Finset.sum_const_nat (fun _ _ => rfl)] at sum
  have orient := orientation_exact (U:=P) (hf.mono_set (sub.trans (Finset.filter_subset _ _)))
  have fromP : (∑ v∈P,f v)=(∑ v∈U,f v) := by
    apply Finset.sum_subset sub
    intro v hv out
    by_contra! ne
    exact out (Finset.mem_filter.mpr ⟨hv,Nat.pos_of_ne_zero ne⟩)
  rw [fromP] at sum
  have eq := congrArg (fun n : ℕ => P.card*n) (split.trans size)
  change 2*(∑ v∈U,f v)+P.card*(P.card+5)+missingPairs D P≤_
  nlinarith only [sum,orient,eq]

private theorem quadratic_cap {a k L w : ℕ} (h : 2*L+a*(a+5)+w≤2*a*k) :
    2*L≤(k-2)*(k-3) := by
  by_cases small : k≤2
  · have bound := Nat.mul_le_mul_left (2*a) small
    nlinarith only [bound,h,Nat.zero_le (a*a),Nat.zero_le w,Nat.zero_le ((k-2)*(k-3))]
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (by omega : 3≤k)
  have k2 : k-2=j+1 := by omega
  have k3 : k-3=j := by omega
  rw [k2,k3]
  rw [hj] at h
  rcases le_or_gt a j with le|gt
  · obtain ⟨b,eq⟩ := Nat.exists_eq_add_of_le le
    rw [eq] at h ⊢
    nlinarith only [h,Nat.zero_le (b*b),Nat.zero_le w]
  · obtain ⟨b,eq⟩ := Nat.exists_eq_add_of_le (by omega : j+1≤a)
    rw [eq] at h
    nlinarith only [h,Nat.zero_le (b*b),Nat.zero_le w]

theorem pair_bill_global {D : CH.Digraph} {V : Finset ℕ} {s g k}
    (hf : QFree D V 3) (hm : OutEq s D V) (ne : V.Nonempty) (gap : V.card+g=3*s+1)
    (test : ∀ u∈V,∀ v∈activeParents D V u,∃ i∈commonOut D V u v,∃ j∈commonOut D V u v,
      absent D i j=true ∧ (commonOut D V i j).card≤k+(commonIn D (outN D V v) i j).card) :
    2*s*g≤(k-2)*(k-3) := by
  have total := Finset.sum_le_sum (fun u (hu : u∈V) => quadratic_cap (parent_pair_bill hf hm hu (test u hu)))
  rw [←Finset.mul_sum,Finset.sum_const_nat (fun _ _ => rfl)] at total
  change 2*edges D V (residual D V)≤V.card*((k-2)*(k-3)) at total
  have mass := endpoint_shortfall hf hm
  rw [←gap,Nat.mul_add] at mass
  apply Nat.le_of_mul_le_mul_left _ (Finset.card_pos.mpr ne)
  nlinarith only [mass,total]

#print axioms pair_transfer
#print axioms parent_pair_bill
#print axioms pair_bill_global

/-- Follow an active arc u→v to any of its common heads w. The two labelled
arcs u→v and v→w must have large combined banks. -/
theorem successor_pressure {D : CH.Digraph} {V : Finset ℕ} {s u v w}
    (hm : OutEq s D V) (hw : w∈commonOut D V u v) :
    s≤(endpoints D V u v).card+(commonOut D V v w).card := by
  have wV := (mem_outN.mp (Finset.mem_inter.mp hw).1).1
  have inc : outN D V w ⊆ endpoints D V u v∪commonOut D V v w := by
    intro z hz
    by_cases hit : z∈outN D V v
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hit,hz⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨(mem_outN.mp hz).1,hit,w,hw,(mem_outN.mp hz).2⟩)
  simpa only [hm w wV] using (Finset.card_le_card inc).trans (Finset.card_union_le _ _)

theorem arc_pressure_bound {D : CH.Digraph} {V : Finset ℕ} {s g m}
    (hf : QFree D V 3) (hm : OutEq s D V) (ne : V.Nonempty) (hs : 0<s)
    (gap : V.card+g=3*s+1) (ms : m≤s)
    (cap : ∀ u∈V,∀ v∈outN D V u,(commonOut D V u v).card≤m) :
    2*m*g≤(2*m-s)*(s-1) := by
  let f := residual D V
  let t := fun u v => (commonOut D V u v).card
  have row (u) (hu : u∈V) (v) (hv : v∈outN D V u) : m*f u v≤(2*m-s)*t u v := by
    by_cases pos : 0<f u v
    · have gp : 0<(commonOut D V u v).card-(endpoints D V u v).card := pos
      obtain ⟨w,hw⟩ := Finset.card_pos.mp (by omega : 0<(commonOut D V u v).card)
      have two := successor_pressure hm hw
      have next := cap v (mem_outN.mp hv).1 w (Finset.mem_inter.mp hw).2
      have first : t u v≤m := cap u hu v hv
      have fbound : f u v+s≤t u v+m := by change (commonOut D V u v).card-(endpoints D V u v).card+s≤(commonOut D V u v).card+m; omega
      have h2 : 2*m-s+s=2*m := by omega
      have dm : s-m+m=s := by omega
      have paid := Nat.mul_le_mul_left m fbound
      have use := Nat.mul_le_mul_left (s-m) first
      have e1 := congrArg (fun a => a*t u v) h2
      have e2 := congrArg (fun a => a*t u v) dm
      have e3 := congrArg (fun a => a*m) dm
      nlinarith only [paid,use,e1,e2,e3]
    · simp [show f u v=0 by omega]
  have total := Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (row u hu))
  simp only [←Finset.mul_sum] at total
  change m*edges D V f≤(2*m-s)*edges D V t at total
  let N := V.card*s
  have mass := endpoint_shortfall hf hm
  rw [←gap,Nat.mul_add] at mass
  have bill : N*g≤edges D V f := by dsimp only [N,f]; omega
  have capacity : 2*edges D V t+N≤N*s := common_head_capacity hf hm
  have use := Nat.mul_le_mul_left (2*m-s) capacity
  have start := Nat.mul_le_mul_left m bill
  have eq := congrArg (fun k : ℕ => (2*m-s)*N*k) (show s-1+1=s by omega)
  apply Nat.le_of_mul_le_mul_left _ (Nat.mul_pos (Finset.card_pos.mpr ne) hs : 0<N)
  change N*(2*m*g)≤N*((2*m-s)*(s-1))
  nlinarith only [total,use,start,eq]

/-- The arc cap is monotone under trimming, so this transition applies
directly to the user's original minimum-degree graph. -/
theorem cycle_of_arc_pressure {D : CH.Digraph} {n s m : ℕ} (hn : 0<n) (hs : 0<s)
    (ord : n≤3*s) (ms : m≤s) (price : (2*m-s)*(s-1)<2*m*(3*s+1-n))
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s)
    (cap : ∀ u∈Finset.range n,∀ v∈outN D (Finset.range n) u,
      (commonOut D (Finset.range n) u v).card≤m) : CH.HasDirectedCycleAtMost D n 3 := by
  by_contra no
  let V := Finset.range n
  have degree (x) (hx : x∈V) := Compose.FloorSix.out_card hm (Finset.mem_range.mp hx)
  obtain ⟨F,sub,reg⟩ := exists_outEq degree
  have lift (x) : outN F V x⊆outN D V x :=
    fun _ hz => mem_outN.mpr ⟨(mem_outN.mp hz).1,sub _ _ (mem_outN.mp hz).2⟩
  have localCap (u) (hu : u∈V) (v) (hv : v∈outN F V u) : (commonOut F V u v).card≤m :=
    (Finset.card_le_card (Finset.inter_subset_inter (lift u) (lift v))).trans (cap u hu v (lift u hv))
  have gap : V.card+(3*s+1-n)=3*s+1 := by simp only [V,Finset.card_range]; omega
  exact (Nat.not_lt_of_ge (arc_pressure_bound (qfree_sub sub (qfree_of_noShort hl no))
    reg ⟨0,Finset.mem_range.mpr hn⟩ hs gap ms localCap)) price

#print axioms arc_pressure_bound
#print axioms cycle_of_arc_pressure

/-- A surviving input has an actual arc with more than half (rounded up)
of the required degree in common heads, at every positive degree. -/
theorem large_arc_of_survival {D : CH.Digraph} {n s} (hn : 0<n) (hs : 0<s)
    (ord : n≤3*s) (hl : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s)
    (no : ¬CH.HasDirectedCycleAtMost D n 3) :
    ∃ u∈Finset.range n,∃ v∈outN D (Finset.range n) u,
      (s+1)/2<(commonOut D (Finset.range n) u v).card := by
  by_contra! cap
  let m := (s+1)/2
  have low : s≤2*m := by dsimp [m]; omega
  have high : 2*m-s≤1 := by dsimp [m]; omega
  have left := Nat.mul_le_mul_right (s-1) high
  have right := Nat.mul_le_mul_left (2*m) (show 1≤3*s+1-n by omega)
  apply no
  exact cycle_of_arc_pressure (m:=m) hn hs ord (by dsimp [m]; omega) (by omega) hl degree cap

def CheapPairOnEachActiveArc (D : CH.Digraph) (V : Finset ℕ) (k : ℕ) : Prop :=
  ∀ u∈V,∀ v∈activeParents D V u,∃ i∈commonOut D V u v,∃ j∈commonOut D V u v,
    absent D i j=true ∧ (commonOut D V i j).card≤k+(commonIn D (outN D V v) i j).card

theorem cycle_of_pair_test {D F : CH.Digraph} {n s k} (hn : 0<n) (ord : n≤3*s)
    (hl : CH.Loopless D n) (sub : ∀ x y,F x y=true → D x y=true) (reg : OutEq s F (Finset.range n))
    (test : CheapPairOnEachActiveArc F (Finset.range n) k)
    (price : (k-2)*(k-3)<2*s*(3*s+1-n)) : CH.HasDirectedCycleAtMost D n 3 := by
  by_contra no
  have gap : (Finset.range n).card+(3*s+1-n)=3*s+1 := by rw [Finset.card_range]; omega
  exact (Nat.not_lt_of_ge (pair_bill_global (qfree_sub sub (qfree_of_noShort hl no)) reg
    ⟨0,Finset.mem_range.mpr hn⟩ gap test)) price

#print axioms large_arc_of_survival
#print axioms cycle_of_pair_test

end LeanCH.BR.ShenSharedHead
