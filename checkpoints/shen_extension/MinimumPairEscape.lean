import checkpoints.shen_extension.RoutedPoolEscape

namespace LeanCH.BR.Closure.MinimumPairEscape
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShenCycleSuccessor ShortestCycleWeights
open MandatoryTwoStep EqualColumnRepair MandatoryExcursion BlockerHeadRouting

/-- Prescribe the minimum label as the sender by transferring one unit of
walk-length allowance from its mate. Routes into the mate then cost at most
one more arc than the shortest route. The deleted mass pays every parent
of the minimum label without any further order or credit hypothesis. -/
theorem from_equal_pair {q n} (X : Model q n) (hq : 2≤q) {h t}
    (hv : h∈X.V) (tv : t∈X.V) (ht : h≠t) (forward : Forces X.D X.V q h t)
    (back : Forces X.D X.V q t h) (minimum : ∀z∈X.V,X.weights h≤X.weights z)
    (size : q*(q-1)+1≤X.V.card) :
    let K : Finset ℕ := {h,t}
    ∃T⊆outN X.D (X.V\K) h,
      (∑y∈outN X.D (X.V\K) h\T,X.weights y)<X.weights h ∧
      (∀y∈T,∃r k,Blocks X K r t ∧ Walk X.D (X.V\K) y r k ∧
        span X.D X.V q h t ≤ k+2 ∧ k+2 ≤ span X.D X.V q h t+1) ∧
      ∃v∈(X.V\K)\T, X.D v h=false ∧
        X.weights h+X.weights t+(∑y∈T,X.weights y)<q*(∑y∈outN X.D T v,X.weights y) ∧
        ∀y∈outN X.D T v,∃C,Cycle X.D (X.V\K) q C ∧ v∈C ∧ y∈C := by
  classical
  intro K
  have hk : h∈K := mem_insert_self _ _
  have tk : t∈K := mem_insert_of_mem (mem_singleton_self _)
  have pair {z} (zk : z∈K) : z=h ∨ z=t := by simpa [K] using zk
  have sub : K⊆X.V := fun z zk => (pair zk).elim (fun eq => eq ▸ hv) (fun eq => eq ▸ tv)
  have many : 2≤K.card := one_lt_card.mpr ⟨h,hk,t,tk,ht⟩
  have equal (a) (ak : a∈K) (b) (bk : b∈K) : Forces X.D X.V q a b := by
    rcases pair ak with rfl|rfl <;> rcases pair bk with rfl|rfl
    · exact fun _ _ hit => hit
    · assumption
    · assumption
    · exact fun _ _ hit => hit
  obtain ⟨C,_,c,hc,_,_,_⟩ := ShortestReturnCertificate.on_model X hq hv
  have kc : K⊆C := fun z zk => equal h hk z zk C c hc
  let f (z : ℕ) := if z=t then 1 else 0
  have fh : f h=0 := by simp [f,ht]
  have ft : f t=1 := by simp [f]
  have diagonal {i z y p k} (ik : i∈K) (zk : z∈K) (ne : i≠z)
      (head : y∈outN X.D (X.V\K) i) (block : Blocks X K p i) (path : Walk X.D (X.V\K) y p k) :
      ∃d, 1 ≤ d ∧ d+f i≤k+1+f i ∧ Walk X.D X.V i i d := by
    obtain ⟨pos,bound,front,rev⟩ := segments (by omega : 1≤q) X.free c (kc ik) (kc zk)
    have strict : span X.D X.V q i z<q+1 := by
      by_contra! no
      have zero : q+1-span X.D X.V q i z=0 := by omega
      rw [zero] at rev
      cases rev
      exact ne rfl
    have depth : PuncturedDistance.depth X.D X.V i z=span X.D X.V q i z := by simp [span,ne]
    have pi : i∈outN X.D K p := block.2.2.1 ▸ mem_singleton_self _
    obtain ⟨dp,bd,w⟩ := excursion_bound (by omega : 1≤q) X.free c (kc ik) (kc ik) zk
      (equal i ik z zk) (by rw [depth]; omega) (by simpa only [span,ite_true,ite_eq_left rfl] using (depth ▸ strict))
      (mem_outN.mp head).1 (mem_outN.mp head).2 (mem_outN.mp pi).2 path
    exact ⟨_,dp,by omega,w.mono c.sub⟩
  have every : outN X.D (X.V\K) t⊆spareAt X K f t := by
    intro y yh
    refine mem_filter.mpr ⟨yh,?_⟩
    intro j jk p blk k path
    rcases pair jk with same|same
    · subst j
      have edge : h∈outN X.D K p := blk.2.2.1 ▸ mem_singleton_self _
      have orig : Walk X.D X.V t h (k+2) :=
        .step (mem_sdiff.mp (mem_outN.mp yh).1).1 (mem_outN.mp yh).2
          ((path.mono sdiff_subset).snoc hv (mem_outN.mp edge).2)
      exact ⟨k+2,by omega,by omega,orig⟩
    · subst j
      exact diagonal tk hk ht.symm yh blk path
  obtain ⟨_,x,b,_,thin⟩ := concentration_at X hq f sub hk many equal minimum size
  have xh : x=h := (pair b.2.1).resolve_right (fun eq => by
    subst x
    have cost := (class_data X hq sub hk many equal minimum size).2.1 t tk
    have room := sum_le_sum_of_subset_of_nonneg every (f:=X.weights) (by intros; omega)
    omega)
  subst x
  let O := outN X.D (X.V\K) h
  let S := spareAt X K f h
  let T := O\S
  have so : S⊆O := filter_subset _ _
  have cut : O\T=S := by
    ext y
    simp only [T,mem_sdiff]
    exact ⟨fun ⟨o,rest⟩ => by_contra (fun ns => rest ⟨o,ns⟩),fun s => ⟨so s,fun miss => miss.2 s⟩⟩
  have credit : q*X.weights h≤X.weights h+X.weights t+(∑z∈T,X.weights z) := by
    have split := sum_sdiff so (f:=X.weights)
    change (∑z∈T,X.weights z)+(∑z∈S,X.weights z)=∑z∈O,X.weights z at split
    have heads := (class_profile X hq sub hk equal minimum size).2 h hk
    change O=_ at heads
    rw [heads] at split
    change (∑z∈S,X.weights z)<X.weights h at thin
    have low := PunctureWeightCoverage.flow_floor X hv minimum size
    have decomp : (q-1)*X.weights h+X.weights h=q*X.weights h := by
      rw [←Nat.succ_mul]; congr 1; omega
    have tm := minimum t tv
    omega
  refine ⟨T,sdiff_subset,?_,?_,?_⟩
  · change (∑z∈O\T,X.weights z)<_
    rw [cut]; exact thin
  · intro y yt
    obtain ⟨yh,non⟩ := mem_sdiff.mp yt
    have no : ¬SpareAt X K f h y := fun yes => non (mem_filter.mpr ⟨yh,yes⟩)
    unfold SpareAt at no
    push Not at no
    obtain ⟨j,jk,r,block,k,path,no⟩ := no
    have jt : j=t := (pair jk).resolve_left (fun same => by
      subst j
      obtain ⟨d,dp,dc,w⟩ := diagonal hk tk ht yh block path
      exact no d dp dc w)
    subst j
    obtain ⟨dp,_,w,_⟩ := segments (by omega : 1≤q) X.free c hc (kc tk)
    have notle : ¬span X.D X.V q h t+f t≤k+1+f h := fun le => no _ dp le (w.mono c.sub)
    have edge : t∈outN X.D K r := block.2.2.1 ▸ mem_singleton_self _
    have orig : Walk X.D X.V h t (k+2) := .step (mem_sdiff.mp (mem_outN.mp yh).1).1 (mem_outN.mp yh).2
      ((path.mono sdiff_subset).snoc tv (mem_outN.mp edge).2)
    have lower := PuncturedDistance.depth_le_walk orig
    exact ⟨r,k,block,path,by simpa [span,ht] using lower,by omega⟩
  · obtain ⟨v,vt,vh,cost,cycles⟩ := RoutedPoolEscape.bank_escape X hq sub hk many hk tk ht equal minimum size
      (T:=T) sdiff_subset credit
    have high := nat_strict.mp X.strict v (mem_sdiff.mp (mem_sdiff.mp vt).1).1
    exact ⟨v,vt,vh,by omega,cycles⟩

/-- At the minimum, a head set of mass strictly below w(h) is empty.
Consequently every actual head of h has a near-shortest route to a blocking
parent of the prescribed mate t. One outside row captures a strict weighted
share of this entire head set. Its used arcs survive on shortest cycles even
after deleting every label that forces h. -/
theorem all_heads {q n} (X : Model q n) (hq : 2≤q) {h t}
    (hv : h∈X.V) (tv : t∈X.V) (ht : h≠t) (forward : Forces X.D X.V q h t)
    (back : Forces X.D X.V q t h) (minimum : ∀z∈X.V,X.weights h≤X.weights z)
    (size : q*(q-1)+1≤X.V.card) :
    let K : Finset ℕ := {h,t}
    let H := outN X.D X.V h
    (∀y∈H,∃r k,Blocks X K r t ∧ Walk X.D (X.V\K) y r k ∧
        span X.D X.V q h t ≤ k+2 ∧ k+2 ≤ span X.D X.V q h t+1) ∧
    ∃v∈(X.V\K)\H, X.D v h=false ∧
        X.weights h+X.weights t+(∑y∈H,X.weights y)<q*(∑y∈outN X.D H v,X.weights y) ∧
        ∀B : Finset ℕ,(∀z∈B,Forces X.D X.V q z h) →
          ∀y∈outN X.D H v,∃C,Cycle X.D (X.V\B) q C ∧ v∈C ∧ y∈C := by
  classical
  intro K H
  obtain ⟨T,sub,thin,route,v,vt,vh,capture,_⟩ := from_equal_pair X hq hv tv ht forward back minimum size
  have hk : h∈K := mem_insert_self _ _
  have tk : t∈K := mem_insert_of_mem (mem_singleton_self _)
  have pair {z} (zk : z∈K) : z=h ∨ z=t := by simpa [K] using zk
  have kv : K⊆X.V := fun z zk => (pair zk).elim (fun eq => eq ▸ hv) (fun eq => eq ▸ tv)
  have equal (a) (ak : a∈K) (b) (bk : b∈K) : Forces X.D X.V q a b := by
    rcases pair ak with rfl|rfl <;> rcases pair bk with rfl|rfl
    · exact fun _ _ hit => hit
    · assumption
    · assumption
    · exact fun _ _ hit => hit
  have heads := (class_profile X hq kv hk equal minimum size).2 h hk
  change outN X.D (X.V\K) h=H at heads
  change T⊆outN X.D (X.V\K) h at sub
  change (∑y∈outN X.D (X.V\K) h\T,X.weights y)<_ at thin
  rw [heads] at sub thin
  have eq : T=H := Subset.antisymm sub (by
    intro y yh
    by_contra miss
    have outside := mem_sdiff.mpr (show y∈H ∧ y∉T from ⟨yh,miss⟩)
    have single := single_le_sum (f:=X.weights) (fun _ _ => Nat.zero_le _) outside
    have floor := minimum y (mem_outN.mp yh).1
    omega)
  subst T
  refine ⟨route,v,vt,vh,capture,?_⟩
  intro B force y yh
  obtain ⟨yh',vy⟩ := mem_outN.mp yh
  obtain ⟨yv,hy⟩ := mem_outN.mp yh'
  have vout := mem_sdiff.mp (mem_sdiff.mp vt).1
  have ne : v≠h := fun eq => vout.2 (by rw [eq]; exact hk)
  exact RoutedPoolEscape.shared_head_escape X hq vout.1 yv ne hy vy force

#print axioms all_heads
#print axioms from_equal_pair
end LeanCH.BR.Closure.MinimumPairEscape
