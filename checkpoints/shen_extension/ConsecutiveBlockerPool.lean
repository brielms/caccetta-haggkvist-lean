import checkpoints.shen_extension.BlockerHeadRouting
import checkpoints.shen_extension.MandatoryExcursion

namespace LeanCH.BR.Closure.ConsecutiveBlockerPool
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShenCycleSuccessor ShortestCycleWeights
open MandatoryTwoStep EqualColumnRepair MandatoryExcursion BlockerHeadRouting

theorem same_end {D V q C u v d} (c : Cycle D V q C) (uc : u∈C)
    (path : Walk D C u v d) {z} (other : Walk D C u z d) : v=z := by
  induction path generalizing z with
  | refl => cases other; rfl
  | step bc ub _ ih =>
    cases other with
    | step ec ue tail =>
      obtain rfl := card_le_one.mp (c.heads _ uc).le _ (mem_outN.mpr ⟨bc,ub⟩) _ (mem_outN.mpr ⟨ec,ue⟩)
      exact ih bc tail

/-- Almost all retained head weight of some blocking anchor x is routed to
blocking parents of one fixed, different class member j. The same j works
for every charged head, independently of its weight and of the witnessing
parent. The shortest lengths are measured in the full source. -/
theorem consecutive_pool {q n} (X : Model q n) (hq : 2≤q) {K : Finset ℕ} {h}
    (sub : K⊆X.V) (hk : h∈K) (many : 2≤K.card)
    (equal : ∀x∈K,∀y∈K,Forces X.D X.V q x y)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (size : q*(q-1)+1≤X.V.card) :
    ∃p x j, Blocks X K p x ∧ j∈K ∧ j≠x ∧
      (∀v∈K,span X.D X.V q x j≤span X.D X.V q x v) ∧
      (∑y∈spareHeads X K x,X.weights y)<X.weights x ∧
      score q X.D X.V X.weights p + (∑z∈K,X.weights z)+q*(∑y∈spareHeads X K x,X.weights y)
        ≤ (∑z∈X.V,X.weights z)+q*X.weights x ∧
      (outN X.D (X.V\K) x\spareHeads X K x).Nonempty ∧
      ∀y∈outN X.D (X.V\K) x\spareHeads X K x,∃r k,Blocks X K r j ∧
        Walk X.D (X.V\K) y r k ∧ k+2=span X.D X.V q x j := by
  classical
  obtain ⟨p,x,bx,loss,cap⟩ := concentration X hq sub hk many equal minimum size
  have xk := bx.2.1
  obtain ⟨C,_,c,xc,_,_,_⟩ := ShortestReturnCertificate.on_model X hq (sub xk)
  have kc : K⊆C := fun z zk => equal x xk z zk C c xc
  let dist := span X.D X.V q x
  obtain ⟨j,jk,best⟩ := K.exists_min_image dist ⟨x,xk⟩
  have part (v) (vk : v∈K) := segments (by omega : 1≤q) X.free c xc (kc vk)
  have jx : j≠x := by
    intro eq
    subst j
    obtain ⟨z,zk,ne⟩ := exists_mem_ne (s:=K) (a:=x) (by omega)
    have small := best z zk
    obtain ⟨_,ub,_,reverse⟩ := part z zk
    change span X.D X.V q x x≤span X.D X.V q x z at small
    simp only [span] at small
    have zero : q+1-span X.D X.V q x z=0 := by
      change q+1≤span X.D X.V q x z at small
      omega
    rw [zero] at reverse
    cases reverse
    exact ne rfl
  have positive : 0<PuncturedDistance.depth X.D X.V x j := by
    have s := (part j jk).1
    simpa [span,Ne.symm jx] using (show 0<span X.D X.V q x j by omega)
  have nonempty : (outN X.D (X.V\K) x\spareHeads X K x).Nonempty := by
    by_contra no
    have le := sdiff_eq_empty_iff_subset.mp (not_nonempty_iff_eq_empty.mp no)
    have small := sum_le_sum_of_subset_of_nonneg le (f:=X.weights) (by intros; omega)
    have actual := (class_data X hq sub hk many equal minimum size).2.1 x xk
    omega
  refine ⟨p,x,j,bx,jk,jx,best,cap,loss,nonempty,?_⟩
  intro y charged
  obtain ⟨head,used⟩ := mem_sdiff.mp charged
  obtain ⟨v,vk,r,block,k,path,full,least⟩ := routed X sub head used
  have rv : v∈outN X.D K r := block.2.2.1 ▸ mem_singleton_self _
  have lo := best v vk
  have eq : dist j=dist v := by
    by_contra ne
    have between : PuncturedDistance.depth X.D X.V x j<span X.D X.V q x v := by
      have rr : dist j=PuncturedDistance.depth X.D X.V x j := by simp [dist,span,Ne.symm jx]
      change span X.D X.V q x j≤span X.D X.V q x v at lo
      change span X.D X.V q x j≠span X.D X.V q x v at ne
      dsimp only [dist] at rr
      omega
    obtain ⟨pos,bd,walk⟩ := excursion_bound (by omega : 1≤q) X.free c xc (kc vk) jk
      (equal x xk j jk) positive between (mem_outN.mp head).1 (mem_outN.mp head).2 (mem_outN.mp rv).2 path
    have lower := least _ pos (walk.mono c.sub)
    omega
  obtain ⟨_,_,fj,_⟩ := part j jk
  obtain ⟨vp,_,fv,_⟩ := part v vk
  change span X.D X.V q x j=span X.D X.V q x v at eq
  have same : j=v := same_end c xc fj (eq.symm ▸ fv)
  subst v
  have lb := least _ vp (fv.mono c.sub)
  have ub := PuncturedDistance.depth_le_walk full
  rw [←(show span X.D X.V q x j=PuncturedDistance.depth X.D X.V x j by simp [span,Ne.symm jx])] at ub
  exact ⟨r,k,block,path,by omega⟩

/-- Any chosen set of pivots separated by intervening mandatory labels
can be bypassed together. A different class head still has to block. -/
theorem nonconsecutive_pivots {q n} (X : Model q n) (hq : 2≤q) {K J : Finset ℕ} {h}
    (sub : K⊆X.V) (hk : h∈K) (many : 2≤K.card) (jk : J⊆K)
    (equal : ∀x∈K,∀y∈K,Forces X.D X.V q x y)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (size : q*(q-1)+1≤X.V.card)
    (separated : ∀i∈J,∀j∈J,∃z∈K,0<PuncturedDistance.depth X.D X.V i z ∧
      PuncturedDistance.depth X.D X.V i z<span X.D X.V q i j) :
    ∃p x,x∉J ∧ Blocks X K p x := by
  obtain ⟨C,_,c,hc,_,_,_⟩ := ShortestReturnCertificate.on_model X hq (sub hk)
  apply MultiPivotRepair.recurrent_blocker X hq sub hk many jk equal minimum size
  exact independent_excursions (by omega : 1≤q) X.free c (fun x xk => equal h hk x xk C c hc)
    jk (fun i ij => equal i (jk ij)) separated

#print axioms nonconsecutive_pivots
#print axioms consecutive_pool
end LeanCH.BR.Closure.ConsecutiveBlockerPool
