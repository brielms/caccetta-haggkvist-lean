import checkpoints.shen_extension.SquareFiberPressure

namespace LeanCH.BR.Closure.MarkedSquareFrontier
open Finset BRq2 BRq3 BR45 ShortestCycleWeights ShenCycleSuccessor CycleSquareTensor

/-- Actual replacement arcs u(i) → v(i) carry a circulation on original labels.
Consequently a nonempty closed shift sequence moves at least q+1 different labels. -/
theorem active_labels {D W q} (hq : 1≤q) (free : QFree D W q) (M : ℕ→Finset ℕ)
    (a u v b : ℕ→ℕ) (l : ℕ) (live : 0<l) (closed : M l=M 0)
    (cycle : ∀i,Cycle D W q (M i)) (move : ∀i,Shift D (M i) (M (i+1)) (a i) (u i) (v i) (b i)) :
    (range l).image u=(range l).image v ∧ q+1≤((range l).image u).card ∧ q+1≤l := by
  classical
  have hits (x : ℕ) : (∑i∈range l,if v i=x then (1:ℤ) else 0)=
      ∑i∈range l,if u i=x then (1:ℤ) else 0 := by
    have e := CycleSquareBalance.closed_balance hq free M a u v b l closed cycle move
      (fun k _ => if k=x then (1:ℤ) else 0)
    simp only [sum_add_distrib] at e
    omega
  have seen (g : ℕ→ℕ) (x : ℕ) : x∈(range l).image g ↔ 0<(∑i∈range l,if g i=x then (1:ℤ) else 0) := by
    simp only [sum_boole, Int.natCast_pos,card_pos,Finset.Nonempty,mem_image,mem_filter]
  have same : (range l).image u=(range l).image v := by
    ext x
    rw [seen,seen,hits x]
  let S := (range l).image u
  have sub : S⊆W := by
    rintro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact (cycle i).sub (move i).uM
  have deg (x) (hx : x∈S) : 1≤(outN D S x).card := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    exact card_pos.mpr ⟨v i,mem_outN.mpr ⟨by change v i∈(range l).image u; rw [same]; exact mem_image_of_mem v hi,(move i).move⟩⟩
  have size := dt_size hq (ball_q_one q hq) (free.mono_set sub) deg
    (show S.Nonempty from ⟨u 0,mem_image_of_mem u (mem_range.mpr live)⟩)
  have cap : S.card≤l := (card_image_le.trans (card_range l).le)
  exact ⟨same,by simpa using size,by simpa using size.trans cap⟩

def ReceiverAlternative {q n} (X : Model q n) : Prop :=
  ∀h∈X.V,(∀x∈X.V,X.weights h≤X.weights x) → ∀M,Cycle X.D (X.V\{h}) q M →
    X.V.card≤q*(inN X.D M h).card ∨ ∃v∈(X.V\{h})\M,2≤(inN X.D M v).card ∧
      (outN X.D M v=∅ ∨ ∃a u b N, Shift X.D M N a u v b ∧ Cycle X.D (X.V\{h}) q N ∧
        inN X.D M v={a,u} ∧ outN X.D M v={b})

theorem receiver {q n} (X : Model q n) (hq : 2≤q) : ReceiverAlternative X := by
  classical
  intro h hv minimum M c
  rcases MinimumPunctureIncidence.receiver X hq hv minimum c with small | ⟨v,vw,high⟩
  · exact Or.inl small
  refine Or.inr ⟨v,vw,high,?_⟩
  rcases (outN X.D M v).eq_empty_or_nonempty with none | ⟨b,bh⟩
  · exact Or.inl none
  obtain ⟨a,u,N,e,cn,p,t⟩ := replacement hq (X.free.mono_set sdiff_subset) c vw high
    (mem_outN.mp bh).1 (mem_outN.mp bh).2
  exact Or.inr ⟨a,u,b,N,e,cn,p,t⟩

/-- An edge of the state graph retains its four witnesses. -/
def Edge (D : CH.Digraph) (W : Finset ℕ) (q : ℕ) (M N : Finset ℕ) : Prop :=
  Cycle D W q N ∧ ∃a u v b,Shift D M N a u v b

/-- Starting at any supplied shortest cycle in a sufficiently large minimum
puncture, either a reachable cycle has a receiver with no return, or there
is a reachable closed shift sequence moving at least q+1 original labels. -/
theorem from_cycle {q n} (X : Model q n) (hq : 2≤q) (large : q*(q+1)<X.V.card)
    {h seed} (hv : h∈X.V) (minimum : ∀x∈X.V,X.weights h≤X.weights x)
    (start : Cycle X.D (X.V\{h}) q seed) :
    let W := X.V\{h}
    let reach := Relation.ReflTransGen (Edge X.D W q) seed
    (∃M,reach M ∧ Cycle X.D W q M ∧ ∃v∈W\M,2≤(inN X.D M v).card ∧ outN X.D M v=∅) ∨
    ∃(M : ℕ→Finset ℕ) (a u v b : ℕ→ℕ) (l : ℕ), M l=M 0 ∧
      (∀i,reach (M i) ∧ Cycle X.D W q (M i) ∧ Shift X.D (M i) (M (i+1)) (a i) (u i) (v i) (b i)) ∧
      (range l).image u=(range l).image v ∧ q+1≤((range l).image u).card ∧ q+1≤l := by
  classical
  intro W reach
  by_cases stop : ∃M,reach M ∧ Cycle X.D W q M ∧ ∃v∈W\M,2≤(inN X.D M v).card ∧ outN X.D M v=∅
  · exact Or.inl stop
  apply Or.inr
  let family := W.powerset.filter (fun M => reach M ∧ Cycle X.D W q M)
  have init : seed∈family := mem_filter.mpr ⟨mem_powerset.mpr start.sub,.refl,start⟩
  have step (M) (mf : M∈family) : ∃N∈family,∃a u v b,Shift X.D M N a u v b := by
    obtain ⟨_,r,c⟩ := mem_filter.mp mf
    rcases receiver X hq h hv minimum M c with small | ⟨v,vw,hi,none | ⟨a,u,b,N,e,d,_,_⟩⟩
    · have bound : (inN X.D M h).card≤q+1 := c.size ▸ card_le_card (filter_subset _ _)
      exact False.elim (large.not_ge (small.trans (Nat.mul_le_mul_left _ bound)))
    · exact False.elim (stop ⟨M,r,c,v,vw,hi,none⟩)
    · exact ⟨N,mem_filter.mpr ⟨mem_powerset.mpr d.sub,r.tail (show Edge X.D W q M N from ⟨d,a,u,v,b,e⟩),d⟩,a,u,v,b,e⟩
  choose! g gf a u v b ge using step
  let F (i : ℕ) := g^[i] seed
  have fm (i) : F i∈family := by
    induction i with
    | zero => exact init
    | succ i ih => simpa only [F,Function.iterate_succ_apply'] using gf _ ih
  have fe (i) : Shift X.D (F i) (F (i+1)) (a (F i)) (u (F i)) (v (F i)) (b (F i)) := by
    simpa only [F,Function.iterate_succ_apply'] using ge _ (fm i)
  obtain ⟨i,_,j,_,ne,eq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
    (s:=range (family.card+1)) (t:=family) (f:=F) (by simp) (fun k _ => fm k)
  obtain ⟨i,j,lt,eq⟩ : ∃i j,i<j ∧ F j=F i := by
    rcases Nat.lt_or_gt_of_ne ne with lt | lt
    · exact ⟨i,j,lt,eq.symm⟩
    · exact ⟨j,i,lt,eq⟩
  let M (t) := F (i+t)
  have endeq : M (j-i)=M 0 := by simpa [M,show i+(j-i)=j by omega] using eq
  have e (t) : Shift X.D (M t) (M (t+1)) (a (M t)) (u (M t)) (v (M t)) (b (M t)) := by
    simpa [M,Nat.add_assoc] using fe (i+t)
  have rc (t) : reach (M t) ∧ Cycle X.D W q (M t) := (mem_filter.mp (fm (i+t))).2
  exact ⟨M,a ∘ M,u ∘ M,v ∘ M,b ∘ M,j-i,endeq,(fun t => ⟨(rc t).1,(rc t).2,e t⟩),
    active_labels (by omega) (X.free.mono_set sdiff_subset) M _ _ _ _ _ (by omega) endeq
      (fun t => (rc t).2) e⟩

#print axioms from_cycle
#print axioms active_labels
#print axioms receiver
end LeanCH.BR.Closure.MarkedSquareFrontier
