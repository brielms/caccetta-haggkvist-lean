import checkpoints.shen_extension.SharedArcFlatTransport
import LeanCH.BR.BRSerialChain

namespace LeanCH.BR.Closure.SingleArcReturnProfile
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling

private theorem split_walk {V : Finset ℕ} {D E : CH.Digraph} {a b x y n : ℕ}
    (only : ∀ i ∈ V, ∀ j ∈ V, D i j=true → E i j=true ∨ (i=a ∧ j=b))
    (w : Walk D V x y n) (hx : x∈V) :
    Walk E V x y n ∨ ∃ t<n, Walk D V x a t := by
  induction w with
  | refl x => exact Or.inl (.refl x)
  | @step x z y k hz ed _ ih =>
    rcases only x hx z hz ed with old | ⟨rfl,_⟩
    · rcases ih hz with rest | ⟨t,lt,path⟩
      · exact Or.inl (.step hz old rest)
      · exact Or.inr ⟨t+1,by omega,.step hz ed path⟩
    · exact Or.inr ⟨0,by omega,.refl _⟩

/-- Old forward short-ball size plus old indegree. Its deficit from the
order counts the safe missing arcs that end at the root. -/
noncomputable def profile (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (x : ℕ) :=
  (ball E V x (q-1)).card + (inN E V x).card

/-- Every native successor of the edited tail retains its entire ball
through radius q. At radius q-1 its complement is its native in-neighborhood. -/
theorem balls {D E : CH.Digraph} {V : Finset ℕ} {q a b : ℕ} (hq : 1 ≤ q)
    (free : QFree D V q) (sat : BRsub.Sat q D V)
    (sub : ∀ i j, E i j=true → D i j=true)
    (only : ∀ i ∈ V, ∀ j ∈ V, D i j=true → E i j=true ∨ (i=a ∧ j=b))
    {v : ℕ} (hv : v∈V) (av : D a v=true) :
    (∀ t ≤ q, ball E V v t = ball D V v t) ∧
      ball E V v (q-1) = V \ inN D V v := by
  have same (t : ℕ) (ht : t≤q) : ball E V v t = ball D V v t := by
    apply Subset.antisymm (ball_sub sub)
    intro k hk
    obtain ⟨kv,l,lo,path⟩ := mem_ball.mp hk
    rcases split_walk only path hv with old | ⟨s,ls,back⟩
    · exact mem_ball.mpr ⟨kv,l,lo,old⟩
    · exact (free a _ (by omega) (by omega) (.step hv av back)).elim
  refine ⟨same,?_⟩
  rw [same _ (by omega)]
  ext k
  constructor
  · intro h
    obtain ⟨kv,s,lo,path⟩ := mem_ball.mp h
    exact mem_sdiff.mpr ⟨kv,fun inc => free k _ (by omega) (by omega)
      (.step hv (mem_inN.mp inc).2 path)⟩
  · intro h
    obtain ⟨kv,off⟩ := mem_sdiff.mp h
    exact sat v hv k kv (fun ed => off (mem_inN.mpr ⟨kv,ed⟩))

private theorem jump {D E : CH.Digraph} {V : Finset ℕ} {q : ℕ} (hq : 1≤q)
    (free : QFree D V q) (sat : BRsub.Sat q D V) (a b : V)
    (ab : D a b=true) (off : E a b=false) (sub : ∀ i j, E i j=true → D i j=true)
    (only : ∀ i ∈ V, ∀ j ∈ V, D i j=true → E i j=true ∨ (i=a.val ∧ j=b.val)) :
    profile q E V b + 1 = V.card ∧ ∀ v : V, E a v=true → profile q E V v = V.card := by
  have cut (v : V) (av : D a v=true) :
      (ball E V v (q-1)).card + (inN D V v).card = V.card := by
    rw [(balls hq free sat sub only v.property av).2]
    exact card_sdiff_add_card_eq_card (filter_subset _ _)
  have ins : inN D V b = insert a.val (inN E V b) := by
    ext k
    constructor
    · intro hit
      obtain ⟨kv,ed⟩ := mem_inN.mp hit
      rcases only k kv b b.property ed with old | same
      · exact mem_insert_of_mem (mem_inN.mpr ⟨kv,old⟩)
      · exact mem_insert.mpr (.inl same.1)
    · intro hit
      rcases mem_insert.mp hit with rfl | h
      · exact mem_inN.mpr ⟨a.property,ab⟩
      · exact mem_inN.mpr ⟨(mem_inN.mp h).1,sub _ _ (mem_inN.mp h).2⟩
  have h := cut b ab
  rw [ins,card_insert_of_notMem (fun h => Bool.noConfusion (off.symm.trans (mem_inN.mp h).2))] at h
  refine ⟨by unfold profile; omega,?_⟩
  intro v av
  have ne : v.val ≠ b.val := by rintro e; exact Bool.noConfusion (off.symm.trans (e ▸ av))
  have same : inN D V v = inN E V v := by
    ext k
    simp only [mem_inN]
    constructor
    · rintro ⟨kv,ed⟩
      exact ⟨kv,(only k kv v v.property ed).resolve_right (fun pair => ne pair.2)⟩
    · rintro ⟨kv,ed⟩; exact ⟨kv,sub _ _ ed⟩
  simpa only [profile,←same] using cut v (sub _ _ av)

/-- For a singleton native insertion, both orientations have a jump of
exactly one, at every old successor and every old predecessor respectively. -/
theorem at_singleton {q n} (X : Model q n) (hq : 1≤q) (F : Family)
    (f : SharedArcFlatCut.Missing X F) (single : ∀ g : SharedArcFlatCut.Missing X F, g=f) :
    let E := graph X.D F
    let a := f.val.1
    let b := f.val.2
    (profile q E X.V b + 1 = X.V.card ∧
      ∀ v : X.V, E a v=true → profile q E X.V v = X.V.card) ∧
    (profile q (fun i j => E j i) X.V a + 1 = X.V.card ∧
      ∀ k : X.V, E k b=true → profile q (fun i j => E j i) X.V k = X.V.card) := by
  intro E a b
  have sub (i j) (ed : E i j=true) : X.D i j=true := by
    obtain ⟨_,h⟩ := active.mp ed; exact (mem_col.mp h).2.2.2
  have only (i) (hi : i∈X.V) (j) (hj : j∈X.V) (ed : X.D i j=true) :
      E i j=true ∨ (i=a.val ∧ j=b.val) := by
    by_cases old : E i j=true
    · exact Or.inl old
    · let g : SharedArcFlatCut.Missing X F :=
        ⟨(⟨i,hi⟩,⟨j,hj⟩),ed,Bool.eq_false_iff.mpr old⟩
      exact Or.inr ⟨congrArg (fun t : SharedArcFlatCut.Missing X F => t.val.1.val) (single g),
        congrArg (fun t : SharedArcFlatCut.Missing X F => t.val.2.val) (single g)⟩
  exact ⟨jump hq X.free X.sat a b f.property.1 f.property.2 sub only,
    jump (D:=fun i j => X.D j i) (E:=fun i j => E j i) hq X.free.reverse
      (SerialChain.sat_reverse X.sat) b a f.property.1 f.property.2 (fun _ _ => sub _ _)
      (fun i hi j hj ed => (only j hj i hi ed).imp_right And.symm)⟩

/-- Failure of either one-unit jump supplies a second actual native arc
outside the old family, without knowing the degrees or the flat laws. -/
theorem second_arc {q n} (X : Model q n) (hq : 1≤q) (F : Family)
    (f : SharedArcFlatCut.Missing X F)
    (fail : let E := graph X.D F
            let a := f.val.1
            let b := f.val.2
            (∃ v : X.V, E a v=true ∧ profile q E X.V v ≠ profile q E X.V b + 1) ∨
            (∃ k : X.V, E k b=true ∧ profile q (fun i j => E j i) X.V k ≠
              profile q (fun i j => E j i) X.V a + 1)) :
    ∃ g : SharedArcFlatCut.Missing X F, g≠f := by
  classical
  by_contra! single
  obtain ⟨⟨head,successors⟩,⟨tail,parents⟩⟩ := at_singleton X hq F f single
  rcases fail with ⟨v,av,bad⟩ | ⟨k,kb,bad⟩
  · exact bad ((successors v av).trans head.symm)
  · exact bad ((parents k kb).trans tail.symm)

end LeanCH.BR.Closure.SingleArcReturnProfile
#print axioms LeanCH.BR.Closure.SingleArcReturnProfile.balls
#print axioms LeanCH.BR.Closure.SingleArcReturnProfile.at_singleton
#print axioms LeanCH.BR.Closure.SingleArcReturnProfile.second_arc
