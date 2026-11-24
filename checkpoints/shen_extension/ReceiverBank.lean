import checkpoints.shen_extension.ReceiverTwoLoss

namespace LeanCH.BR.Closure.ReceiverRetry
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights

/-- Candidate middle labels of d → r → w with the same remaining cycle vertices P. -/
noncomputable def middles (D : CH.Digraph) (V P : Finset ℕ) (q d w : ℕ) : Finset ℕ := by
  classical exact (V \ P).filter (fun r => D d r = true ∧ D r w = true ∧ Cycle D V q (insert r P))

def protectsHeads (D : CH.Digraph) (V cut : Finset ℕ) (d : ℕ) : Prop :=
  ∀ v ∈ V \ cut, D d v = true → (outN D cut v).card ≤ 1

/-- A single deletion protects all surviving heads of d exactly when the
candidate picked for deletion has no incoming arc from another candidate. -/
theorem bank_iff {D V P q d w r} (hq : 2 ≤ q) (free : QFree D V q)
    (dp : d ∈ P) (wp : w ∈ P) (wd : w ≠ d) (rm : r ∈ middles D V P q d w) :
    protectsHeads D V ((insert r P).erase d) d ↔ ∀ v ∈ middles D V P q d w, D v r ≠ true := by
  classical
  obtain ⟨rv,dr,rw',ck⟩ := mem_filter.mp (show r ∈ (V \ P).filter _ from rm)
  have rp := (mem_sdiff.mp rv).2
  have rd : r ≠ d := fun eq => rp (eq ▸ dp)
  have wr : w ≠ r := fun eq => rp (eq ▸ wp)
  have rk : r ∈ insert r P := mem_insert_self _ _
  have dk : d ∈ insert r P := mem_insert_of_mem dp
  have wk : w ∈ insert r P := mem_insert_of_mem wp
  have rc := mem_erase.mpr ⟨rd,rk⟩
  have wc := mem_erase.mpr ⟨wd,wk⟩
  constructor
  · intro pay v vm vr
    obtain ⟨vv,dv,vw,_⟩ := mem_filter.mp (show v ∈ (V \ P).filter _ from vm)
    have ne : v ≠ r := fun eq => loopfree free (by omega) (mem_sdiff.mp rv).1 (eq ▸ vr)
    have out : v ∉ (insert r P).erase d := fun inc =>
      (mem_insert.mp (mem_of_mem_erase inc)).elim ne (mem_sdiff.mp vv).2
    have bound := pay v (mem_sdiff.mpr ⟨(mem_sdiff.mp vv).1,out⟩) dv
    exact wr (card_le_one.mp bound w (mem_outN.mpr ⟨wc,vw⟩) r (mem_outN.mpr ⟨rc,vr⟩))
  · intro light v outside dv
    by_contra! loss
    have vne : v ≠ d := fun eq => loopfree free (by omega) (ck.sub dk) (eq ▸ dv)
    have vk : v ∉ insert r P := fun inc => (mem_sdiff.mp outside).2 (mem_erase.mpr ⟨vne,inc⟩)
    have rich := loss.trans_le (card_le_card (show outN D ((insert r P).erase d) v ⊆ outN D (insert r P) v from
      fun _ h => mem_outN.mpr ⟨mem_of_mem_erase (mem_outN.mp h).1,(mem_outN.mp h).2⟩))
    obtain ⟨eq,_,cn⟩ := two_loss hq free ck dk rk wk dr rw' (mem_sdiff.mpr ⟨(mem_sdiff.mp outside).1,vk⟩) dv rich
    have vr := (mem_outN.mp (eq.symm ▸ (mem_insert_self r {w}))).2
    have vw := (mem_outN.mp (eq.symm ▸ (mem_insert_of_mem (mem_singleton_self w) : w ∈ ({r,w}:Finset ℕ)))).2
    have vm : v ∈ middles D V P q d w := mem_filter.mpr
      ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp outside).1,fun vp => vk (mem_insert_of_mem vp)⟩,dv,vw,by simpa [rp] using cn⟩
    exact light v vm vr

/-- Try every legal receiver on the same q-vertex bank. Either one cut
protects the feeder and all its surviving heads, or at least q+1 distinct
middle labels share the marked first and last vertex and have no source. -/
theorem bank_or_many {D V K q d z w} (hq : 2 ≤ q) (free : QFree D V q) (ck : Cycle D V q K)
    (dk : d ∈ K) (zk : z ∈ K) (wk : w ∈ K) (dz : D d z = true) (zw : D z w = true) :
    let P := K.erase z
    let J := middles D V P q d w
    (∃ r ∈ J, let cut := (insert r P).erase d
      cut.card = q ∧ d ∉ cut ∧ (outN D cut d).card = 1 ∧ protectsHeads D V cut d) ∨
    (q+1 ≤ J.card ∧ J ⊆ outN D V d ∩ inN D V w ∧ ∀ r ∈ J, ∃ v ∈ J, D v r = true) := by
  classical
  intro P J
  have dzn : d ≠ z := fun e => loopfree free (by omega) (ck.sub zk) (e ▸ dz)
  have wzn : w ≠ z := fun e => loopfree free (by omega) (ck.sub zk) (e ▸ zw)
  have wd : w ≠ d := by
    intro eq
    exact free d 2 (by decide) hq (.step (ck.sub zk) dz (.step (ck.sub dk) (eq ▸ zw) (.refl d)))
  have dp : d ∈ P := mem_erase.mpr ⟨dzn,dk⟩
  have wp : w ∈ P := mem_erase.mpr ⟨wzn,wk⟩
  have zJ : z ∈ J := mem_filter.mpr ⟨mem_sdiff.mpr ⟨ck.sub zk,by simp [P]⟩,dz,zw,by simpa [P,zk] using ck⟩
  by_cases has : ∃ r ∈ J, ∀ v ∈ J, D v r ≠ true
  · obtain ⟨r,rm,light⟩ := has
    obtain ⟨rv,dr,_,cr⟩ := mem_filter.mp (show r ∈ (V \ P).filter _ from rm)
    have rd : r ≠ d := fun e => (mem_sdiff.mp rv).2 (e ▸ dp)
    have dm : d ∈ insert r P := mem_insert_of_mem dp
    have heads : outN D ((insert r P).erase d) d = {r} := by
      ext i
      constructor
      · intro h
        exact mem_singleton.mpr (card_le_one.mp (cr.heads d dm).le i
          (mem_outN.mpr ⟨mem_of_mem_erase (mem_outN.mp h).1,(mem_outN.mp h).2⟩)
          r (mem_outN.mpr ⟨mem_insert_self _ _,dr⟩))
      · intro h
        obtain rfl := mem_singleton.mp h
        exact mem_outN.mpr ⟨mem_erase.mpr ⟨rd,mem_insert_self _ _⟩,dr⟩
    exact Or.inl ⟨r,rm,by rw [card_erase_of_mem dm,cr.size]; omega,by simp,
      by rw [heads,card_singleton],(bank_iff hq free dp wp wd rm).mpr light⟩
  · have sub : J ⊆ outN D V d ∩ inN D V w := by
      intro v vm
      obtain ⟨h,dv,vw,_⟩ := mem_filter.mp (show v ∈ (V \ P).filter _ from vm)
      exact mem_inter.mpr ⟨mem_outN.mpr ⟨(mem_sdiff.mp h).1,dv⟩,mem_inN.mpr ⟨(mem_sdiff.mp h).1,vw⟩⟩
    have jv : J ⊆ V := fun _ vm => (mem_outN.mp (mem_inter.mp (sub vm)).1).1
    have large : q < J.card := by
      by_contra! cap
      exact has (exists_sink (free.reverse.mono_set jv) ⟨z,zJ⟩ cap)
    push Not at has
    exact Or.inr ⟨large,sub,has⟩

#print axioms bank_iff
#print axioms bank_or_many
end LeanCH.BR.Closure.ReceiverRetry
