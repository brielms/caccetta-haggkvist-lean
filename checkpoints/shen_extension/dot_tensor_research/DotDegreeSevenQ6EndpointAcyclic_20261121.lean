import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ6SpillBanks_20261121
import LeanCH.BR.BRFiniteWalk
import LeanCH.BR.BRNearBoundaryRows

namespace LeanCH.BR.DotDegreeSevenQ6
open Finset BRq2 BRq3 BR45 BRsGen

def BankSink (D : CH.Digraph) (A : Finset ℕ) (a : ℕ) : Prop :=
  ∀ z∈A, D a z ≠ true

/-- The same shortest sink path yields distinct labels outside the receiver set. -/
theorem sink_far_set_card {D : CH.Digraph} {A R : Finset ℕ} {j : ℕ}
    (hf : QFree D A 7) (cA : A.card=7) (hR : R⊆A)
    (ban : ∀ a∈R, ∀ z∈A, BankSink D A z → ∀ k≤j, ¬ Walk D A a z k) :
    R.card=0 ∨ R.card+j+1≤7 := by
  classical
  by_cases H : R.card=0
  · exact Or.inl H
  right
  obtain ⟨a,ha⟩ := card_pos.mp (show 0<R.card by omega)
  obtain ⟨p⟩ := exists_shortest_sink_path hf (by omega : A.card≤7) (hR ha)
  have L : j+1≤p.len := by
    by_contra! sm
    have w := p.walk (Nat.zero_le p.len) le_rfl
    rw [p.start,Nat.sub_zero] at w
    exact ban a ha (p.vertex p.len) (p.mem _ le_rfl) p.sink p.len (by omega) w
  let I := (range (p.len+1)).filter (fun i => p.len - j ≤ i)
  have Ic : I.card=j+1 := by
    have eq : I = range (p.len+1) \ range (p.len-j) := by
      ext i
      simp only [I,mem_filter,mem_range,mem_sdiff]
      omega
    rw [eq]
    have h := card_sdiff_add_card_eq_card
      (range_mono (show p.len-j≤p.len+1 by omega))
    simp only [card_range] at h
    omega
  have images : (I.image p.vertex).card=j+1 := by
    rw [card_image_of_injOn, Ic]
    exact (p.injective hf (by omega)).mono (fun _ hi => (mem_filter.mp hi).1)
  have imagesSub : I.image p.vertex ⊆ A \ R := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    obtain ⟨hi,lo⟩ := mem_filter.mp hi
    have il : i≤p.len := Nat.le_of_lt_succ (mem_range.mp hi)
    exact mem_sdiff.mpr ⟨p.mem _ il,fun hr =>
      ban _ hr _ (p.mem _ le_rfl) p.sink (p.len-i) (by omega) (p.walk il le_rfl)⟩
  have count := card_le_card imagesSub
  have cd := card_sdiff_add_card_eq_card hR
  omega

#print axioms sink_far_set_card
end LeanCH.BR.DotDegreeSevenQ6


namespace LeanCH.BR.DotDegreeSevenQ6
open Finset BRq2 BRq3 BR45 BRsGen

noncomputable def BackPool (D : CH.Digraph) (B : Finset ℕ) (x : ℕ) : Finset ℕ := by
  classical
  exact B.filter (fun b => ∃ y∈B, D y x=true ∧ y∈ball D B b 4)

theorem no_return_of_acyclic_first_bank {D : CH.Digraph} {V A B T : Finset ℕ}
    (hf : QFree D V 6) (he : OutEq 7 D V) (hA : A⊆V) (hB : B⊆V)
    (cA : A.card=7) (cB : B.card=7) (cT : T.card=6)
    (acyc : QFree D A 7)
    (keepA : ∀ a∈A, outN D V a⊆A∪B)
    (keepB : ∀ b∈B, outN D V b⊆(A∪B)∪T) :
    ∀ b∈B, ∀ x∈A, D b x ≠ true := by
  classical
  let R := A.filter (fun x => ∃ b∈B, D b x=true)
  have hR : R⊆A := filter_subset _ _
  have sinkHeads (z) (hz : z∈A) (hs : BankSink D A z) :
      ∀ b∈B, D z b=true := by
    have sub : outN D V z ⊆ B := by
      intro t ht
      exact (mem_union.mp (keepA z hz ht)).resolve_left (fun h => hs t h (mem_outN.mp ht).2)
    have eq := eq_of_subset_of_card_le sub (by rw [he z (hA hz),cB])
    intro b hb
    exact (mem_outN.mp (eq ▸ hb)).2
  have ban (x) (hx : x∈R) (z) (hz : z∈A) (hs : BankSink D A z) (k) (hk : k≤4) :
      ¬ Walk D A x z k := by
    intro w
    obtain ⟨b,hb,edge⟩ := (mem_filter.mp hx).2
    exact hf x (k+1+1) (by omega) (by omega)
      (((w.mono hA).snoc (hB hb) (sinkHeads z hz hs b hb)).snoc (hA (hR hx)) edge)
  have rcap : R.card≤2 := by
    rcases sink_far_set_card acyc cA hR ban with h|h <;> omega
  have five (x) (hx : x∈R) : 5 ≤ (outN D B x).card := by
    have hsubset : outN D A x ⊆ A := fun _ h => (mem_outN.mp h).1
    have no (a) (ha : a∈outN D A x) (z) (hz : z∈A) (hs : BankSink D A z)
        (k) (hk : k≤3) : ¬ Walk D A a z k := by
      intro w
      exact ban x hx z hz hs (k+1) (by omega)
        (.step (hsubset ha) (mem_outN.mp ha).2 w)
    have hcap : (outN D A x).card≤3 := by
      rcases sink_far_set_card acyc cA hsubset no with h|h <;> omega
    have sub : outN D V x ⊆ outN D A x ∪ outN D B x := by
      intro t ht
      rcases mem_union.mp (keepA x (hR hx) ht) with h|h
      · exact mem_union_left _ (mem_outN.mpr ⟨h,(mem_outN.mp ht).2⟩)
      · exact mem_union_right _ (mem_outN.mpr ⟨h,(mem_outN.mp ht).2⟩)
    -- At most three first-bank heads gives four second-bank heads absent one more
    -- excluded label. The row itself is also not a head, and has distance ≥5.
    have hcap' : (outN D A x).card≤2 := by
      have sub' : insert x (outN D A x) ⊆ A :=
        insert_subset_iff.mpr ⟨hR hx,hsubset⟩
      have no' (a) (ha : a∈insert x (outN D A x)) (z) (hz : z∈A) (hs : BankSink D A z)
          (k) (hk : k≤3) : ¬ Walk D A a z k := by
        rcases mem_insert.mp ha with hh|hh
        · subst a
          exact ban x hx z hz hs k (by omega)
        · exact no a hh z hz hs k hk
      have nin : x∉outN D A x := fun hh => loopfree (hf.mono_set hA) (by decide) (hR hx) (mem_outN.mp hh).2
      rcases sink_far_set_card acyc cA sub' no' with h|h <;> rw [card_insert_of_notMem nin] at h <;> omega
    have H := (card_le_card sub).trans (card_union_le _ _)
    rw [he x (hA (hR hx))] at H
    omega
  have pcap (x) (hx : x∈R) : (BackPool D B x).card≤2 := by
    have sep : Disjoint (BackPool D B x) (outN D B x) := disjoint_left.mpr (by
      intro b hb hxb
      obtain ⟨y,hy,edge,reach⟩ := (mem_filter.mp (show b∈B.filter _ from hb)).2
      obtain ⟨_,k,hk,w⟩ := mem_ball.mp reach
      exact hf x (k+1+1) (by omega) (by omega)
        ((Walk.step (hB (mem_outN.mp hxb).1) (mem_outN.mp hxb).2 (w.mono hB)).snoc (hA (hR hx)) edge))
    have sub : BackPool D B x ∪ outN D B x ⊆ B := union_subset
      (filter_subset _ _) (fun _ h => (mem_outN.mp h).1)
    have card := card_le_card sub
    rw [card_union_of_disjoint sep,cB] at card
    have := five x hx
    omega
  intro b hb x hx edge
  have hxr : x∈R := mem_filter.mpr ⟨hx,b,hb,edge⟩
  by_cases fa : QFree D B 7
  · have cover : B ⊆ R.biUnion (BackPool D B) := by
      intro a ha
      obtain ⟨p⟩ := exists_shortest_sink_path fa (by omega : B.card≤7) ha
      let z := p.vertex p.len
      have hz : z∈B := p.mem _ le_rfl
      have has (e) (he' : e∈outN D V z) : e∈A∨e∈T := by
        rcases mem_union.mp (keepB z hz he') with h|h
        · rcases mem_union.mp h with h|h
          · exact Or.inl h
          · exact (p.sink e h (mem_outN.mp he').2).elim
        · exact Or.inr h
      have ex : ∃ y∈A, D z y=true := by
        by_contra! h
        have sub : outN D V z ⊆ T := fun e he' =>
          (has e he').resolve_left (fun hh => h e hh (mem_outN.mp he').2)
        have H := card_le_card sub
        rw [he z (hB hz), cT] at H
        omega
      obtain ⟨y,hy,zy⟩ := ex
      have yR : y∈R := mem_filter.mpr ⟨hy,z,hz,zy⟩
      have P (i) (hi : i≤p.len) (hk : p.len-i≤4) : p.vertex i∈BackPool D B y :=
        mem_filter.mpr ⟨p.mem i hi,z,hz,zy,mem_ball.mpr ⟨hz,_,hk,p.walk hi le_rfl⟩⟩
      have len : p.len≤4 := by
        by_contra! h
        let I := (range (p.len+1)).filter (fun i => p.len-2≤i)
        have cI : I.card=3 := by
          have eq : I = range (p.len+1) \ range (p.len-2) := by
            ext i
            simp only [I,mem_filter,mem_range,mem_sdiff]
            omega
          rw [eq]
          have hc := card_sdiff_add_card_eq_card (range_mono (show p.len-2≤p.len+1 by omega))
          simp only [card_range] at hc
          omega
        have ce : (I.image p.vertex).card=3 := by
          rw [card_image_of_injOn,cI]
          exact (p.injective fa (by omega)).mono (fun _ hi => (mem_filter.mp hi).1)
        have subs : I.image p.vertex ⊆ BackPool D B y := by
          intro v hv
          obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
          obtain ⟨hi,lo⟩ := mem_filter.mp hi
          have il := mem_range.mp hi
          exact P i (by omega) (by omega)
        have cd := card_le_card subs
        have ac := pcap y yR
        omega
      exact mem_biUnion.mpr ⟨y,yR,by simpa only [p.start] using P 0 (Nat.zero_le _) (by omega)⟩
    have le := (card_le_card cover).trans (card_biUnion_le (s:=R) (t:=BackPool D B))
    have cap : (∑ y∈R,(BackPool D B y).card)≤2*R.card := by
      calc
        _ ≤ ∑ _y∈R,(2:ℕ) := sum_le_sum pcap
        _ = _ := by simp [Nat.mul_comm]
    omega
  · unfold QFree at fa
    push Not at fa
    obtain ⟨a,m,hm,hm',w⟩ := fa
    have mm : m=7 := by
      by_contra ne
      exact (hf.mono_set hB) a m hm (by omega) w
    subst m
    have ff := hf.mono_set hB
    have minB : ∀ t∈B,1≤(outN D B t).card := fun t ht =>
      minOut_of_boundary_closed_walk ff (by omega : B.card=6+1) w t ht
    have rr := dt_reg (q:=6) (by decide) (ball_q_one 6 (by decide)) ff minB (by omega)
    let E : CH.Digraph := fun a b => D b a
    have revM : ∀ a∈B,1≤(outN E B a).card := fun a ha => (rr.2 a ha).ge
    have grow := ball_one_growth ff.reverse revM hb 4 (by decide : 4+1≤6)
    have sub : ball E B b 4 ⊆ BackPool D B x := by
      intro a ha
      obtain ⟨ha,k,hk,wa⟩ := mem_ball.mp ha
      exact mem_filter.mpr ⟨ha,b,hb,edge,mem_ball.mpr ⟨hb,k,hk,wa.reverse_of_mem hb⟩⟩
    have lb := grow.trans (card_le_card sub)
    have ub := pcap x hxr
    omega

#print axioms no_return_of_acyclic_first_bank
end LeanCH.BR.DotDegreeSevenQ6


