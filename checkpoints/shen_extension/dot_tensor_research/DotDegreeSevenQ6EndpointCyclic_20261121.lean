import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ6SpillBanks_20261121
import LeanCH.BR.BRNearBoundaryRows

namespace LeanCH.BR.DotDegreeSevenQ6
open Finset BRq2 BRq3 BR45 BRsGen

/-- A receiver from a complete internal degree-one bank must miss at least five
columns of the first bank reach tensor. -/
theorem five_missing_of_return {D : CH.Digraph} {V A : Finset ℕ} {b x : ℕ}
    (hf : QFree D V 6) (hA : A⊆V) (hb : b∈V) (hx : x∈A)
    (hin : ∀ a∈A, 1≤(outN D A a).card) (ret : D b x=true) :
    5 ≤ (A.filter (fun a => D a b ≠ true)).card := by
  classical
  let E : CH.Digraph := D
  have revF : QFree E A 6 := hf.mono_set hA
  have revM : ∀ a∈A, 1≤(outN E A a).card := hin
  have grow := ball_one_growth revF revM hx 4 (by decide : 4+1≤6)
  have sub : ball E A x 4 ⊆ A.filter (fun a => D a b ≠ true) := by
    intro a ha
    obtain ⟨haA,k,hk,w⟩ := mem_ball.mp ha
    apply mem_filter.mpr
    refine ⟨haA,?_⟩
    intro edge
    have fw : Walk D V x a k := w.mono hA
    exact hf b (k+1+1) (by omega) (by omega) ((Walk.step (hA hx) ret (fw.snoc hb edge)))
  exact grow.trans (card_le_card sub)

#print axioms five_missing_of_return
end LeanCH.BR.DotDegreeSevenQ6



namespace LeanCH.BR.DotDegreeSevenQ6
open Finset BRq2 BRq3 BR45 BRsGen

theorem no_return_of_degree_one_first_bank {D : CH.Digraph} {V A B T : Finset ℕ}
    (hf : QFree D V 6) (he : OutEq 7 D V) (hA : A⊆V) (hB : B⊆V)
    (cA : A.card=7) (cB : B.card=7) (cT : T.card=6)
    (eA : OutEq 1 D A)
    (keepA : ∀ a∈A, outN D V a⊆A∪B)
    (keepB : ∀ b∈B, outN D V b⊆(A∪B)∪T) :
    ∀ b∈B, ∀ x∈A, D b x ≠ true := by
  classical
  have mA : ∀ a∈A,1≤(outN D A a).card := fun a ha => (eA a ha).ge
  have mB (a) (ha : a∈A) : 6≤(outN D B a).card := by
    have H : outN D V a ⊆ outN D A a ∪ outN D B a := by
      intro y hy
      rcases mem_union.mp (keepA a ha hy) with h | h
      · exact mem_union_left _ (mem_outN.mpr ⟨h,(mem_outN.mp hy).2⟩)
      · exact mem_union_right _ (mem_outN.mpr ⟨h,(mem_outN.mp hy).2⟩)
    have E := (card_le_card H).trans (card_union_le _ _)
    rw [he a (hA ha),eA a ha] at E
    omega
  have miss (a) (ha : a∈A) : (B.filter fun b => D a b ≠ true).card ≤ 1 := by
    have split : (B.filter (fun b => D a b ≠ true)) = B \ outN D B a := by
      ext b
      simp only [mem_filter,mem_sdiff,mem_outN]
      tauto
    rw [split]
    have eq := card_sdiff_add_card_eq_card (show outN D B a ⊆ B from
      fun _ h => (mem_outN.mp h).1)
    have m := mB a ha
    omega
  have noTwo (a b c) (ha : a∈A) (hb : b∈B) (hc : c∈B) (ne : b≠c)
      (mb : D a b ≠ true) (mc : D a c ≠ true) : False := by
    have inc : ({b,c} : Finset ℕ) ⊆ B.filter (fun b => D a b ≠ true) := by
      simp [insert_subset_iff,hb,hc,mb,mc]
    have n := card_le_card inc
    rw [card_pair ne] at n
    have := miss a ha
    omega
  intro b hb x hx bx
  have unique (c) (hc : c∈B) (ne : c≠b) (y) (hy : y∈A) (cy : D c y=true) : False := by
    let U := A.filter (fun a => D a b ≠ true)
    let W := A.filter (fun a => D a c ≠ true)
    have cU : 5≤U.card := five_missing_of_return hf hA (hB hb) hx mA bx
    have cW : 5≤W.card := five_missing_of_return hf hA (hB hc) hy mA cy
    have dis : Disjoint U W := disjoint_left.mpr fun a ha ha' =>
      noTwo a b c (mem_filter.mp ha).1 hb hc ne.symm (mem_filter.mp ha).2 (mem_filter.mp ha').2
    have ub : (U∪W).card ≤ 7 := by
      rw [←cA]
      exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
    rw [card_union_of_disjoint dis] at ub
    omega
  have noInto (c) (hc : c∈B.erase b) (cb : D c b=true) : False := by
    have ne := (mem_erase.mp hc).1
    have hc' := mem_of_mem_erase hc
    have xb : D x b ≠ true := fun xb => hf b 2 (by decide) (by decide)
      (.step (hA hx) bx (.step (hB hb) xb (.refl b)))
    have xc : D x c=true := by
      by_contra m
      exact noTwo x b c hx hb hc' ne.symm xb m
    exact hf b 3 (by decide) (by decide) (.step (hA hx) bx (.step (hB hc') xc
      (.step (hB hb) cb (.refl b))))
  have m : ∀ c∈B.erase b, 1 ≤ (outN D (B.erase b) c).card := by
    intro c hc
    have H : outN D V c ⊆ outN D (B.erase b) c ∪ T := by
      intro z hz
      rcases mem_union.mp (keepB c (mem_of_mem_erase hc) hz) with h|h
      · rcases mem_union.mp h with a|d
        · exact (unique c (mem_of_mem_erase hc) (mem_erase.mp hc).1 z a (mem_outN.mp hz).2).elim
        · exact mem_union_left _ (mem_outN.mpr ⟨mem_erase.mpr ⟨
            fun eq => noInto c hc (eq ▸ (mem_outN.mp hz).2),d⟩,(mem_outN.mp hz).2⟩)
      · exact mem_union_right _ h
    have lb := (card_le_card H).trans (card_union_le _ _)
    rw [he c (hB (mem_of_mem_erase hc)),cT] at lb
    omega
  have ca : (B.erase b).card=6 := by rw [card_erase_of_mem hb,cB]
  have lb := dt_size (q:=6) (by decide) (ball_q_one 6 (by decide))
    (hf.mono_set ((erase_subset b B).trans hB)) m (card_pos.mp (by omega))
  omega

#print axioms no_return_of_degree_one_first_bank
end LeanCH.BR.DotDegreeSevenQ6

