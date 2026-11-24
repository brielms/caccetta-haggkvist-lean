import LeanCH.BR.BR96
import checkpoints.shen_extension.TightRowCapstone
import checkpoints.shen_extension.dot_tensor_research.DotTightParentCarrier_20261118


namespace LeanCH.BR.DotDegreeSeven
open Finset BRq2 BRq3 BR45 BRq6 DotTightParentCarrier
open scoped BigOperators

def Endpoint (q r : ℕ) : Prop :=
  ∀ D V, QFree D V q → V.Nonempty → V.card = q*r →
    (∀ v ∈ V, r ≤ (outN D V v).card) → False

theorem from_endpoint {q n r : ℕ} {D : CH.Digraph} (E : Endpoint q r)
    (hn : 0<n) (size : n≤q*r) (loop : CH.Loopless D n)
    (degree : CH.MinOutdegreeAtLeast D n r) : CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  obtain ⟨H,W,hf,hW,deg⟩ := TightRow.pad_to (q*r-n) D (range n) (qfree_of_noShort loop no)
    (nonempty_range_iff.mpr (by omega)) (fun _ hv => Compose.FloorSix.out_card degree (mem_range.mp hv))
  have hc : W.card = q*r := by rw [hW, card_range]; omega
  exact E H W hf (card_pos.mp (by rw [hc]; omega)) hc deg

private theorem out_erase (D : CH.Digraph) (V : Finset ℕ) (v u : ℕ) :
    outN D (V.erase u) v = (outN D V v).erase u := by
  ext x
  simp only [mem_outN, mem_erase]
  tauto

private theorem keep_six {D : CH.Digraph} {V : Finset ℕ} {a v : ℕ}
    (h : 7 ≤ (outN D V v).card) : 6 ≤ (outN D (V.erase a) v).card := by
  rw [out_erase]
  by_cases hv : a ∈ outN D V v
  · rw [card_erase_of_mem hv]; omega
  · rw [erase_eq_of_notMem hv]; omega

private theorem keep_six_pair {D : CH.Digraph} {V : Finset ℕ} {a b v : ℕ}
    (h : 7 ≤ (outN D V v).card) (block : ¬ (D v a = true ∧ D v b = true)) :
    6 ≤ (outN D ((V.erase a).erase b) v).card := by
  rcases not_and_or.mp block with ha | hb
  · rw [out_erase, out_erase, erase_eq_of_notMem (fun m => ha (mem_outN.mp m).2)]
    simpa [out_erase] using (keep_six (a := b) h)
  · rw [out_erase, out_erase, erase_eq_of_notMem (fun m => hb (mem_outN.mp (mem_erase.mp m).2).2)]
    simpa [out_erase] using (keep_six (a := a) h)

private theorem qfree_sub {D G : CH.Digraph} {V : Finset ℕ} {q : ℕ}
    (hf : QFree D V q) (sub : ∀ a b, G a b = true → D a b = true) : QFree G V q := by
  have transfer {a b k} (w : Walk G V a b k) : Walk D V a b k := by
    induction w with
    | refl a => exact .refl a
    | step hv he _ ih => exact .step hv (sub _ _ he) ih
  exact fun a k h1 hq w => hf a k h1 hq (transfer w)

theorem six_free_order38_false {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 6) (hs : V.card = 38) (hm : ∀ v ∈ V, 7 ≤ (outN D V v).card) : False := by
  classical
  obtain ⟨G,sub,hd⟩ := exists_outEq hm
  have free := qfree_sub hf sub
  have pair (a b : ℕ) (ha : a∈V) (hb : b∈V) (ne : a≠b) :
      ∃ x∈V, G x a = true ∧ G x b = true := by
    by_contra hn
    have block (v) (hv : v∈V) : ¬ (G v a = true ∧ G v b = true) := fun e => hn ⟨v,hv,e⟩
    let U := (V.erase a).erase b
    have uv : U ⊆ V := (erase_subset _ _).trans (erase_subset _ _)
    have hU : U.card=36 := by
      dsimp [U]
      rw [card_erase_of_mem (mem_erase.mpr ⟨ne.symm,hb⟩),card_erase_of_mem ha,hs]
    have deg : ∀ v∈U, 6≤(outN G U v).card :=
      fun v hv => keep_six_pair (hd v (uv hv)).ge (block v (uv hv))
    have lo := card_ge_thirty_seven (free.mono_set uv) deg (card_pos.mp (by omega))
    omega
  have indeg (h : ℕ) (hh : h∈V) : 7≤(inN G V h).card := by
    let P := inN G V h
    have cover : V.erase h ⊆ P.biUnion (fun v => (outN G V v).erase h) := by
      intro x hx
      obtain ⟨p,pV,ph,px⟩ := pair h x hh (mem_erase.mp hx).2 (mem_erase.mp hx).1.symm
      exact mem_biUnion.mpr ⟨p,mem_inN.mpr ⟨pV,ph⟩,mem_erase.mpr ⟨(mem_erase.mp hx).1,
        mem_outN.mpr ⟨(mem_erase.mp hx).2,px⟩⟩⟩
    have cnt := (card_le_card cover).trans card_biUnion_le
    have row (v) (hv : v∈P) : ((outN G V v).erase h).card = 6 := by
      have p := mem_inN.mp hv
      rw [card_erase_of_mem (mem_outN.mpr ⟨hh,p.2⟩),hd v p.1]
    rw [card_erase_of_mem hh,hs,sum_congr rfl row] at cnt
    simp at cnt
    change 7≤P.card
    omega
  have indeq (h : ℕ) (hh : h∈V) : (inN G V h).card=7 := by
    have same : ∑ v ∈ V, (inN G V v).card = ∑ _v ∈ V, 7 := by
      rw [←sum_out_in]
      exact sum_congr rfl hd
    exact ((sum_eq_sum_iff_of_le indeg).mp same.symm h hh).symm
  obtain ⟨h,hh⟩ := card_pos.mp (show 0<V.card by omega)
  let P := inN G V h
  have psub : P⊆V := fun _ h => (mem_inN.mp h).1
  have pc : P.card = (6:ℕ)+1 := indeq h hh
  have hnot : h∉P := fun m => free h 1 (by decide) (by decide)
    (.step hh (mem_inN.mp m).2 (.refl h))
  have cover : ∀ v∈V, ∃ a∈P, G a v = true := by
    intro v vv
    by_cases he : v=h
    · subst v
      obtain ⟨a,ha⟩ := card_pos.mp (show 0<P.card by omega)
      exact ⟨a,ha,(mem_inN.mp ha).2⟩
    · obtain ⟨a,ha,ah,av⟩ := pair h v hh vv (Ne.symm he)
      exact ⟨a,mem_inN.mpr ⟨ha,ah⟩,av⟩
  let U := (V \ P).erase h
  have uv : U⊆V := (erase_subset _ _).trans sdiff_subset
  have cnt := card_sdiff_add_card_eq_card psub
  have uc : U.card = 30 := by
    dsimp [U]
    rw [card_erase_of_mem (mem_sdiff.mpr ⟨hh,hnot⟩)]
    omega
  have five (v) (hv : v∈U) : 5≤(outN G U v).card := by
    have vv := uv hv
    have nop : G v h ≠ true := fun a => (mem_sdiff.mp (mem_erase.mp hv).2).2 (mem_inN.mpr ⟨vv,a⟩)
    have cap := parent_bank_return_cap (by decide : 2≤6) free psub pc cover vv
    have split : (outN G V v).card = (outN G P v).card + (outN G (V \ P) v).card := by
      simpa only [union_sdiff_of_subset psub] using
        card_outN_union (D:=G) (show Disjoint P (V \ P) from disjoint_sdiff) v
    have eq : outN G U v=outN G (V \ P) v := by
      dsimp [U]
      rw [out_erase,erase_eq_of_notMem (fun m => nop (mem_outN.mp m).2)]
    rw [eq]
    have := hd v vv
    omega
  have lo := lower_order (by decide : 5≤6) (by decide : 2≤5) (by decide : 5<6)
    (free.mono_set uv) five (card_pos.mp (by omega))
  omega

theorem six_free_seven_order {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 6) (hn : V.Nonempty) (hs : V.card ≤ 38)
    (hm : ∀ v ∈ V, 7 ≤ (outN D V v).card) : False := by
  obtain ⟨G,W,free,card,deg⟩ := TightRow.pad_to (38-V.card) D V hf hn hm
  exact six_free_order38_false free (by omega) deg

#print axioms from_endpoint
#print axioms six_free_seven_order

theorem seven_free_order44_false {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 7) (hs : V.card = 44) (hm : ∀ v ∈ V, 7 ≤ (outN D V v).card) : False := by
  classical
  obtain ⟨G,sub,hd⟩ := exists_outEq hm
  have free := qfree_sub hf sub
  have pair (a b : ℕ) (ha : a∈V) (hb : b∈V) (ne : a≠b) :
      ∃ x∈V, G x a = true ∧ G x b = true := by
    by_contra hn
    have block (v) (hv : v∈V) : ¬ (G v a = true ∧ G v b = true) := fun e => hn ⟨v,hv,e⟩
    let U := (V.erase a).erase b
    have uv : U ⊆ V := (erase_subset _ _).trans (erase_subset _ _)
    have hU : U.card=42 := by
      dsimp [U]
      rw [card_erase_of_mem (mem_erase.mpr ⟨ne.symm,hb⟩),card_erase_of_mem ha,hs]
    have deg : ∀ v∈U, 6≤(outN G U v).card :=
      fun v hv => keep_six_pair (hd v (uv hv)).ge (block v (uv hv))
    have lo := card_ge_forty_three (free.mono_set uv) deg (card_pos.mp (by omega))
    omega
  have indeg (h : ℕ) (hh : h∈V) : 8≤(inN G V h).card := by
    let P := inN G V h
    have cover : V.erase h ⊆ P.biUnion (fun v => (outN G V v).erase h) := by
      intro x hx
      obtain ⟨p,pV,ph,px⟩ := pair h x hh (mem_erase.mp hx).2 (mem_erase.mp hx).1.symm
      exact mem_biUnion.mpr ⟨p,mem_inN.mpr ⟨pV,ph⟩,mem_erase.mpr ⟨(mem_erase.mp hx).1,
        mem_outN.mpr ⟨(mem_erase.mp hx).2,px⟩⟩⟩
    have cnt := (card_le_card cover).trans card_biUnion_le
    have row (v) (hv : v∈P) : ((outN G V v).erase h).card = 6 := by
      have p := mem_inN.mp hv
      rw [card_erase_of_mem (mem_outN.mpr ⟨hh,p.2⟩),hd v p.1]
    rw [card_erase_of_mem hh,hs,sum_congr rfl row] at cnt
    simp at cnt
    change 8≤P.card
    omega
  have b := sum_le_sum indeg
  have same : ∑ v ∈ V, (inN G V v).card = ∑ _v ∈ V, 7 := by
    rw [←sum_out_in]
    exact sum_congr rfl hd
  rw [same] at b
  simp [hs] at b

theorem seven_free_seven_order {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 7) (hn : V.Nonempty) (hs : V.card ≤ 44)
    (hm : ∀ v ∈ V, 7 ≤ (outN D V v).card) : False := by
  obtain ⟨G,W,free,card,deg⟩ := TightRow.pad_to (44-V.card) D V hf hn hm
  exact seven_free_order44_false free (by omega) deg

#print axioms seven_free_seven_order

end LeanCH.BR.DotDegreeSeven
