import checkpoints.shen_extension.CoverBankRecurrence

namespace LeanCH.BR.Closure.RemoteBankDeletion
open Finset BRq2 BRq3 BR45 DeficitLevels

/-- Replace S at its original size and delete any one external vertex p.
One surviving tight row must point to p while avoiding all of S. Only
common exits distinct from p are required. -/
theorem external_parent {q s} (O : Origin q s) (hq : 1≤q) {S H : Finset ℕ} {p : ℕ}
    (sv : S⊆O.V) (hw : H⊆O.V\S) (exits : ∀a∈S, ∀h∈H, O.G a h=true)
    (size : S.card=s) (pv : p∈O.V\S) (room : q*(s-(H.erase p).card)<s) :
    ∃x∈(O.V\S).erase p, (outN O.G O.V x).card=s ∧ O.G x p=true ∧ outN O.G S x=∅ := by
  classical
  let W := (O.V\S).erase p
  have wv : W⊆O.V := (erase_subset _ _).trans sdiff_subset
  have common : H.erase p⊆W := fun z hz => mem_erase.mpr ⟨(mem_erase.mp hz).1,hw (mem_erase.mp hz).2⟩
  have part (x) (miss : outN O.G S x=∅) : outN O.G (O.V\S) x=outN O.G O.V x := by
    ext z
    simp only [mem_outN,mem_sdiff]
    constructor
    · tauto
    · rintro ⟨zv,arc⟩
      refine ⟨⟨zv,fun zs => ?_⟩,arc⟩
      have ze : z∈outN O.G S x := mem_outN.mpr ⟨zs,arc⟩
      simp [miss] at ze
  by_contra none
  have paid (x) (hx : x∈W) : s≤(outN O.G W x).card+(if (outN O.G S x).Nonempty then s else 0) := by
    by_cases seen : (outN O.G S x).Nonempty
    · simp [seen]
    · simp only [seen,ite_false,Nat.add_zero]
      have miss := not_nonempty_iff_eq_empty.mp seen
      have eq : outN O.G W x=(outN O.G O.V x).erase p := by
        rw [←part x miss]
        ext z; simp only [W,mem_erase,mem_outN]; tauto
      rw [eq]
      have deg := O.deg x (wv hx)
      by_cases hit : p∈outN O.G O.V x
      · rw [card_erase_of_mem hit]
        have loose : (outN O.G O.V x).card≠s := fun tight =>
          none ⟨x,hx,tight,(mem_outN.mp hit).2,miss⟩
        omega
      · rwa [erase_eq_of_notMem hit]
  obtain ⟨G,U,live,uc,free,deg⟩ := CommonExitReplacement.funded O.free hq sv wv common
    (fun a ha h hh => exits a ha h (mem_erase.mp hh).2) room paid
  have least := O.least G U free deg live
  have total := card_sdiff_add_card_eq_card sv
  have proper := card_erase_add_one pv
  change W.card+1=_ at proper
  omega

def avoiding (D : CH.Digraph) (V S : Finset ℕ) (s : ℕ) : Finset ℕ :=
  (V\S).filter (fun x => (outN D V x).card=s ∧ outN D S x=∅)

/-- When the common exits can lose any single label, the tight rows
avoiding S have at least q+1 members. Internally every row has a parent. -/
theorem avoiding_size {q s} (O : Origin q s) (hq : 1≤q) {S H : Finset ℕ}
    (sv : S⊆O.V) (hw : H⊆O.V\S) (exits : ∀a∈S, ∀h∈H, O.G a h=true)
    (size : S.card=s) (room : q*(s-(H.card-1))<s) :
    q+1≤(avoiding O.G O.V S s).card := by
  classical
  let A := avoiding O.G O.V S s
  have all (p) (pv : p∈O.V\S) : ∃x∈A, O.G x p=true := by
    have compare : H.card-1≤(H.erase p).card := by
      by_cases ph : p∈H
      · rw [card_erase_of_mem ph]
      · rw [erase_eq_of_notMem ph]; omega
    have cheaper := Nat.mul_le_mul_left q (Nat.sub_le_sub_left compare s)
    obtain ⟨x,xw,deg,arc,miss⟩ := external_parent O hq sv hw exits size pv (cheaper.trans_lt room)
    exact ⟨x,mem_filter.mpr ⟨(mem_erase.mp xw).2,deg,miss⟩,arc⟩
  have hv : H.Nonempty := by
    by_contra h
    have empty := not_nonempty_iff_eq_empty.mp h
    have qs := Nat.mul_le_mul_right s hq
    simp [empty] at room
    omega
  obtain ⟨p,ph⟩ := hv
  obtain ⟨x,xA,_⟩ := all p (hw ph)
  have av : A⊆O.V := (show A⊆O.V\S from filter_subset _ _).trans sdiff_subset
  let R : CH.Digraph := fun a b => O.G b a
  have rev : QFree R A q := O.free.reverse.mono_set av
  have one (p) (pa : p∈A) : 1≤(outN R A p).card := by
    obtain ⟨y,ya,yp⟩ := all p (mem_filter.mp pa).1
    exact card_pos.mpr ⟨y,mem_outN.mpr ⟨ya,yp⟩⟩
  have ord := dt_size hq (ball_q_one q hq) rev one ⟨x,xA⟩
  simpa using ord

#print axioms external_parent
#print axioms avoiding_size
end LeanCH.BR.Closure.RemoteBankDeletion
