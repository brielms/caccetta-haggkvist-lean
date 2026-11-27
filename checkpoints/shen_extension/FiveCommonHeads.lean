import Mathlib.Data.Finset.Card

namespace LeanCH.BR.TripleBank
open Finset

/-- Two full rows in L have at least five common exterior heads when each
replacement label costs three heads plus one per row pointing to the label.
The exterior pool can be smaller than L. -/
theorem five_common_exterior_heads {L Y : Finset ℕ} {N : ℕ → Finset ℕ} {p q : ℕ}
    (pl : p ∈ L) (ql : q ∈ L) (pp : p ∉ N p) (qq : q ∉ N q)
    (nodigon : ¬ (q ∈ N p ∧ p ∈ N q)) (ys : Y.card ≤ L.card)
    (pfull : L.card + 2 ≤ (N p).card) (qfull : L.card + 2 ≤ (N q).card)
    (pex : N p \ L ⊆ Y) (qex : N q \ L ⊆ Y)
    (paid : ∀ r ∈ L, 3 + (if r ∈ N p then 1 else 0) + (if r ∈ N q then 1 else 0) ≤
      ((N p \ L) ∩ (N q \ L)).card) :
    5 ≤ ((N p \ L) ∩ (N q \ L)).card := by
  classical
  by_contra! small
  let I := N p ∩ L
  let J := N q ∩ L
  let E := N p \ L
  let F := N q \ L
  have rowP : E.card + I.card = (N p).card := card_sdiff_add_card_inter _ _
  have rowQ : F.card + J.card = (N q).card := card_sdiff_add_card_inter _ _
  have outside : (E ∪ F).card ≤ L.card := (card_le_card (union_subset pex qex)).trans ys
  have outsideId := card_union_add_card_inter E F
  have insideId := card_union_add_card_inter I J
  have hole : ∃ r ∈ L, r ∉ I ∪ J := by
    by_cases pq : q ∈ N p
    · exact ⟨p, pl, fun h => (mem_union.mp h).elim
        (fun hi => pp (mem_inter.mp hi).1) (fun hj => nodigon ⟨pq,(mem_inter.mp hj).1⟩)⟩
    · exact ⟨q, ql, fun h => (mem_union.mp h).elim
        (fun hi => pq (mem_inter.mp hi).1) (fun hj => qq (mem_inter.mp hj).1)⟩
  obtain ⟨s, sl, gap⟩ := hole
  have incl : I ∪ J ⊆ L.erase s := by
    intro r hr
    exact mem_erase.mpr ⟨fun eq => gap (eq ▸ hr),
      (mem_union.mp hr).elim (fun h => (mem_inter.mp h).2) (fun h => (mem_inter.mp h).2)⟩
  have inside := card_le_card incl
  have erased := card_erase_add_one sl
  change (E ∩ F).card < 5 at small
  obtain ⟨r, both⟩ := card_pos.mp (show 0 < (I ∩ J).card by omega)
  obtain ⟨ri, rj⟩ := mem_inter.mp both
  obtain ⟨rp, rl⟩ := mem_inter.mp ri
  have rq := (mem_inter.mp rj).1
  exact (Nat.not_le_of_lt small) (by simpa [rp, rq, E, F] using paid r rl)

end LeanCH.BR.TripleBank
