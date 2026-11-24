import LeanCH.BR.BRFiniteWalk
import LeanCH.BR.BRq3Util
import Mathlib.Order.Interval.Finset.Nat

namespace LeanCH.BR.RecipientUnionAudit

open Finset BRq2 BRq3

/-- At a returning sink, either the starting bank label is omitted by the
recipient, or the recipient omits an entire cutoff-sized suffix. -/
theorem ancestor_omitted {D : CH.Digraph} {V A Y : Finset ℕ} {q v x : ℕ}
    (free : QFree D V q) (time : 2 ≤ q) (sub : A ⊆ V) (inside : A ⊆ Y)
    (acyclic : QFree D A A.card) (vv : v ∈ V) (p : ShortestSinkPath D A x)
    (returnArc : D (p.vertex p.len) v = true)
    (small : (Y \ outN D V v).card < q - 1) :
    x ∈ Y \ outN D V v := by
  classical
  have missing (i : ℕ) (index : i ≤ p.len) (depth : p.len - i + 2 ≤ q) :
      p.vertex i ∈ Y \ outN D V v := by
    have ym := p.mem i index
    refine mem_sdiff.mpr ⟨inside ym, fun h => ?_⟩
    have suffix := (p.walk index le_rfl).mono sub
    exact free v _ (by omega) (by omega)
      ((Walk.step (sub ym) (mem_outN.mp h).2 suffix).snoc vv returnArc)
  have bound : p.len + 2 ≤ q := by
    by_contra! late
    let I := Icc (p.len - (q - 2)) p.len
    have incl : I.image p.vertex ⊆ Y \ outN D V v := by
      intro y hy
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
      obtain ⟨lo,hi⟩ := mem_Icc.mp hi
      exact missing i hi (by omega)
    have inj : Set.InjOn p.vertex ↑I := by
      intro a ha b hb eq
      have hA := (mem_Icc.mp ha).2
      have hB := (mem_Icc.mp hb).2
      exact p.injective acyclic le_rfl (mem_range.mpr (by omega : a < p.len + 1))
        (mem_range.mpr (by omega : b < p.len + 1)) eq
    have count := card_le_card incl
    rw [card_image_of_injOn inj] at count
    have len : I.card = q - 1 := by
      dsimp [I]
      rw [Nat.card_Icc]
      omega
    omega
  exact p.start ▸ missing 0 (Nat.zero_le _) (by omega)

/-- If every sink in the chosen second bank returns, every nonisolated
label is covered by a returning recipient's omission, and every isolated
label is covered by the return-tail bank. -/
theorem recipient_union {D : CH.Digraph} {V X Y A R O H : Finset ℕ} {q : ℕ}
    (free : QFree D V q) (time : 2 ≤ q) (xv : X ⊆ V) (av : A ⊆ V) (ay : A ⊆ Y)
    (acyclic : QFree D A A.card)
    (need : ∀ s ∈ A, (∀ z ∈ A, D s z ≠ true) → ∃ v ∈ X, D s v = true)
    (bank : ∀ s ∈ A, (∀ z ∈ A, D s z ≠ true) →
      (∃ z ∈ A, D z s = true) → ∀ v ∈ X, D s v = true → v ∈ R)
    (small : ∀ v ∈ R, (Y \ outN D V v).card < q - 1)
    (tails : ∀ s ∈ A, (∃ v ∈ X, D s v = true) → s ∈ O ∪ H) :
    A ⊆ R.biUnion (fun v => Y \ outN D V v) ∪ (O ∪ H) := by
  classical
  intro x hx
  obtain ⟨p⟩ := exists_shortest_sink_path acyclic le_rfl hx
  have send := need _ (p.mem _ le_rfl) p.sink
  by_cases parent : ∃ z ∈ A, D z (p.vertex p.len) = true
  · obtain ⟨v,hv,e⟩ := send
    have pay := bank _ (p.mem _ le_rfl) p.sink parent v hv e
    exact mem_union_left _ (mem_biUnion.mpr ⟨v,pay,
      ancestor_omitted free time av ay acyclic (xv hv) p e (small v pay)⟩)
  · have noSteps : p.len = 0 := by
      by_contra nz
      have h := p.edge (p.len - 1) (by omega)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ p.len)] at h
      exact parent ⟨_,p.mem _ (by omega),h⟩
    have endAt : p.vertex p.len = x := by rw [noSteps,p.start]
    exact mem_union_right _ (tails x hx (endAt ▸ send))

/-- A returning column reached quickly from its receiver must be the
omitted label of the actual sink at the end of that receiver's path. -/
theorem early_return_omission {D : CH.Digraph} {V X Y : Finset ℕ} {q v y s k b : ℕ}
    (free : QFree D V q) (xv : X ⊆ V) (yv : Y ⊆ V)
    (vx : v ∈ X) (yy : y ∈ Y) (arc : D y v = true)
    (path : Walk D X v s k) (time : k + 2 ≤ q)
    (row : outN D V s = Y.erase b) : y = b := by
  by_contra different
  have sy := (mem_outN.mp (row.symm ▸ mem_erase.mpr ⟨different,yy⟩)).2
  exact free v _ (by omega) (by omega)
    (((path.mono xv).snoc (yv yy) sy).snoc (xv vx) arc)

/-- A parentful returning column cannot have a receiver with a still
shorter sink path through the actual first layer. -/
theorem parentful_return_excludes_short {D : CH.Digraph} {V X Y : Finset ℕ}
    {q v y z s k b : ℕ} (free : QFree D V q) (xv : X ⊆ V) (yv : Y ⊆ V)
    (vx : v ∈ X) (yy : y ∈ Y) (zy : z ∈ Y)
    (arc : D y v = true) (prior : D z y = true)
    (path : Walk D X v s k) (time : k + 3 ≤ q)
    (row : outN D V s = Y.erase b) : False := by
  have yb := early_return_omission free xv yv vx yy arc path (by omega) row
  have zb : z ≠ b := by
    intro eq
    have same : y = z := yb.trans eq.symm
    exact loopfree free (by omega) (yv zy) (same ▸ prior)
  have sz := (mem_outN.mp (row.symm ▸ mem_erase.mpr ⟨zb,zy⟩)).2
  exact free v _ (by omega) (by omega)
    ((((path.mono xv).snoc (yv zy) sz).snoc (yv yy) prior).snoc (xv vx) arc)

/-- The recipient-union cover with the omission and late-tail sets generated
from actual paths to sinks. The first-layer sink labels and their
omissions are kept throughout. -/
theorem cover_from_depths {D : CH.Digraph} {V X Y S R L : Finset ℕ} {q : ℕ}
    (free : QFree D V q) (time : 2 ≤ q) (xv : X ⊆ V) (yv : Y ⊆ V)
    (omitted : ℕ → ℕ) {s : ℕ}
    (row : ∀ t ∈ S, outN D V t = Y.erase (omitted t))
    (acyclic : QFree D (Y.erase (omitted s)) (Y.erase (omitted s)).card)
    (need : ∀ b ∈ Y.erase (omitted s),
      (∀ z ∈ Y.erase (omitted s), D b z ≠ true) → ∃ v ∈ X, D b v = true)
    (bank : ∀ v ∈ X, v ∉ R → ∃ t ∈ S, ∃ k, k + 3 ≤ q ∧ Walk D X v t k)
    (early : ∀ v ∈ X, v ∉ L → ∃ t ∈ S, ∃ k, k + 2 ≤ q ∧ Walk D X v t k)
    (small : ∀ v ∈ R, (Y \ outN D V v).card < q - 1) :
    let A := Y.erase (omitted s)
    let O := (S.erase s).image omitted
    let H := A.filter (fun b => ∃ v ∈ L, D b v = true)
    A ⊆ R.biUnion (fun v => Y \ outN D V v) ∪ (O ∪ H) := by
  classical
  let A := Y.erase (omitted s)
  let O := (S.erase s).image omitted
  let H := A.filter (fun b => ∃ v ∈ L, D b v = true)
  have ay : A ⊆ Y := erase_subset _ _
  apply recipient_union free time xv (ay.trans yv) ay acyclic need ?_ small ?_
  · intro b hb _ par v hv edge
    by_contra outside
    obtain ⟨t,ht,k,lim,path⟩ := bank v hv outside
    obtain ⟨z,hz,zb⟩ := par
    exact parentful_return_excludes_short free xv yv hv (ay hb) (ay hz) edge zb path lim (row t ht)
  · intro b hb ret
    obtain ⟨v,hv,arc⟩ := ret
    by_cases inLate : v ∈ L
    · exact mem_union_right _ (mem_filter.mpr ⟨hb,v,inLate,arc⟩)
    · obtain ⟨t,ht,k,lim,path⟩ := early v hv inLate
      have bo := early_return_omission free xv yv hv (ay hb) arc path lim (row t ht)
      have different : t ≠ s := fun eq => (mem_erase.mp hb).1 (eq ▸ bo)
      exact mem_union_left _ (mem_image.mpr ⟨t,mem_erase.mpr ⟨different,ht⟩,bo.symm⟩)

/-- The three physical sets pay for all labels in the marked bank. -/
theorem impossible_recipient_union {A U O H : Finset ℕ}
    (cover : A ⊆ U ∪ (O ∪ H))
    (tooFew : U.card + O.card + H.card < A.card) : False := by
  have count := (card_le_card cover).trans (card_union_le _ _)
  have more := card_union_le O H
  omega

/-- If the late recipients are already among the charged recipients, their
tails use no extra slots: each such tail is a missed head by digon-freeness. -/
theorem late_tails_in_recipient_union {D : CH.Digraph} {V Y A R L : Finset ℕ} {q : ℕ}
    (free : QFree D V q) (time : 2 ≤ q) (yv : Y ⊆ V)
    (ay : A ⊆ Y) (lv : L ⊆ V) (charged : L ⊆ R) :
    A.filter (fun b => ∃ v ∈ L, D b v = true) ⊆ R.biUnion (fun v => Y \ outN D V v) := by
  classical
  intro b hb
  obtain ⟨ba,v,vl,arc⟩ := mem_filter.mp hb
  have by_ := ay ba
  exact mem_biUnion.mpr ⟨v,charged vl,mem_sdiff.mpr ⟨by_,fun h =>
    digonfree free time (lv vl) (yv by_) (mem_outN.mp h).2 arc⟩⟩

#print axioms ancestor_omitted
#print axioms recipient_union
#print axioms cover_from_depths
#print axioms impossible_recipient_union
#print axioms late_tails_in_recipient_union
end LeanCH.BR.RecipientUnionAudit
