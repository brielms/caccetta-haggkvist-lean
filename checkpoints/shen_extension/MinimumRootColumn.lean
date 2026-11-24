import checkpoints.shen_extension.AnchoredExteriorColumn

namespace LeanCH.BR.Closure.MinimumRootColumn
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor ShortestCycleWeights

def parents (q : ℕ) (D : CH.Digraph) (P S : Finset ℕ) (z : ℕ) :=
  (q+1)*(inN D P z).card+(inN D S z).card

/-- With the minimum label as the only possible overload, every unit of
unused incoming capacity elsewhere costs another q units in this bound. -/
theorem only_root {q n} (X : Model q n) (hq : 2≤q) {W P S : Finset ℕ} (wv : W⊆X.V)
    (ps : P.card=q) (dis : Disjoint P S) (cs : Cycle X.D W q S)
    (fits : ∀x∈S,Cycle X.D W q (insert x P))
    {h} (he : h∈X.V\(P∪S)) (minimum : ∀z∈X.V,X.weights h≤X.weights z)
    (only : ∀z∈(X.V\(P∪S)).erase h,parents q X.D P S z≤q+2) :
    X.V.card+q*q+q*(∑z∈(X.V\(P∪S)).erase h,(q+2-parents q X.D P S z))≤q*parents q X.D P S h := by
  classical
  let E := X.V\(P∪S)
  let T := E.erase h
  let B := parents q X.D P S
  let L (z) := 1+q*(q+2-B z)
  let C := (q+1)^2
  have high := AnchoredExteriorColumn.exterior_mass X hq wv ps dis cs fits
  change C*(∑z∈E,X.weights z)<q*(∑z∈E,B z*X.weights z) at high
  have eq (z) (zt : z∈T) : L z+q*B z=C := by
    have cap : B z≤q+2 := only z zt
    have e := Nat.sub_add_cancel cap
    dsimp [L,C]
    nlinarith only [congrArg (fun k : ℕ => q*k) e]
  have lost : (∑z∈T,L z*X.weights z)+q*(∑z∈T,B z*X.weights z)=C*(∑z∈T,X.weights z) := by
    simp only [mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro z zt
    rw [←Nat.mul_assoc,←Nat.add_mul,eq z zt]
  have total := sum_erase_add E X.weights he
  have incoming := sum_erase_add E (fun z => B z*X.weights z) he
  rw [←total,←incoming,Nat.mul_add,Nat.mul_add] at high
  change C*(∑z∈T,X.weights z)+C*X.weights h <
    q*(∑z∈T,B z*X.weights z)+q*(B h*X.weights h) at high
  rw [←lost] at high
  have paid : (∑z∈T,L z*X.weights z)+C*X.weights h < q*(B h*X.weights h) := by omega
  have floor := sum_le_sum (s:=T) (fun z zt => Nat.mul_le_mul_left (L z)
    (minimum z (mem_sdiff.mp (mem_of_mem_erase zt)).1))
  rw [←sum_mul] at floor
  have price : ((∑z∈T,L z)+C)*X.weights h < (q*B h)*X.weights h := by
    rw [Nat.add_mul,Nat.mul_assoc q]
    exact (Nat.add_le_add_right floor _).trans_lt paid
  have count := Nat.lt_of_mul_lt_mul_right price
  simp only [L,sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,←mul_sum] at count
  obtain ⟨x,xs⟩ := card_pos.mp (show 0<S.card by rw [cs.size]; omega)
  have pv : P⊆X.V := fun _ zp => wv ((fits x xs).sub (mem_insert_of_mem zp))
  have size := card_sdiff_add_card_eq_card (union_subset pv (cs.sub.trans wv))
  rw [card_union_of_disjoint dis,ps,cs.size] at size
  change E.card+(q+(q+1))=X.V.card at size
  have erase : T.card+1=E.card := card_erase_add_one he
  have expand : C=q*q+2*q+1 := by dsimp [C]; ring
  change T.card+q*(∑z∈T,(q+2-B z))+C<q*B h at count
  rw [expand] at count
  clear high eq floor paid price lost total incoming ps expand
  change X.V.card+q*q+q*(∑z∈T,(q+2-B z))≤q*B h
  omega

theorem sparse_budget {q n} (X : Model q n) (hq : 2≤q) {W P S : Finset ℕ} (wv : W⊆X.V)
    (ps : P.card=q) (dis : Disjoint P S) (cs : Cycle X.D W q S)
    (fits : ∀x∈S,Cycle X.D W q (insert x P)) {h} (he : h∈X.V\(P∪S))
    (minimum : ∀z∈X.V,X.weights h≤X.weights z)
    (stuck : ∀z∈(X.V\(P∪S)).erase h,(inN X.D P z).card+(inN X.D S z).card≤1) :
    (q+1)*X.V.card≤q*parents q X.D P S h+q*q+2*q := by
  classical
  let T := (X.V\(P∪S)).erase h
  let B := parents q X.D P S
  have unit (z) (zt : z∈T) : B z≤q+1 := by
    have f := stuck z zt
    change (q+1)*_+_≤_
    by_cases zero : (inN X.D P z).card=0
    · rw [zero,Nat.mul_zero,zero_add]; omega
    have one : (inN X.D P z).card=1 := by omega
    rw [one,Nat.mul_one]; omega
  have cost := only_root X hq wv ps dis cs fits he minimum (fun z zt => (unit z zt).trans (by omega))
  have deficit : T.card≤∑z∈T,(q+2-B z) := by
    simpa using sum_le_sum (s:=T) (fun z zt => (show 1≤q+2-B z by have := unit z zt; omega))
  change X.V.card+q*q+q*(∑z∈T,(q+2-B z))≤q*B h at cost
  have lb := Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left q deficit) _) cost
  obtain ⟨x,xs⟩ := card_pos.mp (show 0<S.card by rw [cs.size]; omega)
  have pv : P⊆X.V := fun _ zp => wv ((fits x xs).sub (mem_insert_of_mem zp))
  have size := card_sdiff_add_card_eq_card (union_subset pv (cs.sub.trans wv))
  rw [card_union_of_disjoint dis,ps,cs.size] at size
  have et : T.card+1=_ := card_erase_add_one he
  have tv : T.card+2*q+2=X.V.card := by omega
  change (q+1)*X.V.card≤q*B h+q*q+2*q
  nlinarith only [lb,tv,congrArg (fun m : ℕ => q*m) tv]

/-- If every retained exterior column has at most one parent anywhere in
the packet, a large source forces the deleted minimum to receive all P and
at least one S. This threshold is the same one used to start the orbit. -/
theorem stalled_root {q n} (X : Model q n) (hq : 2≤q) {W P S : Finset ℕ} (wv : W⊆X.V)
    (ps : P.card=q) (dis : Disjoint P S) (cs : Cycle X.D W q S)
    (fits : ∀x∈S,Cycle X.D W q (insert x P)) {h} (he : h∈X.V\(P∪S))
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (large : q*(q+1)<X.V.card)
    (stuck : ∀z∈(X.V\(P∪S)).erase h,(inN X.D P z).card+(inN X.D S z).card≤1) :
    (∀p∈P,X.D p h=true) ∧ (inN X.D S h).Nonempty := by
  classical
  let B := parents q X.D P S
  have budget := sparse_budget X hq wv ps dis cs fits he minimum stuck
  change (q+1)*X.V.card≤q*B h+q*q+2*q at budget
  have enough : q*(q+1)<B h := by
    by_contra! short
    nlinarith only [budget,Nat.mul_le_mul_left q short,
      Nat.mul_le_mul_left (q+1) (show q*(q+1)+1≤X.V.card by omega)]
  have lim : (inN X.D S h).card≤q+1 := (card_le_card (filter_subset _ _)).trans cs.size.le
  have lp : (inN X.D P h).card≤q := (card_le_card (filter_subset _ _)).trans ps.le
  change q*(q+1)<(q+1)*(inN X.D P h).card+(inN X.D S h).card at enough
  have eq : (inN X.D P h).card=q := by
    by_contra ne
    have c := Nat.mul_le_mul_left (q+1) (show (inN X.D P h).card+1≤q by omega)
    nlinarith only [enough,c,lim]
  have allP : inN X.D P h=P := eq_of_subset_of_card_le (filter_subset _ _) (eq.trans ps.symm).ge
  refine ⟨fun p hp => (mem_inN.mp (show p∈inN X.D P h from allP.symm ▸ hp)).2,card_pos.mp ?_⟩
  rw [eq,Nat.mul_comm (q+1) q] at enough
  omega

/-- At every cutoff, a packet in a minimum puncture of order at least
(q+1)^2 must send two actual arcs to some retained exterior label. -/
theorem fresh_pair {q n} (X : Model q n) (hq : 2≤q) {W P S : Finset ℕ} (wv : W⊆X.V)
    (ps : P.card=q) (dis : Disjoint P S) (cs : Cycle X.D W q S)
    (fits : ∀x∈S,Cycle X.D W q (insert x P)) {h} (he : h∈X.V\(P∪S))
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (large : (q+1)^2≤X.V.card) :
    ∃z∈(X.V\(P∪S)).erase h,2≤(inN X.D P z).card+(inN X.D S z).card := by
  classical
  by_contra! bad
  have budget := sparse_budget X hq wv ps dis cs fits he minimum (fun z zt => by have := bad z zt; omega)
  have lp : (inN X.D P h).card≤q := (card_le_card (filter_subset _ _)).trans ps.le
  have ls : (inN X.D S h).card≤q+1 := (card_le_card (filter_subset _ _)).trans cs.size.le
  have cap : parents q X.D P S h≤(q+1)^2 := by
    unfold parents
    nlinarith only [Nat.mul_le_mul_left (q+1) lp,ls]
  nlinarith only [budget,Nat.mul_le_mul_left q cap,Nat.mul_le_mul_left (q+1) large]

#print axioms fresh_pair
#print axioms stalled_root
#print axioms only_root
end LeanCH.BR.Closure.MinimumRootColumn
