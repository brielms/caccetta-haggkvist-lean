import checkpoints.shen_extension.ExactFiveInternalHead

namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

/-- Every triple of inherited targets with all three exterior overlaps
exactly five contains a pair with a common neutral head. The pair may
itself be adjacent. -/
theorem exact_five_triple {D : CH.Digraph} {U L Y I : Finset ℕ}
    (safe : QFree D U 3) (lu : L ⊆ U) (il : I ⊆ L) (three : 3 ≤ I.card)
    (ys : Y.card≤L.card) (full : ∀ p∈I, L.card+2≤(outN D U p).card)
    (outside : ∀ p∈I, outN D U p \ L ⊆ Y)
    (five : ∀ p∈I, ∀ q∈I, p≠q → ((outN D U p \ L) ∩ (outN D U q \ L)).card=5) :
    ∃ p∈I, ∃ q∈I, p≠q ∧ ∃ r∈L, D p r=true ∧ D q r=true := by
  classical
  by_cases absent : ∃ p∈I, ∃ q∈I, p≠q ∧ D p q≠true ∧ D q p≠true
  · obtain ⟨p,pi,q,qi,pq,off,rev⟩ := absent
    obtain ⟨r,rl,pr,qr⟩ := exact_five_internal_head (N:=outN D U) (il pi) (il qi) pq
      (fun m => loopfree safe (by decide) (lu (il pi)) (mem_outN.mp m).2)
      (fun m => loopfree safe (by decide) (lu (il qi)) (mem_outN.mp m).2)
      (fun m => off (mem_outN.mp m).2) (fun m => rev (mem_outN.mp m).2)
      ys (full _ pi) (full _ qi) (outside _ pi) (outside _ qi) (five _ pi _ qi pq)
    exact ⟨p,pi,q,qi,pq,r,rl,(mem_outN.mp pr).2,(mem_outN.mp qr).2⟩
  have linked {p q} (pi : p∈I) (qi : q∈I) (ne : p≠q) : D p q=true ∨ D q p=true := by
    by_contra! missing
    exact absent ⟨p,pi,q,qi,ne,missing⟩
  obtain ⟨a,ai,b,bi,c,ci,ab,ac,bc⟩ := two_lt_card.mp three
  have branch {x y z} (xi : x∈I) (yi : y∈I) (zi : z∈I) (xy : x≠y) (xz : x≠z) (yz : y≠z)
      (ed : D x y=true) : ∃ p∈I, ∃ q∈I, p≠q ∧ ∃ r∈L, D p r=true ∧ D q r=true := by
    rcases linked yi zi yz with yz' | zy
    · rcases linked xi zi xz with xz' | zx
      · exact ⟨x,xi,y,yi,xy,z,il zi,xz',yz'⟩
      · exact False.elim (safe x 3 (by decide) (by decide)
          (.step (lu (il yi)) ed (.step (lu (il zi)) yz' (.step (lu (il xi)) zx (.refl _)))))
    · exact ⟨x,xi,z,zi,xz,y,il yi,ed,zy⟩
  exact (linked ai bi ab).elim (branch ai bi ci ab ac bc) (branch bi ai ci ab.symm bc ac)

#print axioms exact_five_triple
end LeanCH.BR.TripleBank
