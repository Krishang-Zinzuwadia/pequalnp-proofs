import Mathlib.Combinatorics.SimpleGraph.VertexCover
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

-- Low-budget circuits share one mixing OR and therefore give three raw clauses.
-- All higher budgets retain the edge and cover accounting separately.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 50000 in
theorem PEqualNP.Outside.R_meta_1597_613
  (smallExtract : let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
    ∀ D : Circuit, D.size ≤ 21 → IsLeastAO G D → TopForm G D → 2 ≤ (junk G D).card →
    let U := Ustar G D
    let B := 2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card
    B ≤ 3 → 2 ≤ U.card →
    (∀ u v : Fin 11, s(u,v) ∈ U → ∃ a ∈ tops G D, ∃ b : Fin 2, ∃ h ∈ junk G D,
      gateVal 11 D a (pairInput u v) = true ∧ OrReaches 11 D (opnd D a b) h ∧
      gateVal 11 D h (pairInput u v) = true) →
    ∃ (w : Fin 11) (A : Fin 3 → Finset (Fin 11)), B = 3 ∧
    (∀ i, (A i).card ≤ 1 ∨ ∃ z, ∀ v ∈ A i, G.Adj z v ∧ s(z,v) ∉ U) ∧
    (∀ e ∈ U, ∀ i, ∃ v ∈ A i, v ∈ e) ∧
    (∀ e ∈ U, ∃ y ∈ e, G.Adj w y ∧ s(w,y) ∉ U ∧
      ∀ S : Finset (Fin 11), y ∈ S → G.IsIndepSet (↑S) → ∃ i, Disjoint (A i) S))
  (smallObstruction : let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
    ∀ (U : Finset (Sym2 (Fin 11))) (K : Finset (Fin 11)) (w : Fin 11) (A : Fin 3 → Finset (Fin 11)),
    U ⊆ G.edgeFinset → 2 ≤ U.card → K.card ≤ U.card + 3 →
    (G.deleteEdges ↑U).IsVertexCover (↑K) →
    (∀ i, (A i).card ≤ 1 ∨ ∃ z, ∀ v ∈ A i, G.Adj z v ∧ s(z,v) ∉ U) →
    (∀ e ∈ U, ∀ i, ∃ v ∈ A i, v ∈ e) →
    (∀ e ∈ U, ∃ y ∈ e, G.Adj w y ∧ s(w,y) ∉ U ∧
      ∀ S : Finset (Fin 11), y ∈ S → G.IsIndepSet (↑S) → ∃ i, Disjoint (A i) S) → False)
  (edgeCount : let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
    ∀ D : Circuit, D.size ≤ 21 → IsLeastAO G D → TopForm G D → 2 ≤ (junk G D).card →
    let U := Ustar G D
    let B := 2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card
    (∀ u v : Fin 11, s(u,v) ∈ U → ∃ h ∈ junk G D, gateVal 11 D h (pairInput u v) = true) → 4 ≤ B → B < 2 * U.card → U.card ≤ B)
  (coverLift : let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
    ∀ D : Circuit, D.size ≤ 21 → IsLeastAO G D → TopForm G D → 2 ≤ (junk G D).card →
    let U := Ustar G D
    let B := 2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card
    U.card ≤ B → 4 ≤ B → B < 2 * U.card →
    ∃ K X : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K ∧
      G.IsVertexCover (↑(K ∪ X)) ∧ X.card ≤ B - U.card) :
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → (∀ a ∈ PEqualNP.TopForm.tops G C, Disjoint (PEqualNP.TopForm.side (n := n) C a 0) (PEqualNP.TopForm.side (n := n) C a 1) ∧ (∀ u ∈ PEqualNP.TopForm.side (n := n) C a 0, ∀ v ∈ PEqualNP.TopForm.side (n := n) C a 1, G.Adj u v) ∧ ((PEqualNP.TopForm.side (n := n) C a 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C a 1).card ≤ 1)) ∧ ∀ u v : Fin n, s(u, v) ∈ PEqualNP.TopForm.Ustar G C → ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, ∃ h ∈ PEqualNP.TopForm.junk G C, PEqualNP.EdgeOwnership.gateVal n C a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) h ∧ PEqualNP.EdgeOwnership.gateVal n C h (PEqualNP.EdgeOwnership.pairInput u v) = true) → (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card + 2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤ C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧ ∀ K : Finset (Fin n), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K → K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D → PEqualNP.TopForm.TopForm (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D → 2 ≤ (PEqualNP.TopForm.junk (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D).card → 22 ≤ D.size := by
  classical
  intro routes pre D hm ht hj
  let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  let U := Ustar G D
  let B := 2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card
  change 2 ≤ (junk G D).card at hj
  by_contra! short
  have h4 : NoFourCycle G := by dsimp [G]; decide +kernel
  have h16 : G.edgeFinset.card = 16 := by dsimp [G]; decide +kernel
  have h7 : ∀ K : Finset (Fin 11), G.IsVertexCover (K : Set (Fin 11)) → 7 ≤ K.card := by
    intro K hK
    classical
    let w (i : Fin 11) : ℕ := if i ∈ K then 1 else 0
    have ew (u v : Fin 11) (he : G.Adj u v) : 1 ≤ w u + w v := by
      rcases hK he with hu | hv
      · change u ∈ K at hu
        simp [w, hu]
      · change v ∈ K at hv
        simp [w, hv]
    have e0 := ew 1 4 (by decide +kernel)
    have e1 := ew 4 8 (by decide +kernel)
    have e2 := ew 8 1 (by decide +kernel)
    have e3 := ew 3 6 (by decide +kernel)
    have e4 := ew 6 7 (by decide +kernel)
    have e5 := ew 7 3 (by decide +kernel)
    have e6 := ew 0 9 (by decide +kernel)
    have e7 := ew 9 5 (by decide +kernel)
    have e8 := ew 5 2 (by decide +kernel)
    have e9 := ew 2 10 (by decide +kernel)
    have e10 := ew 10 0 (by decide +kernel)
    have hw : ∑ i, w i = K.card := by
      simp [w]
    rw [Fin.sum_univ_succ] at hw
    simp [Fin.sum_univ_succ] at hw
    omega
  have he : G.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  have hpre := pre 11 G D h4 he hm ht
  have hs := hpre.1
  have hk := hpre.2
  rw [h16] at hs
  change 16 + (tops G D \ centreless G D).card + 2 * (centreless G D).card +
    (junk G D).card + (orN G D \ lam G D).card ≤ D.size + U.card + 1 at hs
  have acc : 16 + (tops G D \ centreless G D).card + B ≤ D.size + U.card + 1 := by
    dsimp [B]
    omega
  by_cases loose : 2 * U.card ≤ B
  · let H := G.deleteEdges (↑U)
    let P (m : ℕ) := ∃ K : Finset (Fin 11), H.IsVertexCover (↑K) ∧ K.card = m
    have existsP : ∃ m, P m := ⟨_, Finset.univ, by simp [H], rfl⟩
    obtain ⟨K, hK, hcard⟩ := Nat.find_spec existsP
    have hmin : IsMinCover H K := by
      refine ⟨hK, fun T hT => ?_⟩
      exact hcard.trans_le (Nat.find_min' existsP ⟨T, hT, rfl⟩)
    have kt := hk K hmin
    let X := U.image (fun e => e.out.1)
    have hx : X.card ≤ U.card := Finset.card_image_le
    have cover : G.IsVertexCover (↑(K ∪ X)) := by
      intro u v huv
      by_cases eh : s(u,v) ∈ U
      · have hvx : s(u,v).out.1 ∈ X := Finset.mem_image_of_mem _ eh
        have hh := Sym2.out_fst_mem s(u,v)
        rw [Sym2.mem_iff] at hh
        rcases hh with h | h
        · exact Or.inl (Finset.mem_union_right _ (h ▸ hvx))
        · exact Or.inr (Finset.mem_union_right _ (h ▸ hvx))
      · have hh : H.Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨huv, eh⟩
        rcases hK hh with h | h
        · exact Or.inl (Finset.mem_union_left X h)
        · exact Or.inr (Finset.mem_union_left X h)
    have score := h7 _ cover
    have card := Finset.card_union_le K X
    omega
  · have routed := (routes 11 G D h4 he hm ht).2
    have small : B < 2 * U.card := Nat.lt_of_not_ge loose
    by_cases hl : B ≤ 3
    · have hu : 2 ≤ U.card := by
        have hb : 2 ≤ B := by dsimp only [B]; omega
        omega
      obtain ⟨w, A, hb, hp, hh, hsafe⟩ := smallExtract D (by omega) hm ht hj hl hu routed
      let H := G.deleteEdges (↑U)
      let P (m : ℕ) := ∃ K : Finset (Fin 11), H.IsVertexCover (↑K) ∧ K.card = m
      have existsP : ∃ m, P m := ⟨_, Finset.univ, by simp [H], rfl⟩
      obtain ⟨K, hK, hcard⟩ := Nat.find_spec existsP
      have hmin : IsMinCover H K := by
        refine ⟨hK, fun T hT => ?_⟩
        exact hcard.trans_le (Nat.find_min' existsP ⟨T, hT, rfl⟩)
      have kt := hk K hmin
      change B = 3 at hb
      exact smallObstruction U K w A Finset.sdiff_subset hu (by omega) hK hp hh hsafe
    · have high : 4 ≤ B := by omega
      have witness : ∀ u v : Fin 11, s(u,v) ∈ U → ∃ h ∈ junk G D, gateVal 11 D h (pairInput u v) = true := by
        intro u v uv
        obtain ⟨_, _, _, h, hjunk, _, _, hon⟩ := routed u v uv
        exact ⟨h, hjunk, hon⟩
      have ep := edgeCount D (by omega) hm ht hj witness high small
      obtain ⟨K, X, hK, hX, hx⟩ := coverLift D (by omega) hm ht hj ep high small
      have kt := hk K hK
      have score := h7 _ hX
      have card := Finset.card_union_le K X
      change U.card ≤ B at ep
      change X.card ≤ B - U.card at hx
      omega
