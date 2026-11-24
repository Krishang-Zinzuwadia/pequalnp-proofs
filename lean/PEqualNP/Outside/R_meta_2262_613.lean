import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

-- Give the protected groups to the finite graph inequality in the branches
-- with no mixing gate and at most one OR outside Lambda.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 50000 in
theorem PEqualNP.Outside.R_meta_2262_613
  (finiteGroups : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (U : Finset (Sym2 (Fin 11)))
    (K : Finset (Fin 11)) (r : ℕ) (E : Fin r → Finset (Sym2 (Fin 11))),
    G = edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
    U ⊆ G.edgeFinset → (G.deleteEdges ↑U).IsVertexCover (↑K) →

    (∀ e ∈ U, ∃ i, e ∈ E i) → (∀ i, E i ⊆ U) →
    (∀ i, ∃ A : List (Finset (Fin 11)),
      (∀ S ∈ A, S.card ≤ 1 ∨ ∃ w, ∀ v ∈ S, G.Adj w v ∧ s(w,v) ∉ U) ∧
      (∀ e ∈ E i, ∀ S ∈ A, ∃ v ∈ S, v ∈ e) ∧
      ∀ X : Finset (Fin 11), G.IsIndepSet (↑X) → ∃ S ∈ A, Disjoint S X) →
    U.card + 6 ≤ K.card + 2 * r)
  (extract : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : Circuit) (g h : ℕ),
    G.edgeFinset.Nonempty →
    IsLeastAO G D → TopForm G D →

    let T := tops G D
    let U := Ustar G D
    let z := (centreless G D).card
    let o := (orN G D \ lam G D).card
    let ic := InCone 11 D
    (∀ u v : Fin 11, s(u,v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ j ∈ junk G D,
      gateVal 11 D a (pairInput u v) = true ∧ OrReaches 11 D (opnd D a b) j ∧
      gateVal 11 D j (pairInput u v) = true) →
    starEdges G D ⊆ G.edgeFinset →
    g < h → junk G D = {g,h} → ¬ ic g h → ¬ ic h g → (∃ a ∈ T, ic g a ∧ ic h a) →

    (o = 0 ∨ o = 1 ∧ mixing G D = ∅) →
    ∃ (r : ℕ) (E : Fin r → Finset (Sym2 (Fin 11))), r ≤ z + o ∧

    (∀ e ∈ U, ∃ i, e ∈ E i) ∧ (∀ i, E i ⊆ U) ∧
    (∀ i, ∃ A : List (Finset (Fin 11)),
      (∀ S ∈ A, S.card ≤ 1 ∨ ∃ w, ∀ v ∈ S, G.Adj w v ∧ s(w,v) ∉ U) ∧
      (∀ e ∈ E i, ∀ S ∈ A, ∃ v ∈ S, v ∈ e) ∧
      ∀ X : Finset (Fin 11), G.IsIndepSet (↑X) → ∃ S ∈ A, Disjoint S X))
  (interacting : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : Circuit) (g h : ℕ) (K : Finset (Fin 11)),
    G = edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
    D.size ≤ 21 → IsLeastAO G D → TopForm G D →

    let T := tops G D
    let U := Ustar G D
    let z := (centreless G D).card
    let o := (orN G D \ lam G D).card
    let ic := InCone 11 D
    (∀ u v : Fin 11, s(u,v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ j ∈ junk G D,
      gateVal 11 D a (pairInput u v) = true ∧ OrReaches 11 D (opnd D a b) j ∧
      gateVal 11 D j (pairInput u v) = true) →
    starEdges G D ⊆ G.edgeFinset →
    g < h → junk G D = {g,h} → ¬ ic g h → ¬ ic h g → (∃ a ∈ T, ic g a ∧ ic h a) →

    IsMinCover (G.deleteEdges ↑U) K →
    K.card ≤ (T \ centreless G D).card →
    (T \ centreless G D).card + 2 * z + o ≤ U.card + 4 →
    2 * z + 2 + o < 2 * U.card →
    (o = 1 ∧ (mixing G D).Nonempty ∨ o = 2 ∧ z = 0) → False)
  (larger : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : Circuit) (g h : ℕ) (K : Finset (Fin 11)),
    G = edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
    D.size ≤ 21 → IsLeastAO G D → TopForm G D →

    let T := tops G D
    let U := Ustar G D
    let z := (centreless G D).card
    let o := (orN G D \ lam G D).card
    let ic := InCone 11 D
    (∀ u v : Fin 11, s(u,v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ j ∈ junk G D,
      gateVal 11 D a (pairInput u v) = true ∧ OrReaches 11 D (opnd D a b) j ∧
      gateVal 11 D j (pairInput u v) = true) →
    starEdges G D ⊆ G.edgeFinset →
    g < h → junk G D = {g,h} → ¬ ic g h → ¬ ic h g → (∃ a ∈ T, ic g a ∧ ic h a) →

    IsMinCover (G.deleteEdges ↑U) K →
    K.card ≤ (T \ centreless G D).card →
    (T \ centreless G D).card + 2 * z + o ≤ U.card + 4 →
    2 * z + 2 + o < 2 * U.card →
    (3 ≤ o ∨ 2 ≤ o ∧ 1 ≤ z) → False) :
  ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         have x12 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;         (∀ x13 ∈ x9,             have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;             (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧ ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x11 → ∃ x17 ∈ x9, ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ), (x19 = x4 ∨ x19 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x16 → x16.card ≤ (x9 \ x10).card) → x4 < x5 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬x12 x4 x5 → ¬x12 x5 x4 → (∃ x21 ∈ x9, x12 x4 x21 ∧ x12 x5 x21) → (22 : ℕ) ≤ x3.size := by
  classical
  intro G _ D g h hGraph hLeast hTop oldT oldZ oldU oldIC hStar hRoutes hBudget hCover hOrder hJunk hNo1 hNo2 hCommon
  let T := tops G D
  let U := Ustar G D
  let z := (centreless G D).card
  let o := (orN G D \ lam G D).card
  by_contra! hShort
  have short : D.size ≤ 21 := by omega
  have counted : (T \ centreless G D).card + 2 * z + o ≤ U.card + 4 := by
    change 17 + (T \ centreless G D).card + 2 * z + o ≤ D.size + U.card at hBudget
    omega
  have routes : ∀ u v : Fin 11, s(u,v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ j ∈ junk G D,
      gateVal 11 D a (pairInput u v) = true ∧ OrReaches 11 D (opnd D a b) j ∧
      gateVal 11 D j (pairInput u v) = true := by
    intro u v he
    obtain ⟨a, ha, b, j, hj, hval, hr, hJ⟩ := hRoutes u v he
    exact ⟨a, ha, b, j, by rw [hJunk]; simpa only [Finset.mem_insert, Finset.mem_singleton] using hj,
      hval, hr, hJ⟩
  have stars : starEdges G D ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨a, ha, hb⟩ := Finset.mem_biUnion.mp he
    obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hb
    rw [← hpe, SimpleGraph.mem_edgeFinset]
    exact (hStar a ha).1 p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2
  let H := G.deleteEdges (↑U)
  let P (m : ℕ) := ∃ K : Finset (Fin 11), H.IsVertexCover (↑K) ∧ K.card = m
  have existsP : ∃ m, P m := ⟨_, Finset.univ, by simp [H], rfl⟩
  obtain ⟨K, hK, hCard⟩ := Nat.find_spec existsP
  have hMin : IsMinCover H K := by
    refine ⟨hK, fun W hW => ?_⟩
    exact hCard.trans_le (Nat.find_min' existsP ⟨W, hW, rfl⟩)
  have kBound : K.card ≤ (T \ centreless G D).card := hCover K hMin
  have coverLift : ∃ X : Finset (Fin 11), G.IsVertexCover (↑(K ∪ X)) ∧ X.card ≤ U.card := by
    let X := U.image (fun e => e.out.1)
    refine ⟨X, ?_, Finset.card_image_le⟩
    intro u v huv
    by_cases he : s(u,v) ∈ U
    · have hvx : s(u,v).out.1 ∈ X := Finset.mem_image_of_mem _ he
      have hh := Sym2.out_fst_mem s(u,v)
      rw [Sym2.mem_iff] at hh
      rcases hh with h1 | h2
      · exact Or.inl (Finset.mem_union_right _ (h1 ▸ hvx))
      · exact Or.inr (Finset.mem_union_right _ (h2 ▸ hvx))
    · have hh : H.Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨huv, he⟩
      rcases hK hh with h1 | h2
      · exact Or.inl (Finset.mem_union_left X h1)
      · exact Or.inr (Finset.mem_union_left X h2)
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
    have e0 := ew 1 4 (by rw [hGraph]; decide +kernel)
    have e1 := ew 4 8 (by rw [hGraph]; decide +kernel)
    have e2 := ew 8 1 (by rw [hGraph]; decide +kernel)
    have e3 := ew 3 6 (by rw [hGraph]; decide +kernel)
    have e4 := ew 6 7 (by rw [hGraph]; decide +kernel)
    have e5 := ew 7 3 (by rw [hGraph]; decide +kernel)
    have e6 := ew 0 9 (by rw [hGraph]; decide +kernel)
    have e7 := ew 9 5 (by rw [hGraph]; decide +kernel)
    have e8 := ew 5 2 (by rw [hGraph]; decide +kernel)
    have e9 := ew 2 10 (by rw [hGraph]; decide +kernel)
    have e10 := ew 10 0 (by rw [hGraph]; decide +kernel)
    have hw : ∑ i, w i = K.card := by
      simp [w]
    rw [Fin.sum_univ_succ] at hw
    simp [Fin.sum_univ_succ] at hw
    omega
  have strict : 2 * z + 2 + o < 2 * U.card := by
    obtain ⟨X, hX, hx⟩ := coverLift
    have hc := h7 _ hX
    have hd := Finset.card_union_le K X
    omega
  have nonempty : G.edgeFinset.Nonempty :=
    ⟨s((1 : Fin 11), (4 : Fin 11)), SimpleGraph.mem_edgeFinset.mpr (by rw [hGraph]; decide +kernel)⟩
  by_cases low : o = 0 ∨ o = 1 ∧ mixing G D = ∅
  · obtain ⟨r, E, hr, hu, he, hg⟩ :=
      extract G D g h nonempty hLeast hTop routes stars hOrder hJunk hNo1 hNo2 hCommon low
    have bound := finiteGroups G U K r E hGraph Finset.sdiff_subset hK hu he hg
    have ho : o ≤ 1 := by rcases low with hp | hp <;> omega
    omega
  · by_cases high : 3 ≤ o ∨ 2 ≤ o ∧ 1 ≤ z
    · exact larger G D g h K hGraph short hLeast hTop routes stars hOrder hJunk hNo1 hNo2 hCommon
        hMin kBound counted strict high
    · have mid : o = 1 ∧ (mixing G D).Nonempty ∨ o = 2 ∧ z = 0 := by
        by_cases h1 : o = 1
        · refine Or.inl ⟨h1, Finset.nonempty_iff_ne_empty.mpr ?_⟩
          intro hm
          exact low (Or.inr ⟨h1, hm⟩)
        · apply Or.inr
          have hz : o ≠ 0 := fun hh => low (Or.inl hh)
          have ho : o = 2 := by omega
          have hz : z = 0 := by
            by_contra hn
            exact high (Or.inr ⟨by omega, by omega⟩)
          exact ⟨ho, hz⟩
      exact interacting G D g h K hGraph short hLeast hTop routes stars hOrder hJunk hNo1 hNo2 hCommon
        hMin kBound counted strict mid
