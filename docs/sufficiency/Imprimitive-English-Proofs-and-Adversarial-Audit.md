# Sufficiency of the imprimitive models — independent English proofs and adversarial audit

**Research branch only.** This note is deliberately kept under `docs/sufficiency/` in the Lean repository. It does **not** edit the EPPA III manuscript, DBW's proofs, or Sofia's Sections 7–8.

## 0. Exact logical target (important)

Let `G` be the chosen induced subgraph of a graph `H`, with an **explicit embedding** `e`. EPPA means that every partial isomorphism of `G` extends to an automorphism of `H` agreeing with that partial map along `e`. Mere graph isomorphism of an abstract host is not sufficient unless the selected embedding is transported.

The already proved `nonhomogeneous_transitive_imprimitive_eppa_global_classification` is a **NECESSITY** statement relative to the *explicit Gardiner input* for a homogeneous selected base. **The disjunction `GeneralImprimitiveHostModels` itself is not a sufficiency theorem.** Its Taylor-pattern disjunct does not assume the associated two-graph is homogeneous, while the latter condition is essential for full EPPA in the genuinely nonhomogeneous mate-free case. Furthermore, a model that is EPPA but primitive does not satisfy the imprimitive hypothesis. No reverse implication may be advertised without handling these qualifications.

We prove EPPA and transitivity for the following **positive models**, and isolate the additional finite/two-graph obligations where necessary.

## 1. Basic lift lemma (full proof)

**Lemma A.** Let `e : G → H` be an induced embedding of finite simple graphs. Suppose that `G` is homogeneous. If every full automorphism `σ` of `G` has an automorphism `σ̂` of `H` satisfying `σ̂(e(x)) = e(σ(x))` for every `x`, then `e` is an EPPA embedding.

**Proof.** Let `f : D → R` be an isomorphism between induced subgraphs of `G`. By homogeneity extend `f` to `σ ∈ Aut(G)`; then its stipulated lift `σ̂` is an automorphism of `H` agreeing with `f` on `e(D)`. This proves the actual-embedding EPPA quantifier. QED.

**Audit.** We do **not** postulate a coherent assignment `σ ↦ σ̂`. We need only existence of a lift for each `σ`. This lemma does not prove `G` homogeneous, and it does not by itself prove vertex-transitivity of `H` or imprimitivity.

## 2. Generalised clique covers, including degenerate parameters

Take the canonical disjoint union `G = sK_t` with vertices `(i,a) ∈ Fin(s) × Fin(t)`, and `H = coverGraph s t X Y` with vertices `(b,i,a)`, where `b ∈ {0,1}`. Within each side, adjacency is precisely `i=j` and `a≠a'`. Between sides, for `i=j` the relation is one of empty, full, matching, or complement matching (`X`); for `i≠j` it is empty or full (`Y`).

**Claim B.** Every such canonical cover is an EPPA witness for the **fixed first-side copy** of `sK_t`, and is vertex-transitive.

**Proof.** Every finite union of equally sized cliques is homogeneous: a partial isomorphism maps every occupied clique injectively into one clique and different occupied cliques into different target cliques; extend the partial permutation of clique indices to all indices, and extend the partial permutation within each clique to its full coordinate permutation. A full base automorphism preserves both the partition into cliques and equality of coordinates for pairs within a clique. Apply the *same* base permutation on each side of `H`; all four possibilities for `X`, and both possibilities for `Y`, are preserved. Lemma A gives EPPA. For transitivity, an automorphism of the base moves any specified `(i,a)` to any other, and the global side swap `b ↦ 1-b` exchanges the two sides while preserving the symmetric inter-side relation. QED.

**Lean already certified:** `CliqueCovers.cliqueUnion_isHomogeneous`, `CliqueCovers.uniform_cover_isEPPA`, `CliqueCovers.uniform_cover_vertex_transitive`. The cover *being imprimitive* should not be silently inferred for every parameter; only EPPA and transitivity are needed for the positive direction of the printed classification.

## 3. Wagner's exceptional graph

**Claim C.** The canonical Wagner graph on eight vertices is EPPA for its fixed induced `2K₂`, and vertex-transitive.

**Proof.** Number the eight vertices cyclically; the graph consists of an eight-cycle plus antipodal chords. Its dihedral group of order 16 preserves the graph. Every partial automorphism of `2K₂` extends to a full automorphism of the homogeneous graph `2K₂`. There are only eight full automorphisms; by explicit verification each is the restriction of one of those 16 dihedral automorphisms which maps the fixed selected four vertices to themselves. A rotation moves any vertex to any other. QED.

**Lean already certified:** `CliqueCovers.wagnerCanonicalGraph_isEPPA` and `CliqueCovers.wagnerCanonicalGraph_vertexTransitive`, with a kernel-checked finite certificate. The proof does not infer EPPA from transitivity alone.

## 4. Homogeneous selected graphs: disjoint doubles, Taylor doubles, matching doubles

Let `G` be homogeneous. The following graphs have the fixed embedding `x ↦ (0,x)`:

* **Separated double:** `H((b,x),(d,y))` iff `b=d` and `G(x,y)`. Any `σ∈Aut(G)` acts diagonally `(b,x)↦(b,σx)`.
* **Taylor double:** for `x≠y`, `H((b,x),(d,y))` iff `(b=d) ⇔ G(x,y)`, with no mate edges. The same diagonal lift works.
* **Prism/matching double:** for `b=d`, use `G(x,y)`; for `b≠d`, use `x=y`. Again the diagonal lift works.
* **Mixed matching double:** for the bottom side use `G`, on the top use `Gᶜ), and between sides connect matched vertices `x=y`. Every automorphism of `G` also preserves `Gᶜ`, so the diagonal lift works.
* **Twin blow-up:** `H((b,x),(d,y))` iff `G(x,y)`, independently of the side bits. Again the diagonal lift works. When `G` is self-complementary, this is (up to the explicitly specified relabelling of the selected base) the complement of the two-clique extension.

**Claim D.** For every homogeneous `G`, each of these five models is EPPA for the fixed selected copy of `G`.

**Proof.** Each bottom side is induced `G`. The displayed adjacency rules are invariant under `(b,x)↦(b,σx)` for every `σ∈Aut(G)`: `σ` preserves adjacency, nonadjacency, equality, and consequently every listed layer relation. Apply Lemma A. QED.

**Transitivity audit.** Homogeneous nonempty `G` is vertex-transitive. The separated double, Taylor double, same-top prism, and twin blow-up admit a global side swap; hence they are transitive. The **mixed** matching double does *not* admit a plain side swap unless `G=Gᶜ` literally (impossible on a nonempty simple-graph type with the same labelling). Instead, if `j:V≃V` exchanges the edges and nonedges of `G`, then `(b,x)↦(¬b,jx)` swaps the two sides and preserves the matching. Thus the mixed model is transitive for the self-complementary `C₅` and `R₃` cases using the *actual* verified self-complementing maps.

**Finite homogeneity audit.** To turn the general implication into unconditional EPPA theorems for `C₅` and `R₃`, a Lean proof of their graph homogeneity (or a direct finite EPPA certificate for each model) is necessary. A bare use of Gardiner's **classification** gives only a list of possible homogeneous graphs, not the converse that each named graph is homogeneous.

## 5. The unequal two-clique selected base: a genuinely nonhomogeneous sufficiency theorem

Here `G=K_l ⊔ K_k` with `l≠k` is not homogeneous. We therefore **cannot** apply Lemma A. Instead let `V` be the base vertex set, let `c:V→Bool` mark which of the two cliques contains a vertex, and let `H_{c,m}` on `Bool×V` have adjacency
`
 (b,x)∼(d,y)  ⇔  (b,x)≠(d,y) AND
 ((b⊕c(x))=(d⊕c(y)) OR (m=true AND x=y)).
`
Thus `H_{c,false}=2K_|V|` and `H_{c,true}` is two `|V|`-cliques joined by the matching pairing their corresponding vertices. The selected bottom is `G`.

**Claim E (all sizes and both mate bits).** `H_{c,m}` is EPPA for the fixed bottom `G` for **every** two-colouring `c`, including unequal, equal, and possibly empty colour classes. The host is vertex-transitive.

**Proof.** Let `f:D→f(D)` be a partial automorphism of the disjoint two-clique base. For any two distinct `x,y∈D`, preservation of adjacency and of nonadjacency gives
`
 c(x)=c(y)  ⇔  c(f(x))=c(f(y)).
`
Consequently `c(x)⊕c(f(x))` is **constant on all of D**; call the constant `δ`. (When `D` is empty, take any `δ`.) Extend `f` to an arbitrary permutation `σ` of `V`. In the Lean interface, `f` is already a permutation restricted to `D`, so we may take `σ=f` as a full set permutation, *without* assuming `f` preserves `G` outside `D`. Define
`
 q_{σ,δ}(b,x)=(b⊕c(x)⊕c(σ x)⊕δ,σ x).
`
This is a bijection: `σ` is, and for each `x` the first-coordinate change is a Boolean translation. Its global clique label transforms by
`
 q_{σ,δ}(b,x).side ⊕ c(σ x) = (b⊕c(x)) ⊕ δ.
`
It preserves equality of the second coordinates and thus every mate edge, and it preserves equality of global clique labels. Hence it is a graph automorphism of `H_{c,m}` for **either** value of `m`. For `x∈D`, we have `δ=c(x)⊕c(f(x))`, so `q_{f,δ}(0,x)=(0,f(x))`, exactly the extension required by EPPA.

For transitivity, choose `σ` moving the second coordinate of a given vertex to any prescribed second coordinate; choose `δ` to send the global clique label of the first vertex to that of the second. The same formula yields an automorphism carrying any vertex to any other. QED.

**Adversarial checks.** This proof never asserts that a partial base automorphism preserves the clique labels `c` globally. Only its *partial constant discrepancy* is used. Uniform mate adjacency is **essential**: a nonuniform matching would generally destroy the displayed automorphisms. The source manuscript's perfect matching between the *two complete host cliques* is the displayed `m=true` case, not a matching between the *original unequal base cliques*.

**Formal target:** unconditional `IsEPPAEmbedding (twoCliqueGraph c) (twoCliqueMatchedGraph c m) (bottomEmbedding V)`, and `IsVertexTransitive (twoCliqueMatchedGraph c m)`. These should be proved in a new dedicated sufficiency module and axiom-checked.

## 6. Exceptional C₅ and 3×3 rook doubles

**C₅:** (i) two disjoint cycles, (ii) Taylor double, (iii) matching prism, (iv) complement of a two-clique extension. Once `C₅` homogeneity is established, Claim D gives EPPA for the first three, and the last follows from the twin-blow-up formula plus the concrete multiplication-by-two self-complementing permutation. To identify the particular four combinatorial models with the manuscript's named graphs, use the finite adjacency identities in `BlockSystems/ExceptionalNamedModels.lean` and `CycleFiveMatchingModels.lean`. The *Petersen* top-complement matching candidate also has EPPA for `C₅` but is **primitive** and must not be included in the imprimitive necessity list; its presence is a useful sanity check against conflating EPPA with imprimitivity.

**Rook:** (i) two disjoint rook graphs, (ii) Taylor double, (iii) matching prism, (iv) complement of a two-clique extension, (v) a rook graph and its complement connected by a matching. Homogeneity of the 3×3 rook graph, Claims D, and the explicit self-complementing coordinate change `(i,j)↦(i+j,i−j)` give sufficiency. The finite named-graph equalities are checked in `ExceptionalNamedModels.lean` and `RookThreeMatchingModels.lean`.

**Adversarial issue:** A graph with the correct 10- or 18-vertex adjacency type is not automatically a witness for an *arbitrary prescribed embedding* of the base. Our claims concern the **fixed canonical bottom embedding**, followed by explicit base/host relabelling. All uses of complementation must complement the selected base as well as the host, with the self-complementing base equivalence supplied.

### 6.1 Direct finite homogeneity proof by orbit certificates

There is a proof **independent of Gardiner** that both exceptional bases are homogeneous. Let (A\leq\operatorname{Aut}(G)) be the explicit group and let (D_1,\dots,D_m) represent its orbits on vertex subsets. For each (D_i), enumerate every injection (f:D_i\to V(G)) preserving adjacency **and** nonadjacency. If each such map agrees with the restriction of an element of (A), every partial automorphism of (G) extends: conjugate the arbitrary domain to a representative, extend there and conjugate back.

- For (C_5), the dihedral group (x\mapsto a\pm x \pmod 5) has order **10**. There are **8** subset orbits, with **66** injective adjacency-preserving partial maps across their representatives. All 66 are restrictions of those automorphisms.
- For the (3\times3) rook graph, independent row/column permutations and coordinate swap form a group of order **72**. There are **26** subset orbits and **1,594** partial isomorphisms on their representatives. Each extends to a member of that explicit 72-element group.

The independently executable `checks/section6_exceptional_homogeneity.py` verifies all the declared group actions preserve the graph, the subset orbits cover the entire power set, and every injective partial isomorphism on each representative extends to the group, using exhaustive backtracking. This yields a complete **English/computational finite proof** of homogeneity without Gardiner.

**Trust boundary:** the enumerations are independently checked by Python, **not yet kernel checked in Lean**. The conditional homogeneous-base Lean EPPA lifts below can use these mathematical facts only after their Lean proofs or an honest explicit external assumption.

## 7. Nontrivial homogeneous two-graphs: the icosahedron and J(6,3)

Let `Δ` be the odd-edge-parity two-graph of a selected representative `G`, and `T(G)` its mate-free Taylor double. Suppose **`Δ` is homogeneous**. Given a partial automorphism of any switching transversal, it preserves the parity of every selected triple and hence extends to an automorphism `σ` of `Δ`. Every `σ` has a Taylor-double lift `q` using the switching potential. A priori the lift may map the chosen transversal to its opposite side on some vertices. But for any two vertices in the prescribed partial domain, preservation of their graph adjacency makes the side discrepancy equal; thus it is globally constant on that domain. Composing `q` with the global deck involution if necessary corrects that common side. Hence **every** switching representative is an EPPA transversal. The host is transitive whenever `Δ` is point-transitive; homogeneity implies point-transitivity for a nonempty two-graph. This is the *sufficiency direction* of the four-way two-graph theorem.

**Lean already certified:** `TwoGraphs.homogeneous_two_graph_all_transversals_eppa` and `TwoGraphs.all_taylor_transversals_eppa_iff_homogeneous_two_graph`. The other direction of this equivalence has also been checked, without Gardiner.

**External outstanding identification:** The classification of finite homogeneous two-graphs as trivial or the unique nontrivial 6- and 10-point examples is **not** a Lean theorem in this repository. To conclude unconditional EPPA of the *named* icosahedron and Johnson graph `J(6,3)`, one must (a) construct explicit 6/10-point two-graphs and prove their homogeneity, or use a separately identified external theorem **and** (b) prove a labelled graph equivalence from their Taylor doubles to these named hosts, taking the selected transversals with them. A classification theorem which only says every homogeneous two-graph belongs to a list is **not sufficient** to prove that every item in that list is homogeneous, absent the converse/existence part. Until then the general implication is formally certified, while unconditional named-model certification is pending.

## 8. Complements and relabellings (fully accounted for)

If `e:G→H` is EPPA, then the same chosen vertex injection `e:Gᶜ→Hᶜ` is EPPA: a partial isomorphism preserves edge and nonedge information in either graph, and every automorphism of `H` preserves its complement. If `φ:K≃G` is a graph equivalence, precompose the embedding and conjugate the partial maps. These are already formally proved as `EPPAIII.eppa_embedding_complement` and `EPPAIII.eppa_relabel_base`; no new correctness hypothesis is introduced.

## 9. Independent adversarial audit — what would make a closure claim false

1. **Raw necessity vs positive classification.** The Taylor disjunct of `GeneralImprimitiveHostModels` does not imply EPPA for all choices of `G`. Require two-graph homogeneity (or the appropriate direct finite certificate) before asserting sufficiency. This is a **logical obstacle**, not just a missing tactic.
2. **Uniform generalized covers.** The uniformity of **every** diagonal/offdiagonal entry is used in the diagonal permutation lift. An arbitrary matrix of matching entries need not have a coherent alignment and is not covered.
3. **Unequal cliques.** A direct `Aut(G)` lift **fails** when the two original clique sizes differ; Claim E uses arbitrary global permutations of the *index set*, and adjusts the side bit on each fibre. Check its constant-δ lemma on domains of size zero or one.
4. **Matching vs no matching.** The mate parameter is preserved by the explicitly constructed lifts, but cannot simply be inserted into arbitrary Taylor double automorphisms without proving those automorphisms preserve fibres.
5. **Exceptional graph homogeneity.** The Gardiner list is not a Lean proof of finite homogeneity of its members. Supply independent evidence when converting generic conditional statements to unconditional certificates.
6. **Primitive exceptions.** The Petersen case must not be treated as an imprimitive host merely because it has a two-half representation; likewise some generalized covers may have other block structures. EPPA, transitivity and imprimitivity are separate predicates.
7. **6/10 homogeneous two-graphs.** The implication homogeneous → EPPA is proved; the named two-graphs' homogeneity and concrete identifications are still explicit obligations unless independently certified.
8. **Translating from a labelled model.** Composing a host graph equivalence and a base graph equivalence must retain the induced embedding, not merely the isomorphism class of the host.
9. **No manuscript modifications.** This note belongs to the Lean repository; the printed English remains subject to its own correction cycle.

## 10. Completion checklist

| Family or bridge | English proof | Lean certificate |
|---|---|---|
| Generalized clique covers, all X/Y and s,t | §2 | Already verified |
| Wagner graph over 2K₂ | §3 | Already verified |
| Complement / base relabelling | §8 | Already verified |
| Homogeneous-base separated/Taylor/prism/mixed/twin graph lift | §4 | Generic framework to formalize |
| Unequal two-clique base, both mate bits | §5 | New unconditional theorem to formalize |
| C₅ and rook named graph EPPA | §6 | Requires homogeneity/dedicated finite EPPA certificates |
| Homogeneous two-graph → all switching representatives EPPA | §7 | Already verified |
| Explicit 6- and 10-point two-graphs homogeneous, with named-host identifications | §7 | Not yet verified; cannot claim full completion |
| Necessity ↔ sufficiency of the **exact printed imprimitive cases** | All | Only after all pending model/embedding cases and imprimitive-vs-primitive qualifications are accounted for |

**Audit verdict at this stage:** the five lifting arguments above are mathematically valid with their exact stated hypotheses. They provide a route to complete sufficiency, but the word “complete” must be reserved until the outstanding finite identity/homogeneity and exact-case converse obligations have passed Lean CI.
