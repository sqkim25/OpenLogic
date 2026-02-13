## CH-MOD (feeds into CH-META and CH-SEM)

### mod/bas/red -- Reducts and Expansions
- **Action**: CONDENSE
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.6: Model-Theoretic Concepts
- **Rationale**: STEPPING-STONE. Introduces reduct/expansion notation (SUPPORT-DEF) used heavily by interpolation (Expan{M}{R} notation) and substructure definitions. No taxonomy items introduced, but structurally necessary for DEF-SEM011 and CP-011/CP-012.
- **Content Directives**:
  - Formal items to preserve: defn[defn:reduct] (reduct/expansion definition), defn (Expan{M}{R} notation)
  - Formal items to drop: prop[prop:reduct] -- stepping stone; statement can be preserved as a one-line remark, proof cut (exercise in OL)
  - Prose: compress to intro+definition only
  - Examples: cut all
  - Proofs: cut (prop:reduct proof is an exercise)

---

### mod/bas/sub -- Substructures
- **Action**: KEEP
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.6: Model-Theoretic Concepts
- **Rationale**: CORE-DEF. Defining occurrence of DEF-SEM011 (Substructure). Note: SECTION-MAP identifies this as DEF-SEM011 but the taxonomy spec DOMAIN-SEMANTICS.md uses PRIM-SEM013 for Substructure. The SECTION-MAP maps defn[defn:substructure] to DEF-SEM011. We follow the SECTION-MAP: this is the authoritative home for the substructure definition regardless of ID numbering. Short section, minimal editing needed.
- **Content Directives**:
  - Formal items to preserve: defn[defn:substructure] (DEF-SEM011 / PRIM-SEM013 -- substructure definition)
  - Formal items to drop: none
  - Prose: preserve (brief and on-point)
  - Examples: preserve rem[rem:substructure] -- relational substructure simplification used by Lindstrom chapter
  - Proofs: N/A

---

### mod/bas/ove -- Overspill
- **Action**: CONDENSE
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.7: Theorems (as application of compactness)
- **Rationale**: STEPPING-STONE. The overspill theorem and the non-expressibility of finiteness in FOL are classic compactness applications. The finiteness result (prop[inf-not-fo]) is significant for CP-013 context (FOL expressiveness limits). No taxonomy items introduced, but both results merit preservation as compact statements.
- **Content Directives**:
  - Formal items to preserve: thm[overspill] (overspill theorem), prop[inf-not-fo] (finiteness not FO-expressible)
  - Formal items to drop: none
  - Prose: compress to intro+definition only (one sentence motivation)
  - Examples: cut all
  - Proofs: preserve sketch only for thm[overspill] (compactness argument in 2 sentences); preserve full for prop[inf-not-fo] (already a 3-line proof)

---

### mod/bas/iso -- Isomorphic Structures
- **Action**: KEEP
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.6: Model-Theoretic Concepts
- **Rationale**: CORE-DEF. Defining occurrence of PRIM-SEM013 (Elementary Equivalence, mapped as defn[defn:elem-equiv]), DEF-SEM013 (Isomorphism of Structures, mapped as defn[defn:isomorphism]), and THM-SEM001 (Isomorphism Lemma, mapped as thm[thm:isom]). Three taxonomy items introduced in one section -- all are authoritative. Critical section referenced throughout model theory.
- **Content Directives**:
  - Formal items to preserve: defn[defn:elem-equiv] (PRIM-SEM013 / DEF-SEM008), defn[defn:isomorphism] (DEF-SEM013 / PRIM-SEM012), thm[thm:isom] (THM-SEM001), defn (automorphism) -- useful SUPPORT-DEF
  - Formal items to drop: none
  - Prose: preserve (introductory paragraph motivating the distinction between elementary equivalence and isomorphism is pedagogically tight)
  - Examples: cut all (no examples in section, only exercises)
  - Proofs: preserve full for thm[thm:isom] (the term-valuation part (a) is given; part (b) is an exercise -- preserve part (a), note part (b) as exercise)

---

### mod/bas/thm -- The Theory of a Structure
- **Action**: KEEP
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.6: Model-Theoretic Concepts
- **Rationale**: CORE-DEF. Defining occurrence of PRIM-SEM012 (Theory of a Structure, Th(M)). Note: The taxonomy DOMAIN-SEMANTICS.md uses DEF-SEM006 for "Theory of a Structure" while the SECTION-MAP uses PRIM-SEM012. We follow the SECTION-MAP entry. This is the authoritative home for the Th(M) definition. Also establishes that Th(M) is complete and connects elementary equivalence to Th(M).
- **Content Directives**:
  - Formal items to preserve: defn (Theory of M, Th(M)) -- PRIM-SEM012 / DEF-SEM006, prop (Th(M) is complete), prop[prop:equiv] (models of Th(M) are elementarily equivalent)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: keep rem[remark:R] (Lowenheim-Skolem counterexample showing iso is strictly stronger than elem-equiv -- canonical example, referenced by mod/bas/dlo)
  - Proofs: preserve full (all proofs are 2-4 lines)

---

### mod/bas/pis -- Partial Isomorphisms
- **Action**: CONDENSE
- **Lean Chapter**: CH-META
- **Lean Section**: META.11: Lindstrom's Theorem (technical infrastructure)
- **Rationale**: STEPPING-STONE for Lindstrom's theorem. Heavy section developing the back-and-forth method, Ehrenfeucht-Fraisse games (I_n relations), quantifier rank, and n-equivalence. None are taxonomy items, but all are essential infrastructure for CP-013. The back-and-forth results (thm:p-isom1, thm:p-isom2, thm:b-n-f) are used directly in the Lindstrom proof chain. Condense by preserving all key definitions and theorem statements but compressing proofs.
- **Content Directives**:
  - Formal items to preserve: defn (partial isomorphism), defn[defn:partialisom] (partial isomorphism with back-and-forth), thm[thm:p-isom1] (enumerable partially iso structures are iso), thm[thm:p-isom2] (partial iso implies elem equiv for relational languages), defn (quantifier rank, n-equivalence), prop[prop:qr-finite] (finitely many sentences per quantifier rank), defn (I_n relations), defn (approx_n), thm[thm:b-n-f] (I_n and n-equivalence connection), cor[cor:b-n-f]
  - Formal items to drop: rem (function case for thm:p-isom2) -- one-sentence remark, can be inlined as a note
  - Prose: compress to intro+definition only; cut the connecting narrative between definitions
  - Examples: cut all
  - Proofs: preserve sketch only for thm[thm:p-isom1] (back-and-forth construction outline in 3 sentences); preserve sketch only for thm[thm:p-isom2] (induction sketch in 2 sentences); cut proof of prop[prop:qr-finite] (stated as "by induction on n" in OL); preserve sketch only for thm[thm:b-n-f] (forward direction easy induction; converse uses prop:qr-finite -- 4-sentence sketch)

---

### mod/bas/dlo -- Dense Linear Orders
- **Action**: KEEP
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.6: Model-Theoretic Concepts
- **Rationale**: CORE-THM. Demonstrates DEF-SEM006 / DEF-SEM014 (Categoricity) via the canonical example: Cantor's theorem on aleph-0 categoricity of DLO (thm[thm:cantorQ]). This is the defining exemplification of categoricity in OL. The proof applies the back-and-forth method. GAP: An explicit formal definition of "kappa-categorical" should be added by Phase 4 (from DOMAIN-SEMANTICS DEF-SEM014) before this theorem.
- **Content Directives**:
  - Formal items to preserve: defn (DLO axioms), thm[thm:cantorQ] (Cantor's theorem: aleph-0 categoricity of DLO)
  - Formal items to drop: none
  - Prose: preserve (tight)
  - Examples: keep rem (R elementarily equivalent to Q) -- directly illustrates the theorem and connects to mod/bas/thm remark:R
  - Proofs: preserve full for thm[thm:cantorQ] (clean back-and-forth proof, canonical example of the technique)

---

### mod/bas/nsa -- Non-standard Models of Arithmetic (COMMENTED OUT)
- **Action**: CUT
- **Lean Chapter**: N/A
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Section is commented out in basics.tex (line 24: `%\olimport{nonstandard-arithmetic}`). Content substantially overlaps with mod/mar/nst (non-standard models via compactness) and mod/mar/mpa (block structure analysis). The standard model/true arithmetic definitions duplicate mod/mar/int and mod/mar/stm. The existence proof for non-standard models is the same compactness argument in mod/mar/nst. The block analysis (items 1-13) is reproduced with more detail in mod/mar/mpa.
- **Content Directives**:
  - Formal items to preserve: none (all subsumed by mod/mar/*)
  - Formal items to drop: all -- defn (standard model, true arithmetic) subsumed by mod/mar/stm; defn (standard/non-standard structure) subsumed by mod/mar/nst; thm[thm:non-std] subsumed by mod/mar/nst; block analysis (items 1-13) subsumed by mod/mar/mpa
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: cut all

---

### mod/mar/int -- Introduction (Models of Arithmetic)
- **Action**: CUT
- **Lean Chapter**: N/A
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Narrative introduction with no labeled formal environments. Motivational paragraph connecting non-standard models to incompleteness phenomena (Con(PA) and its negation). The content about non-standard witnesses for Con(PA) is interesting but tangential -- it is better placed as a remark in the incompleteness chapter (CH-META, META.6) rather than in the model theory feed. No taxonomy items introduced.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: cut entirely (motivational only)
  - Examples: cut all
  - Proofs: N/A

---

### mod/mar/stm -- Standard Models of Arithmetic
- **Action**: CONDENSE
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.5: Arithmetic Models
- **Rationale**: STEPPING-STONE. Establishes the technical notion of "standard structure" (isomorphic to N) and proves key stepping-stone results: domain = values of standard numerals, model of Q with only standard elements is standard, uniqueness of isomorphism. These support the non-standard model existence proof in mod/mar/nst. No taxonomy items introduced (these are SUPPORT-DEFs), but they are needed by the mod/mar chain.
- **Content Directives**:
  - Formal items to preserve: defn (standard structure = isomorphic to N), prop[prop:standard-domain] (domain equals numeral values), prop[prop:thq-standard] (model of Q with only standard elements is standard)
  - Formal items to drop: prop[prop:thq-unique-iso] (uniqueness of isomorphism -- stepping stone not needed downstream)
  - Prose: compress to intro+definition only
  - Examples: cut all (explain blocks cut)
  - Proofs: preserve sketch only for prop[prop:standard-domain] (surjectivity from isomorphism, 2 sentences); preserve sketch only for prop[prop:thq-standard] (injectivity via Q provability, 3 sentences)

---

### mod/mar/nst -- Non-Standard Models
- **Action**: KEEP
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.5: Arithmetic Models
- **Rationale**: CORE-THM. Contains the canonical compactness-based existence proof for non-standard models of true arithmetic (TA). This is a fundamental application of CP-003 (Compactness). The existence of non-standard models is prerequisite for the structural analysis in mod/mar/mpa and connects to Tennenbaum's theorem in mod/mar/cmp. The proof is clean and self-contained.
- **Content Directives**:
  - Formal items to preserve: defn (non-standard structure, non-standard numbers), prop (non-standard element implies non-standard structure), prop (TA has enumerable non-standard model -- existence proof)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: keep explain block (Z as trivial non-standard structure for LA, showing it is not a model of arithmetic -- simple motivating example)
  - Proofs: preserve full (compactness argument is the canonical application)

---

### mod/mar/mdq -- Models of Q
- **Action**: CUT
- **Lean Chapter**: N/A
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Purely pedagogical section constructing explicit models K and L of Robinson arithmetic Q. Demonstrates Q is weak enough to have simple non-standard models (successor-fixed-point) and that Q does not prove commutativity of addition. While illustrative, no taxonomy items are introduced, and the content is not needed by any downstream proof chain. The lean text's coverage of non-standard models (mod/mar/nst, mod/mar/mpa) focuses on TA/PA, where Q-specific models are not relevant.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: ex[ex:model-K-of-Q] (pedagogical), ex[ex:model-L-of-Q] (pedagogical) -- both are detailed constructions with no downstream dependencies
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: N/A (no theorems)

---

### mod/mar/mpa -- Models of PA
- **Action**: CONDENSE
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.5: Arithmetic Models
- **Rationale**: STEPPING-STONE. Detailed structural analysis of non-standard models of PA, culminating in the result that non-standard blocks are ordered like the rationals (omega + Q*Z structure). This is a rich structural analysis that deeply applies categoricity (DLO) and elementary equivalence. No taxonomy items introduced, but the block structure result is a significant model-theoretic fact. Condense by preserving key propositions (discrete ordering, block definition, density of blocks) while cutting detailed verification steps.
- **Content Directives**:
  - Formal items to preserve: prop (nsless is linear strict order), prop[prop:M-discrete] (0 least, successor immediate, predecessor exists), prop (standard less than nonstandard), prop (block of x -- definition), prop[prop:blocks-dense] (blocks are dense)
  - Formal items to drop: cor (disjoint blocks) -- immediate consequence; prop (nonstandard addition leaves block) -- stepping stone for density; prop (no least nonstandard block) -- can be stated as remark; prop (no largest block) -- can be stated as remark
  - Prose: compress to intro+definition only; preserve the concluding explain block summarizing omega+Q*Z structure (key result statement)
  - Examples: cut all
  - Proofs: preserve sketch only for prop[prop:M-discrete] (exercise in OL; note "follows from PA-provable sentences"); preserve sketch only for prop[prop:blocks-dense] (divisibility-by-2 argument in 3 sentences); cut remaining proofs (stepping-stone verifications)

---

### mod/mar/cmp -- Computable Models of Arithmetic
- **Action**: CONDENSE
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.5: Arithmetic Models
- **Rationale**: CORE-THM (Tennenbaum's theorem statement). Introduces the notion of computable model (SUPPORT-DEF) and states Tennenbaum's theorem (N is the only computable model of PA) without proof. The theorem connects model theory to computability and is a significant structural result. However, no proof is given in OL, so the section is already minimal. Condense by cutting the pedagogical example (K' computable model of Q) and preserving the definition and theorem statement.
- **Content Directives**:
  - Formal items to preserve: defn (computable structure), thm (Tennenbaum's Theorem -- statement only, no proof in OL)
  - Formal items to drop: ex[ex:comp-model-q] (pedagogical -- explicit construction of computable K' isomorphic to model K of Q; depends on cut section mod/mar/mdq)
  - Prose: compress to intro+definition only (2 sentences motivating computable models + definition + theorem)
  - Examples: cut ex[ex:comp-model-q]
  - Proofs: N/A (Tennenbaum stated without proof)

---

### mod/int/int -- Introduction (Interpolation)
- **Action**: CUT
- **Lean Chapter**: N/A
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Brief motivational paragraph (6 sentences) stating the interpolation theorem informally and previewing Beth definability and Robinson joint consistency. No formal items. The lean text's META.9 section will have its own brief introduction.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: N/A

---

### mod/int/sep -- Separation of Sentences
- **Action**: CONDENSE
- **Lean Chapter**: CH-META
- **Lean Section**: META.9: Craig Interpolation (technical infrastructure)
- **Rationale**: STEPPING-STONE. Introduces the dual formulation of interpolation (separation/inseparability) and proves two key lemmas (lem:sep1 on constant expansion preserving inseparability, lem:sep2 on witnessing preserving inseparability) used directly in the interpolation proof (mod/int/prf). Essential technical machinery. Condense by preserving all formal items but compressing the prose and the diagram.
- **Content Directives**:
  - Formal items to preserve: defn (separation, inseparability), lem[lem:sep1] (inseparability preserved under constant expansion), lem[lem:sep2] (inseparability preserved under witnessing)
  - Formal items to drop: none
  - Prose: compress to intro+definition only (drop the figure; keep 2-sentence motivation connecting separation to interpolation)
  - Examples: cut all (drop figure fig:sep)
  - Proofs: preserve full for lem[lem:sep1] (compactness + generalization argument, essential for interpolation proof); preserve full for lem[lem:sep2] (two-case argument, essential for interpolation proof)

---

### mod/int/prf -- Craig's Interpolation Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.9: Craig Interpolation
- **Rationale**: CORE-THM. Defining occurrence of CP-011 (Craig's Interpolation Theorem). Full proof via the inseparability/maximally consistent pair construction. The proof uses compactness (CP-003) and completeness (CP-002). This is one of the 13 composition patterns and must be preserved in full.
- **Content Directives**:
  - Formal items to preserve: thm[thm:interpol] (CP-011 -- Craig's Interpolation Theorem, full statement + proof)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: cut all (none present)
  - Proofs: preserve full (the complete proof is the core content; it is the defining occurrence of CP-011)

---

### mod/int/def -- The Definability Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.10: Beth Definability
- **Rationale**: CORE-THM. Defining occurrence of CP-012 (Beth's Definability Theorem). Full proof as a consequence of Craig's Interpolation Theorem (CP-011). Also introduces the formal notions of explicit and implicit definability (SUPPORT-DEFs needed for the theorem statement). Must be preserved in full.
- **Content Directives**:
  - Formal items to preserve: defn (explicit definition of P), defn (implicit definition of P), thm (Beth Definability Theorem -- CP-012, full statement + proof)
  - Formal items to drop: none
  - Prose: preserve (the motivating paragraph connecting implicit to explicit definability is essential context)
  - Examples: cut all (none present beyond the in-proof notation)
  - Proofs: preserve full (the proof via Craig interpolation is the core content; it is the defining occurrence of CP-012)

---

### mod/lin/int -- Introduction (Lindstrom)
- **Action**: CUT
- **Lean Chapter**: N/A
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Single motivational paragraph (4 sentences) stating the goal of characterizing FOL as maximal logic with compactness + downward Lowenheim-Skolem. No formal items. The lean text's META.11 section will have its own brief introduction.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: N/A

---

### mod/lin/alg -- Abstract Logics
- **Action**: MERGE-INTO:mod/lin/prf
- **Lean Chapter**: CH-META
- **Lean Section**: META.11: Lindstrom's Theorem
- **Rationale**: STEPPING-STONE. Introduces the framework of abstract logics (4 definitions: abstract logic, Mod/elementary equivalence in L, normal abstract logic with 7 properties, expressiveness comparison) needed for Lindstrom's theorem statement. These are SUPPORT-DEFs for CP-013 -- none are standalone taxonomy items. The definitions are compact and should be absorbed into the Lindstrom section (mod/lin/prf) as preliminary definitions, since they serve no purpose outside the Lindstrom proof. The remark that FOL is normal is a useful sanity check to preserve.
- **Content Directives**:
  - Formal items surviving in merge target (mod/lin/prf): defn (abstract logic), defn (Mod(L), elementary equivalence in L), defn (normal abstract logic, 7 properties), defn (at least as expressive, equivalent logics)
  - Formal items to drop: rem (first-order logic is normal) -- can be compressed to a one-line note after the normal logic definition
  - Prose: compress to definitions only (cut the explanatory paragraph about infinitary logics)
  - Examples: cut all
  - Proofs: N/A (no proofs)

---

### mod/lin/lsp -- Compactness and Lowenheim-Skolem Properties
- **Action**: MERGE-INTO:mod/lin/prf
- **Lean Chapter**: CH-META
- **Lean Section**: META.11: Lindstrom's Theorem
- **Rationale**: STEPPING-STONE. Defines the Compactness Property and Downward Lowenheim-Skolem Property for abstract logics, and proves the key theorem (thm:abstract-p-isom) that partially isomorphic structures are L-equivalent under the LS property. All three items are essential infrastructure for the Lindstrom proof but have no standalone role outside CP-013. Merge into mod/lin/prf to create a single self-contained Lindstrom section.
- **Content Directives**:
  - Formal items surviving in merge target (mod/lin/prf): defn (Compactness Property for abstract logics), defn (Downward LS property), thm[thm:abstract-p-isom] (partially isomorphic structures are L-equivalent under LS)
  - Formal items to drop: none
  - Prose: compress connecting text to 2 sentences motivating the generalization from FOL to abstract logics
  - Examples: cut all
  - Proofs: preserve sketch only for thm[thm:abstract-p-isom] (construction of combined structure M with internal partial isomorphism, appeal to LS property for countable model, then isomorphism by thm:p-isom1 -- 5-sentence sketch)

---

### mod/lin/prf -- Lindstrom's Theorem
- **Action**: ABSORB:mod/lin/alg,mod/lin/lsp
- **Lean Chapter**: CH-META
- **Lean Section**: META.11: Lindstrom's Theorem
- **Rationale**: CORE-THM. Defining occurrence of CP-013 (Lindstrom's Theorem). Full proof using compactness to obtain a non-standard element in an ordering encoding I_n relations, then deriving a partial isomorphism contradicting the separation hypothesis. Absorbs the abstract logic framework (mod/lin/alg) and the abstract LS/compactness property definitions (mod/lin/lsp) to create a single self-contained section.
- **Content Directives**:
  - Formal items to preserve: lem[lem:lindstrom] (n-equivalence invariance implies FO equivalence), thm[thm:lindstrom] (CP-013 -- Lindstrom's Theorem)
  - Absorbed from mod/lin/alg: defn (abstract logic), defn (Mod(L), elem equiv in L), defn (normal abstract logic), defn (expressiveness comparison)
  - Absorbed from mod/lin/lsp: defn (Compactness Property), defn (LS Property), thm[thm:abstract-p-isom]
  - Formal items to drop: none
  - Prose: preserve for thm[thm:lindstrom]; compress absorbed definitions to minimal introductory text
  - Examples: cut all
  - Proofs: preserve full for lem[lem:lindstrom] (uses prop:qr-finite; compact argument); preserve full for thm[thm:lindstrom] (the defining proof of CP-013; uses compactness for non-standard element, I_n relations, and partial isomorphism contradiction)

---

### MOD Batch Summary
- **Total sections**: 22
- **Action distribution**: 7 KEEP, 7 CONDENSE, 2 MERGE-INTO, 1 ABSORB, 5 CUT
- **Verification**: 7 + 7 + 2 + 1 + 5 = 22 (confirmed)
- **Taxonomy coverage**: All MOD-related taxonomy items have authoritative homes:
  - DEF-SEM011 (Substructure): mod/bas/sub (KEEP)
  - DEF-SEM013 / PRIM-SEM012 (Isomorphism): mod/bas/iso (KEEP)
  - PRIM-SEM013 / DEF-SEM008 (Elementary Equivalence): mod/bas/iso (KEEP)
  - PRIM-SEM012 / DEF-SEM006 (Theory of a Structure, Th(M)): mod/bas/thm (KEEP)
  - DEF-SEM006 / DEF-SEM014 (Categoricity -- by example): mod/bas/dlo (KEEP)
  - THM-SEM001 (Isomorphism Lemma): mod/bas/iso (KEEP)
  - CP-011 (Craig's Interpolation): mod/int/prf (KEEP)
  - CP-012 (Beth's Definability): mod/int/def (KEEP)
  - CP-013 (Lindstrom's Theorem): mod/lin/prf (ABSORB)
- **Compression targets resolved**:
  - CP-013 (Lindstrom, 2 support sections): mod/lin/alg MERGE-INTO mod/lin/prf; mod/lin/lsp MERGE-INTO mod/lin/prf; primary = mod/lin/prf (ABSORB)
  - mod/bas/nsa (commented out): CUT -- content fully subsumed by mod/mar/{stm,nst,mpa}
- **Lean chapter distribution**:
  - CH-SEM: 10 sections (mod/bas/red, mod/bas/sub, mod/bas/ove, mod/bas/iso, mod/bas/thm, mod/bas/dlo, mod/mar/stm, mod/mar/nst, mod/mar/mpa, mod/mar/cmp)
  - CH-META: 5 sections (mod/bas/pis, mod/int/sep, mod/int/prf, mod/int/def, mod/lin/prf [absorbing mod/lin/alg + mod/lin/lsp])
  - CUT (no lean chapter): 5 sections (mod/bas/nsa, mod/mar/int, mod/mar/mdq, mod/int/int, mod/lin/int)
  - MERGE-INTO (absorbed into mod/lin/prf): 2 sections (mod/lin/alg, mod/lin/lsp)
- **Surviving sections**: 15 (KEEP(7) + CONDENSE(7) + ABSORB(1) = 15 surviving sections. The 2 MERGE-INTO sources are absorbed into the ABSORB target (mod/lin/prf), and 5 CUT sections are removed. Total surviving: 15.)

### ABSENT Items in MOD scope
The following taxonomy items from the model theory supplement are ABSENT from OL's model-theory/ content:
- **PRIM-SEM014** (Elementary Substructure): Not defined in OL. Gap persists.
- **DEF-SEM003** (Semantic Consistency): Defined elsewhere (fol/sem or fol/com).
- **DEF-SEM008** (Decidable Theory): Not formally defined in OL model-theory.
- **DEF-SEM012** (Embedding): Not defined in OL (only isomorphism).
- **DEF-SEM014** (Diagram): Not discussed in OL.
- **DEF-SEM015** (Type): Not discussed in OL.
- **DEF-SEM016** (Omitting Types): Not discussed in OL.

These gaps were identified in Phase 2 SECTION-MAP and will be resolved in Phase 4 via NEW-CONTENT entries written from DOMAIN-SEMANTICS.md definitions, placed in SEM.6: Model-Theoretic Concepts.

### Discrepancies
1. **Taxonomy ID numbering mismatch**: The SECTION-MAP uses different IDs than DOMAIN-SEMANTICS.md for some concepts. Specifically:
   - SECTION-MAP calls the substructure definition "DEF-SEM011" while DOMAIN-SEMANTICS.md has "PRIM-SEM013" for Substructure.
   - SECTION-MAP maps mod/bas/iso's defn[defn:elem-equiv] to "PRIM-SEM013" (Elementary Equivalence) while DOMAIN-SEMANTICS.md uses "DEF-SEM008" for Elementary Equivalence.
   - SECTION-MAP maps mod/bas/thm to "PRIM-SEM012" (Theory of a Structure) while DOMAIN-SEMANTICS.md uses "DEF-SEM006" for Theory of a Structure.
   - SECTION-MAP maps mod/bas/iso's defn[defn:isomorphism] to "DEF-SEM013" (Isomorphism) while DOMAIN-SEMANTICS.md uses "PRIM-SEM012" for Isomorphism.

   **Resolution**: These are Phase 1 vs Phase 2 naming inconsistencies. The concepts themselves are correctly mapped to their authoritative sections. Step 11 (QC) should harmonize the IDs. For this block, both IDs are noted at each entry to ensure traceability.

2. **DEF-SEM006 (Categoricity)**: The SECTION-MAP notes that mod/bas/dlo demonstrates aleph-0 categoricity by example (Cantor's theorem) but never formally defines the concept of kappa-categoricity. DOMAIN-SEMANTICS.md has DEF-SEM014 for Categoricity. Phase 4 should add an explicit formal definition of kappa-categoricity (from DEF-SEM014) before the DLO theorem in the lean text.
