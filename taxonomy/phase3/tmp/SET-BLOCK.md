## CH-SET: Formal Set Theory (Level-1)

---

## Chapter 1: story/ -- The Iterative Conception

### sth/story/extensionality -- Extensionality
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms
- **Rationale**: CORE-DEF. Authoritative introduction of AX-SET001 (Extensionality), the first ZFC axiom. The formal statement is clean and standalone.
- **Content Directives**:
  - Formal items to preserve: axiom[Extensionality] (AX-SET001)
  - Formal items to drop: none
  - Prose: preserve (brief, directly supports axiom statement)
  - Examples: preserve (implicit in the axiom statement)
  - Proofs: N/A (no proofs in this section)

---

### sth/story/rus -- Russell's Paradox (again)
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Re-derives Russell's Paradox already covered in sfr/. No taxonomy items introduced; Naive Comprehension and Russell's Paradox are OL-ONLY.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: defish[Naive Comprehension] (OL-ONLY, rejected principle), thm[Russell's Paradox] (OL-ONLY, redundant with sfr/)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/story/predicative -- Predicative and Impredicative
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Philosophical discussion of predicativity vs. impredicativity. No formal definitions or taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: defish[Predicative Comprehension] (OL-ONLY, informal)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/story/approach -- The Cumulative-Iterative Approach
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Informal motivational narrative about the cumulative-iterative conception. No formal items or taxonomy content. The lean text's SET.1 and SET.2 opening prose can incorporate a compressed version of this motivation (1-2 sentences).
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/story/urelements -- Urelements or Not?
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Design-decision discussion about excluding urelements. No formal content, no taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/story/blv -- Appendix: Frege's Basic Law V
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: TANGENTIAL. Historical appendix on Frege's system. OL-ONLY items (lem[Fregeextensions], etc.) are purely historical and outside taxonomy scope.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: lem[Fregeextensions] (OL-ONLY, historical), lem (Naive Comprehension from BLV) (OL-ONLY, historical)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

## Chapter 2: z/ -- Steps towards Z

### sth/z/story -- The Story in More Detail
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms (introductory subsection)
- **Rationale**: STEPPING-STONE. The informal principles StagesHier, StagesOrd, StagesAcc provide philosophical context for the axioms. Compress to 1-paragraph summary that precedes the axiom statements in SET.2.
- **Content Directives**:
  - Formal items to preserve: none (no formal items -- informal principles only)
  - Formal items to drop: none
  - Prose: compress to 1 paragraph stating the three informal principles and their role in justifying ZFC
  - Examples: cut all
  - Proofs: N/A

---

### sth/z/sep -- Separation
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms
- **Rationale**: CORE-DEF. Authoritative introduction of AX-SET006 (Separation) and derives AX-SET002 (Empty Set existence) as consequence. The no-universal-set theorem is a key early result.
- **Content Directives**:
  - Formal items to preserve: axiom[Scheme of Separation] (AX-SET006), prop[emptyexists] (AX-SET002 derivation)
  - Formal items to drop: thm[NoUniversalSet] (OL-ONLY, but preserve as a 1-line corollary remark), prop (A\B exists) (OL-ONLY, technical), prop[intersectionsexist] (OL-ONLY, technical)
  - Prose: preserve (directly supports axiom definitions)
  - Examples: preserve
  - Proofs: preserve full for prop[emptyexists]; cut proofs for OL-ONLY technical props

---

### sth/z/union -- Union
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms
- **Rationale**: CORE-DEF. Authoritative introduction of AX-SET004 (Union).
- **Content Directives**:
  - Formal items to preserve: axiom[Union] (AX-SET004)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: preserve
  - Proofs: N/A (no proofs)

---

### sth/z/pairs -- Pairs
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms
- **Rationale**: CORE-DEF. Authoritative introduction of AX-SET003 (Pairing). Also derives singletons, binary union, and ordered pairs as consequences.
- **Content Directives**:
  - Formal items to preserve: axiom[Pairs] (AX-SET003)
  - Formal items to drop: prop[pairsconsequences] (OL-ONLY, but preserve statement as a remark -- these are standard consequences)
  - Prose: preserve
  - Examples: preserve
  - Proofs: preserve sketch only for pairsconsequences

---

### sth/z/power -- Powersets
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms
- **Rationale**: CORE-DEF. Authoritative introduction of AX-SET005 (Power Set).
- **Content Directives**:
  - Formal items to preserve: axiom[Powersets] (AX-SET005)
  - Formal items to drop: prop[thm:Products] (OL-ONLY, Cartesian product existence -- preserve as 1-line remark)
  - Prose: preserve
  - Examples: preserve
  - Proofs: cut proof for Products (standard consequence)

---

### sth/z/infinity-again -- Infinity
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms
- **Rationale**: CORE-DEF. Authoritative introduction of AX-SET008 (Infinity). Also defines omega informally.
- **Content Directives**:
  - Formal items to preserve: axiom[Infinity] (AX-SET008), defn[defnomega] (OL-ONLY but critical -- defines omega, keep as remark)
  - Formal items to drop: prop[naturalnumbersarentinfinite] (OL-ONLY, technical consequence)
  - Prose: preserve
  - Examples: preserve
  - Proofs: cut proof for naturalnumbersarentinfinite (technical)

---

### sth/z/milestone -- Z^-: a Milestone
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms (closing remark)
- **Rationale**: STEPPING-STONE. Collects axioms of Z^- into named theory. Useful as a 2-sentence summary remark at end of axiom block, not a standalone section.
- **Content Directives**:
  - Formal items to preserve: defn (Z^-) as inline remark (OL-ONLY)
  - Formal items to drop: none
  - Prose: compress to 2-sentence remark defining Z^- = {Extensionality, Pairing, Union, Power Set, Separation, Infinity}
  - Examples: cut all
  - Proofs: N/A

---

### sth/z/nat -- Selecting our Natural Numbers
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Philosophical discussion of Benacerraf's problem. No formal content, no taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/z/arbintersections -- Appendix: Closure, Comprehension, and Intersection
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms (appendix note)
- **Rationale**: STEPPING-STONE. Technical appendix showing intersections via Separation. Useful as a brief remark establishing that Z^- supports closure definitions from BST, but does not need standalone treatment.
- **Content Directives**:
  - Formal items to preserve: none in taxonomy (all OL-ONLY)
  - Formal items to drop: all (technical details)
  - Prose: compress to 1-paragraph remark on intersection existence via Separation
  - Examples: cut all
  - Proofs: cut (technical)

---

## Chapter 3: ordinals/ -- Ordinals

### sth/ordinals/intro -- Introduction
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Brief motivational introduction with no formal content. The lean text's SET.3 opening can incorporate any necessary motivation in 1-2 sentences.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/ordinals/idea -- The General Idea of an Ordinal
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Informal examples of ordinal orderings on natural numbers. No formal definitions or taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/ordinals/wo -- Well-Orderings
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.3: Ordinals
- **Rationale**: CORE-DEF. Defines well-ordering (DEF-SET009 in taxonomy, though SECTION-MAP maps propwoinduction to DEF-SET006 kernel). Establishes the strong induction principle on well-orderings, which is the foundation for transfinite induction. Also provides the authoritative home for DEF-SET009 (Well-Ordering).
- **Content Directives**:
  - Formal items to preserve: defn (well-ordering) (DEF-SET009), prop[wo:strictorder], prop[propwoinduction] (kernel of DEF-SET006/DEF-SET005)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: preserve
  - Proofs: preserve full

---

### sth/ordinals/iso -- Order-Isomorphisms
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.3: Ordinals
- **Rationale**: STEPPING-STONE. Extensive technical development of order-isomorphism theory. Key result thm[woalwayscomparable] is needed by sth/ordinals/vn and the ordinal representation theorem. Compress verification proofs to sketches.
- **Content Directives**:
  - Formal items to preserve: defn (order-isomorphism), defn (initial segment A_a), thm[thm:woalwayscomparable] (key theorem), lem[wellordnotinitial] (needed by basic), lem[wellordinitialsegment] (needed by ordtype), lem[lemordsegments] (needed by ordtype)
  - Formal items to drop: lem[isoscompose] (trivial), cor[ordisoisequiv] (trivial consequence), prop[ordisounique] (OL-ONLY, preserve statement only)
  - Prose: compress to intro + definitions only
  - Examples: cut all
  - Proofs: preserve sketch only for thm[woalwayscomparable]; cut detailed verification proofs for other lemmas (preserve statements)

---

### sth/ordinals/vn -- Von Neumann's Construction of the Ordinals
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.3: Ordinals
- **Rationale**: CORE-DEF. Authoritative introduction of DEF-SET001 (Ordinal), DEF-SET002 (Transitive Set), DEF-SET003 (Von Neumann Ordinal). These are the central definitions of ordinal theory.
- **Content Directives**:
  - Formal items to preserve: defn (transitive set) (DEF-SET002), defn (ordinal = transitive + well-ordered by membership) (DEF-SET001/DEF-SET003)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: preserve (first few ordinals as natural numbers)
  - Proofs: N/A

---

### sth/ordinals/basic -- Basic Properties of the Ordinals
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.3: Ordinals
- **Rationale**: CORE-THM. Central section establishing DEF-SET006 (Transfinite Induction), Trichotomy, and PRIM-SET003 (Proper Class via Burali-Forti Paradox). Multiple taxonomy items have their authoritative home here.
- **Content Directives**:
  - Formal items to preserve: thm[ordinductionschema] (DEF-SET006, Transfinite Induction), thm[ordtrichotomy] (Trichotomy), thm[buraliforti] (PRIM-SET003, Burali-Forti Paradox), cor[corordtransitiveord], lem[ordmemberord]
  - Formal items to drop: cor[ordissetofsmallerord] (OL-ONLY, immediate), prop (no infinite descending chain) (OL-ONLY, standard), prop[ordinalsaresubsets] (OL-ONLY, preserve statement), prop[ordisoidentity] (OL-ONLY, preserve statement)
  - Prose: preserve
  - Examples: preserve
  - Proofs: preserve full for ordinductionschema, ordtrichotomy, buraliforti; preserve sketch only for others

---

### sth/ordinals/replacement -- Replacement
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms
- **Rationale**: CORE-DEF. Authoritative introduction of AX-SET007 (Replacement). Although placed in the ordinals chapter in OL, the axiom statement itself belongs in SET.2 in the lean text.
- **Content Directives**:
  - Formal items to preserve: axiom[Scheme of Replacement] (AX-SET007)
  - Formal items to drop: cor (image of set under term exists) (OL-ONLY, standard consequence)
  - Prose: preserve (axiom motivation is relevant)
  - Examples: preserve
  - Proofs: N/A for axiom statement

---

### sth/ordinals/zfm -- ZF^-: a milestone
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms (closing remark)
- **Rationale**: STEPPING-STONE. Milestone collecting axioms of ZF^- = Z^- + Replacement. Useful as a 1-sentence inline remark, not standalone.
- **Content Directives**:
  - Formal items to preserve: defn (ZF^-) as inline remark (OL-ONLY)
  - Formal items to drop: none
  - Prose: compress to 1-sentence remark
  - Examples: cut all
  - Proofs: N/A

---

### sth/ordinals/ordtype -- Ordinals as Order-Types
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.3: Ordinals
- **Rationale**: CORE-THM. Proves the Ordinal Representation Theorem (thm[thmOrdinalRepresentation]): every well-ordering is isomorphic to a unique ordinal. Major theorem requiring Replacement. Defines order type.
- **Content Directives**:
  - Formal items to preserve: thm[thmOrdinalRepresentation], defn (order type ordtype(A,<)), cor[ordtypesworklikeyouwant]
  - Formal items to drop: none
  - Prose: preserve
  - Examples: preserve
  - Proofs: preserve full

---

### sth/ordinals/opps -- Successor and Limit Ordinals
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.3: Ordinals
- **Rationale**: CORE-DEF. Authoritative introduction of DEF-SET004 (Successor Ordinal) and DEF-SET005 (Limit Ordinal). Also provides Simple Transfinite Induction, needed throughout the development.
- **Content Directives**:
  - Formal items to preserve: defn (successor ordinal, limit ordinal) (DEF-SET004, DEF-SET005), thm[simpletransrecursion] (Simple Transfinite Induction), defn[defsupstrict] (lsub/supstrict)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: preserve
  - Proofs: preserve full

---

## Chapter 4: spine/ -- Stages and Ranks

### sth/spine/valpha -- Defining the Stages as the V_alpha's
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics (Von Neumann Hierarchy)
- **Rationale**: CORE-DEF. Authoritative introduction of DEF-SET012 (Von Neumann Hierarchy). Defines V_alpha by transfinite recursion, formalizing the cumulative hierarchy.
- **Content Directives**:
  - Formal items to preserve: defn[defValphas] (DEF-SET012, V_alpha definition)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: preserve
  - Proofs: N/A (definition, not theorem)

---

### sth/spine/recursion -- The Transfinite Recursion Theorem(s)
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.3: Ordinals (or SET.6: Theorems)
- **Rationale**: CORE-THM. Proves DEF-SET007 / THM-SET002 (Transfinite Recursion Theorem). Key technical section using Transfinite Induction + Replacement. Vindicates V_alpha definition.
- **Content Directives**:
  - Formal items to preserve: defn (alpha-approximation), lem[transrecursionfun] (Bounded Recursion), thm[transrecursionschema] (General Recursion, DEF-SET007/THM-SET002), thm[simplerecursionschema] (Simple Recursion)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: preserve (vindication of V_alpha at end)
  - Proofs: preserve full for all three results (they form a tight chain)

---

### sth/spine/Valphabasic -- Basic Properties of Stages
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics
- **Rationale**: STEPPING-STONE. Technical properties of V_alpha hierarchy. Preserve key statements, compress verification proofs.
- **Content Directives**:
  - Formal items to preserve: lem[Valphabasicprops] (V_alpha transitive, potent, cumulative -- statement only), lem[Valphanotref] (V_alpha not in V_alpha -- statement only)
  - Formal items to drop: defn (potent set) (OL-ONLY, auxiliary), cor (alpha in beta iff V_alpha in V_beta) (OL-ONLY)
  - Prose: compress to intro + key lemma statements
  - Examples: cut all
  - Proofs: preserve sketch only

---

### sth/spine/foundation -- Foundation
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms
- **Rationale**: STEPPING-STONE. Introduces Foundation axiom (AX-SET008 in the DOMAIN-SET-FORMAL numbering, where AX-SET008 = Foundation/Regularity). The SECTION-MAP lists this as OL-ONLY for Foundation, but the taxonomy's AX-SET008 is "Foundation (Regularity)." This section provides the authoritative Foundation axiom statement. Compress the lengthy proof of Foundation => Regularity.
- **Content Directives**:
  - Formal items to preserve: axiom[Foundation] (maps to AX-SET008 per domain spec), defish[Regularity] (informal equivalent), defn (transitive closure trcl(A))
  - Formal items to drop: prop[subsetoftrcl] (OL-ONLY, technical), lem[lem:TransitiveWellFounded] (OL-ONLY, technical stepping stone), thm[zfentailsregularity] (OL-ONLY, preserve statement with proof sketch)
  - Prose: compress to intro + axiom statement + brief remark on Foundation-Regularity equivalence
  - Examples: cut all
  - Proofs: preserve sketch only for zfentailsregularity; cut detailed proofs

---

### sth/spine/zf -- Z and ZF: A Milestone
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms (closing remark)
- **Rationale**: STEPPING-STONE. Milestone defining Z = Z^- + Foundation, ZF = ZF^- + Foundation = Z + Replacement. Compress to 2-sentence remark.
- **Content Directives**:
  - Formal items to preserve: defn (Z), defn (ZF) as inline remarks (OL-ONLY)
  - Formal items to drop: none
  - Prose: compress to 2-sentence remark defining Z and ZF
  - Examples: cut all
  - Proofs: N/A

---

### sth/spine/rank -- Rank
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics
- **Rationale**: STEPPING-STONE. Defines rank and proves epsilon-induction. Compress proofs; preserve key definitions and statements.
- **Content Directives**:
  - Formal items to preserve: defn[defnsetrank] (rank of a set), thm (epsilon-Induction Scheme -- statement), cor[ordsetrankalpha] (rank(alpha) = alpha for ordinals -- statement)
  - Formal items to drop: prop[ranksexist] (OL-ONLY, technical), prop[valphalowerrank] (OL-ONLY, technical), prop[rankmemberslower] (OL-ONLY, technical), prop[ranksupstrict] (OL-ONLY, technical), prop[zfminusregularityfoundation] (OL-ONLY, preserve statement as remark)
  - Prose: compress to intro + definition + key results
  - Examples: cut all
  - Proofs: preserve sketch only for epsilon-Induction; cut other proofs

---

## Chapter 5: replacement/ -- Replacement

### sth/replacement/intro -- Introduction
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Brief introduction framing the question of justifying Replacement. No formal content.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/replacement/strength -- The Strength of Replacement
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics
- **Rationale**: STEPPING-STONE. Shows Z cannot prove existence of omega+omega. Introduces formula relativization. Useful result but compress the model-theoretic argument.
- **Content Directives**:
  - Formal items to preserve: defn[formularelativization] (relativization of formulas to a set M -- OL-ONLY but useful for SET.5)
  - Formal items to drop: none beyond compression
  - Prose: compress to intro + relativization definition + 1-paragraph summary of V_{omega+omega} model argument
  - Examples: cut all
  - Proofs: preserve sketch only

---

### sth/replacement/extrinsic -- Extrinsic Considerations about Replacement
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Philosophical discussion of extrinsic justification (Boolos). No formal content, no taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/replacement/limofsize -- Limitation-of-size
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Philosophical discussion of limitation-of-size as justification for Replacement. No formal items, no taxonomy content.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: (informal principle: LimOfSize) (OL-ONLY)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/replacement/absinf -- Replacement and "Absolute Infinity"
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Philosophical discussion of Shoenfield's cofinality-based justification. Informal principles StagesInex, StagesCofin are OL-ONLY. No formal content.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: (informal principles: StagesInex, StagesCofin) (OL-ONLY)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/replacement/ref -- Replacement and Reflection
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics
- **Rationale**: STEPPING-STONE. States the Reflection Schema (equivalent to Replacement over Z). Preserve the statement as a key metatheoretic result; compress philosophical discussion.
- **Content Directives**:
  - Formal items to preserve: thm[reflectionschema] (Reflection Schema -- OL-ONLY, statement only)
  - Formal items to drop: none
  - Prose: compress to intro + theorem statement + 1-sentence remark on Montague-Levy equivalence
  - Examples: cut all
  - Proofs: cut (proof is in refproofs appendix)

---

### sth/replacement/refproofs -- Appendix: Results surrounding Replacement
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics
- **Rationale**: STEPPING-STONE. Most advanced mathematics in the textbook: proves Reflection in ZF and Replacement from Weak-Reflection. Preserve key theorem statements; compress lengthy proofs to sketches.
- **Content Directives**:
  - Formal items to preserve: thm[thm:replacement] (Weak-Reflection implies Replacement over Z -- OL-ONLY, statement)
  - Formal items to drop: lem[lemreflection] (OL-ONLY, technical), defish[Weak-Reflection] (OL-ONLY, preserve as remark), lem[lem:reflect] (OL-ONLY, technical)
  - Prose: compress to intro + key theorem statement
  - Examples: cut all
  - Proofs: preserve sketch only for Reflection proof; cut detailed verification

---

### sth/replacement/finiteaxiomatizability -- Appendix: Finite axiomatizability
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics
- **Rationale**: STEPPING-STONE. Proves ZF is not finitely axiomatizable (Montague). Notable metatheoretic result. Preserve statement; compress proof.
- **Content Directives**:
  - Formal items to preserve: thm[zfnotfinitely] (ZF is not finitely axiomatizable -- OL-ONLY, statement)
  - Formal items to drop: prop[finiteextensionofZ] (OL-ONLY, consequence)
  - Prose: compress to statement + 1-paragraph proof sketch
  - Examples: cut all
  - Proofs: preserve sketch only

---

## Chapter 6: ord-arithmetic/ -- Ordinal Arithmetic

### sth/ord-arithmetic/intro -- Introduction
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Brief motivational introduction. No formal content.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/ord-arithmetic/add -- Ordinal Addition
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics (Ordinal Arithmetic)
- **Rationale**: STEPPING-STONE. Defines ordinal addition. OL-ONLY items but needed for the ordinal arithmetic development that supports cardinal theory. Preserve definition and recursion equations; compress verification proofs.
- **Content Directives**:
  - Formal items to preserve: defn[defordplus] (ordinal addition -- OL-ONLY), lem[ordadditionrecursion] (recursion equations -- statement), prop[ordsumnotcommute] (non-commutativity -- statement)
  - Formal items to drop: defn[defdissum] (disjoint sum -- OL-ONLY, auxiliary), defn (reverse lexicographic ordering -- OL-ONLY, auxiliary), lem[ordsumlessiswo] (OL-ONLY, technical), lem[ordinaladditionisnice] (OL-ONLY, compress to statement)
  - Prose: compress to intro + definition + recursion equations + non-commutativity remark
  - Examples: keep 1 (1+omega = omega vs omega+1)
  - Proofs: cut all (preserve statements only)

---

### sth/ord-arithmetic/using-addition -- Using Ordinal Addition
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics
- **Rationale**: STEPPING-STONE. Rank computations and characterizations of infinite ordinals. The 5 equivalent characterizations of infinite ordinals (lem[ordinfinitycharacter]) are referenced by cardinal development.
- **Content Directives**:
  - Formal items to preserve: lem[ordinfinitycharacter] (5 equivalent characterizations of infinite ordinals -- statement)
  - Formal items to drop: lem[rankcomputation] (OL-ONLY, technical rank computations)
  - Prose: compress to statement of ordinfinitycharacter + brief context
  - Examples: cut all
  - Proofs: preserve sketch only for ordinfinitycharacter

---

### sth/ord-arithmetic/mult -- Ordinal Multiplication
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics (Ordinal Arithmetic)
- **Rationale**: STEPPING-STONE. Defines ordinal multiplication. Compress to definition + recursion equations + non-commutativity.
- **Content Directives**:
  - Formal items to preserve: defn (ordinal multiplication -- OL-ONLY), lem[ordtimesrecursion] (recursion equations -- statement), prop (non-commutativity -- statement)
  - Formal items to drop: lem[ordtimeslessiswo] (OL-ONLY, technical), lem[ordinalmultiplicationisnice] (OL-ONLY, compress to statement)
  - Prose: compress to intro + definition + recursion equations + non-commutativity remark
  - Examples: keep 1 (2*omega = omega vs omega*2)
  - Proofs: cut all

---

### sth/ord-arithmetic/expo -- Ordinal Exponentiation
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics (Ordinal Arithmetic)
- **Rationale**: STEPPING-STONE. Defines ordinal exponentiation by transfinite recursion. Compress to definition only.
- **Content Directives**:
  - Formal items to preserve: defn[ordexporecursion] (ordinal exponentiation -- OL-ONLY)
  - Formal items to drop: none
  - Prose: compress to definition + 1-sentence remark on non-commutativity (2^omega = omega vs omega^2)
  - Examples: keep 1 (2^omega = omega)
  - Proofs: N/A

---

## Chapter 7: cardinals/ -- Cardinals

### sth/cardinals/cp -- Cantor's Principle
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.4: Cardinals
- **Rationale**: STEPPING-STONE. Motivates cardinal notion via Cantor's Principle. The SECTION-MAP lists this as introducing DEF-SET008 (motivation), but the formal definition is in cardsasords. Compress to the statement of Cantor's Principle as a desideratum for the cardinal definition.
- **Content Directives**:
  - Formal items to preserve: (Cantor's Principle stated informally -- preserve as motivating remark)
  - Formal items to drop: none
  - Prose: compress to 1 paragraph stating Cantor's Principle: |A| = |B| iff A equinumerous B
  - Examples: cut all
  - Proofs: N/A

---

### sth/cardinals/cardsasords -- Cardinals as Ordinals
- **Action**: ABSORB:{sth/cardinals/cp motivation}
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.4: Cardinals
- **Rationale**: CORE-DEF. Authoritative introduction of DEF-SET008 (Cardinal Number as least ordinal equinumerous to A). Also introduces AX-SET009 (Well-Ordering axiom). This is the primary section for both DEF-SET008 and AX-SET009 (first occurrence). The Well-Ordering axiom is later shown equivalent to Choice in sth/choice/woproblem. Absorbs motivation from cp.
- **Content Directives**:
  - Formal items to preserve: defn[defcardinalasordinal] (DEF-SET008), axiom[Well-Ordering] (AX-SET009), lem[lem:CardinalsExist], lem[lem:CardinalsBehaveRight] (Cantor's Principle verified)
  - Formal items to drop: proof (re-proof of Schroder-Bernstein) (OL-ONLY, redundant with sfr/)
  - Prose: preserve (directly supports cardinal definition)
  - Examples: preserve
  - Proofs: preserve full for CardinalsExist and CardinalsBehaveRight; cut Schroder-Bernstein re-proof

---

### sth/cardinals/zfc -- ZFC: A Milestone
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms (final remark)
- **Rationale**: STEPPING-STONE. Final milestone: ZFC = ZF + Well-Ordering = ZF + Choice. Compress to 2-sentence remark at end of SET.2.
- **Content Directives**:
  - Formal items to preserve: defn (ZFC = ZF + Well-Ordering) as inline remark (OL-ONLY)
  - Formal items to drop: none
  - Prose: compress to 2-sentence remark defining ZFC and noting equivalence of Well-Ordering and Choice
  - Examples: cut all
  - Proofs: N/A

---

### sth/cardinals/classing -- Finite, Enumerable, Nonenumerable
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.4: Cardinals
- **Rationale**: STEPPING-STONE. Classifies cardinals as finite/infinite. Key results: omega is least infinite cardinal, no largest cardinal (via THM-SET002/Cantor's Theorem reference). Preserve key definitions and results; compress proofs.
- **Content Directives**:
  - Formal items to preserve: defn[defnfinite] (finite/infinite sets), cor[omegaisacardinal] (omega is least infinite cardinal), thm[lem:NoLargestCardinal] (no largest cardinal -- THM-SET002 reference), prop[unioncardinalscardinal] (union of cardinals is cardinal)
  - Formal items to drop: prop[finitecardisoequal] (OL-ONLY), cor[naturalsarecardinals] (OL-ONLY, immediate), thm[generalinfinitycharacter] (OL-ONLY, preserve statement), cor (infinite cardinal = limit ordinal) (OL-ONLY), thm (no set of all cardinals) (OL-ONLY, preserve as 1-line remark)
  - Prose: compress to definitions + key theorems
  - Examples: cut all
  - Proofs: preserve sketch only for NoLargestCardinal; cut others

---

### sth/cardinals/hp -- Appendix: Hume's Principle
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: TANGENTIAL. Philosophical appendix on Hume's Principle and neo-Fregean logicism. No formal set-theoretic content, no taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: (Hume's Principle -- discussed informally) (OL-ONLY)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

## Chapter 8: card-arithmetic/ -- Cardinal Arithmetic

### sth/card-arithmetic/opps -- Defining the Basic Operations
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.4: Cardinals (Cardinal Arithmetic)
- **Rationale**: CORE-DEF. Defines cardinal addition, multiplication, exponentiation (OL-ONLY but essential operations). Also proves |P(A)| = 2^|A| and the cardinal Cantor's Theorem (THM-SET002 reference: a < 2^a), and |R| = 2^omega. Key section for cardinal arithmetic.
- **Content Directives**:
  - Formal items to preserve: defn (cardinal addition, multiplication, exponentiation), prop[cardplustimescommute], lem[lem:SizePowerset2Exp] (|P(A)| = 2^|A|), cor[cantorcor] (a < 2^a, THM-SET002 cardinal form), thm[continuumis2aleph0] (|R| = 2^omega)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: preserve
  - Proofs: preserve full

---

### sth/card-arithmetic/simp -- Simplifying Addition and Multiplication
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.4: Cardinals (Cardinal Arithmetic)
- **Rationale**: STEPPING-STONE. Major simplification: for infinite cardinals, addition and multiplication collapse to max. Key lemma alpha*alpha = alpha for infinite alpha. Preserve key results; compress the canonical ordering proof.
- **Content Directives**:
  - Formal items to preserve: lem[alphatimesalpha] (alpha equinumerous alpha x alpha for infinite alpha -- statement + sketch), thm[cardplustimesmax] (a * b = a + b = max(a,b) for infinite cardinals), prop[kappaunionkappasize] (kappa-union of kappa-size sets has size kappa)
  - Formal items to drop: defn (canonical ordering on pairs of ordinals) (OL-ONLY, auxiliary), prop[simplecardproduct] (OL-ONLY, intermediate)
  - Prose: compress to intro + key theorem statements + sketch of alpha*alpha = alpha
  - Examples: cut all
  - Proofs: preserve sketch only for alphatimesalpha; preserve statement + sketch for cardplustimesmax

---

### sth/card-arithmetic/expotough -- Some Simplification with Cardinal Exponentiation
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.4: Cardinals (Cardinal Arithmetic)
- **Rationale**: STEPPING-STONE. Partial simplification of cardinal exponentiation. Cannot fully simplify due to CH-related issues. Preserve key results as statements.
- **Content Directives**:
  - Formal items to preserve: prop[simplecardexpo] (exponent laws -- statement), prop[cardexpo2reduct] (a^b = 2^b when 2 <= a <= b, b infinite -- statement)
  - Formal items to drop: prop (a^n = a for infinite a, finite n) (OL-ONLY, compress to remark), prop (a^b = 2^b when...) (OL-ONLY, redundant with cardexpo2reduct)
  - Prose: compress to key results + remark on CH-related limitations
  - Examples: cut all
  - Proofs: cut (preserve statements only)

---

### sth/card-arithmetic/ch -- The Continuum Hypothesis
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics
- **Rationale**: CORE-DEF. Authoritative introduction of DEF-SET013 (Aleph Numbers) and DEF-SET015 (Continuum Hypothesis). Defines aleph_alpha and beth_alpha sequences, states CH and GCH, notes independence.
- **Content Directives**:
  - Formal items to preserve: defn (aleph numbers, beth numbers) (DEF-SET013), defish[GCH] (DEF-SET015), defish[CH] (DEF-SET015), prop (every infinite cardinal is an aleph)
  - Formal items to drop: none
  - Prose: preserve (includes essential independence result statements)
  - Examples: preserve
  - Proofs: preserve full for prop (every infinite cardinal is an aleph)

---

### sth/card-arithmetic/fix -- Aleph-Fixed Points
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics
- **Rationale**: STEPPING-STONE. Illustrates the "height" forced by Replacement via aleph-fixed-points and beth-fixed-points. Preserve key statements; compress proofs and philosophical discussion.
- **Content Directives**:
  - Formal items to preserve: prop[alephfixed] (existence of aleph-fixed-point -- statement), prop[stagesize] (|V_{omega+alpha}| = beth_alpha -- statement)
  - Formal items to drop: prop[bethfixed] (OL-ONLY, similar to alephfixed, mention in remark), cor (exists kappa with |V_kappa| = kappa) (OL-ONLY, consequence)
  - Prose: compress to key statements + 1-paragraph context
  - Examples: cut all
  - Proofs: cut (preserve statements only)

---

## Chapter 9: choice/ -- Choice

### sth/choice/intro -- Introduction
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Brief introduction to Choice chapter. No formal content.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/choice/tarskiscott -- The Tarski-Scott Trick
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.4: Cardinals (alternative definition remark)
- **Rationale**: STEPPING-STONE. Shows how to define cardinals without Choice using least-rank representatives. Interesting alternative definition but secondary to the standard (Well-Ordering-based) approach. Compress to brief remark.
- **Content Directives**:
  - Formal items to preserve: defn[Tarski-Scott] (Tarski-Scott trick -- OL-ONLY, statement only)
  - Formal items to drop: defn (TS-cardinality, TS-ordinality) (OL-ONLY, alternative definitions)
  - Prose: compress to 1-paragraph remark on the Tarski-Scott alternative
  - Examples: cut all
  - Proofs: N/A

---

### sth/choice/hartogs -- Comparability and Hartogs' Lemma
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.6: Theorems (or SET.4: Cardinals supplement)
- **Rationale**: STEPPING-STONE. Proves Hartogs' Lemma (key ingredient for Well-Ordering => Choice proof) and the equivalence of Well-Ordering with Comparability. Preserve key results; compress proofs.
- **Content Directives**:
  - Formal items to preserve: lem[HartogsLemma] (for any set A there is an ordinal not injectable into A), thm (Well-Ordering iff Comparability -- statement)
  - Formal items to drop: none
  - Prose: compress to key theorem statements + brief context
  - Examples: cut all
  - Proofs: preserve sketch only for HartogsLemma; cut proof for equivalence theorem

---

### sth/choice/woproblem -- The Well-Ordering Problem
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.6: Theorems
- **Rationale**: CORE-THM. Authoritative proof of THM-SET001 (Well-Ordering and Choice are equivalent). Also defines choice function and Axiom of Choice (AX-SET009 equivalent formulation). Primary section for AX-SET009's Choice formulation and THM-SET001.
- **Content Directives**:
  - Formal items to preserve: defn (choice function, choice function for A), axiom[Choice] (AX-SET009), thm[thmwochoice] (THM-SET001)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: preserve
  - Proofs: preserve full (both directions of the equivalence)

---

### sth/choice/countablechoice -- Countable Choice
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics (Choice variants)
- **Rationale**: STEPPING-STONE. Discusses Countable Choice as weaker principle. Preserve key results; compress historical discussion and Russell's boots-and-socks example.
- **Content Directives**:
  - Formal items to preserve: defish[Countable Choice] (OL-ONLY, statement), thm (countable union of countable sets is countable -- in Z^- + Countable Choice, statement)
  - Formal items to drop: lem (every finite set has a choice function -- in Z^-) (OL-ONLY, technical), thm (every set is finite or infinite -- in Z^- + Countable Choice) (OL-ONLY, preserve as remark)
  - Prose: compress to definition of Countable Choice + key consequences (2-3 sentences)
  - Examples: cut all (Russell's boots-and-socks is pedagogical)
  - Proofs: cut (preserve statements only)

---

### sth/choice/justifications -- Intrinsic Considerations about Choice
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics (Choice justification remark)
- **Rationale**: PEDAGOGICAL. Philosophical justification of Choice via StagesAcc. However, it introduces THM-SET003 (Zorn's Lemma as equivalent) by mention. The lean text needs Zorn's Lemma stated somewhere. Compress to: (1) statement of Zorn's Lemma equivalence (THM-SET003), (2) brief justification remark.
- **Content Directives**:
  - Formal items to preserve: thm[choiceset] (Choice iff choice sets -- OL-ONLY, statement), THM-SET003 mention (Zorn's Lemma equivalence -- state formally per domain spec DEF-SET010)
  - Formal items to drop: none
  - Prose: compress to statement of Zorn's Lemma equivalence + 2-sentence justification remark
  - Examples: cut all
  - Proofs: cut (proof left as exercise in OL anyway)

---

### sth/choice/banach -- The Banach-Tarski Paradox
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: TANGENTIAL. Discussion of Banach-Tarski Paradox as consequence of Choice. Stated but not proved. No taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: thm[Banach-Tarski Paradox] (OL-ONLY, stated not proved)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/choice/vitali -- Appendix: Vitali's Paradox
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: TANGENTIAL. Detailed proof of Vitali's Paradox and Hausdorff's Paradox. Outside taxonomy scope -- these are applications of Choice in analysis/measure theory, not formal set theory for logic.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: thm[vitaliparadox] (OL-ONLY), lem[rotationsgroupabelian] (OL-ONLY), lem[disjointgroup] (OL-ONLY), lem[vitalicover] (OL-ONLY), lem[vitalinooverlap] (OL-ONLY), lem[pseudobanachtarski] (OL-ONLY), cor[Vitali] (OL-ONLY), thm[Hausdorff's Paradox] (OL-ONLY)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### SET Batch Summary

- **Total sections**: 62
- **Action distribution**:

| Action | Count |
|--------|-------|
| KEEP | 17 |
| CONDENSE | 27 |
| ABSORB | 1 |
| MERGE-INTO | 0 |
| CUT | 17 |
| DISTRIBUTE | 0 |
| **Total** | **62** |

**Per-chapter breakdown**:

| Chapter | Sections | KEEP | CONDENSE | ABSORB | CUT |
|---------|----------|------|----------|--------|-----|
| story/ | 6 | 1 | 0 | 0 | 5 |
| z/ | 9 | 5 | 3 | 0 | 1 |
| ordinals/ | 10 | 6 | 2 | 0 | 2 |
| spine/ | 6 | 2 | 4 | 0 | 0 |
| replacement/ | 8 | 0 | 4 | 0 | 4 |
| ord-arithmetic/ | 5 | 0 | 4 | 0 | 1 |
| cardinals/ | 5 | 0 | 3 | 1 | 1 |
| card-arithmetic/ | 5 | 2 | 3 | 0 | 0 |
| choice/ | 8 | 1 | 4 | 0 | 3 |
| **Total** | **62** | **17** | **27** | **1** | **17** |

- **Taxonomy coverage**: All SET taxonomy items (3 PRIM + 15 DEF + 9 AX + 3 THM) have authoritative homes:

| ID | Concept | Authoritative Section | Action |
|----|---------|----------------------|--------|
| PRIM-SET001 | Set (formal) | SET.1 opening | FORMALIZE (per A4) |
| PRIM-SET002 | Membership (formal) | sth/story/extensionality | KEEP (implicit in AX-SET001) |
| PRIM-SET003 | Class (informal) | sth/ordinals/basic | KEEP (via Burali-Forti) |
| AX-SET001 | Extensionality | sth/story/extensionality | KEEP |
| AX-SET002 | Empty Set | sth/z/sep | KEEP (derived) |
| AX-SET003 | Pairing | sth/z/pairs | KEEP |
| AX-SET004 | Union | sth/z/union | KEEP |
| AX-SET005 | Power Set | sth/z/power | KEEP |
| AX-SET006 | Separation | sth/z/sep | KEEP |
| AX-SET007 | Replacement | sth/ordinals/replacement | KEEP |
| AX-SET008 | Foundation | sth/spine/foundation | CONDENSE (axiom preserved) |
| AX-SET009 | Choice/Well-Ordering | sth/choice/woproblem (Choice); sth/cardinals/cardsasords (WO) | KEEP; ABSORB |
| DEF-SET001 | Ordinal | sth/ordinals/vn | KEEP |
| DEF-SET002 | Transitive Set | sth/ordinals/vn | KEEP |
| DEF-SET003 | Von Neumann Ordinal | sth/ordinals/vn | KEEP |
| DEF-SET004 | Successor Ordinal | sth/ordinals/opps | KEEP |
| DEF-SET005 | Limit Ordinal | sth/ordinals/opps | KEEP |
| DEF-SET006 | Transfinite Induction | sth/ordinals/basic | KEEP |
| DEF-SET007 | Transfinite Recursion | sth/spine/recursion | KEEP |
| DEF-SET008 | Cardinal Number | sth/cardinals/cardsasords | ABSORB |
| DEF-SET009 | Well-Ordering | sth/ordinals/wo | KEEP |
| DEF-SET010 | Zorn's Lemma | sth/choice/justifications | CONDENSE |
| DEF-SET011 | Cantor's Theorem (formal) | sth/card-arithmetic/opps | KEEP |
| DEF-SET012 | Von Neumann Hierarchy | sth/spine/valpha | KEEP |
| DEF-SET013 | Aleph Numbers | sth/card-arithmetic/ch | KEEP |
| DEF-SET014 | Cofinality | (no OL section) | DEFER (deferred, per domain spec) |
| DEF-SET015 | Continuum Hypothesis | sth/card-arithmetic/ch | KEEP |
| THM-SET001 | WO iff Zorn iff AC | sth/choice/woproblem | KEEP |
| THM-SET002 | Transfinite Recursion Thm | sth/spine/recursion | KEEP |
| THM-SET003 | Cantor's Thm (in ZFC) | sth/card-arithmetic/opps | KEEP |

- **Compression targets resolved**:
  - **AX-SET009** (Choice, 2 sections): Primary = sth/choice/woproblem (KEEP, proves equivalence THM-SET001). Secondary = sth/cardinals/cardsasords (ABSORB, introduces Well-Ordering axiom first). Both preserved: cardsasords defines Well-Ordering as axiom for cardinal theory; woproblem proves Choice equivalent and is the authoritative proof of THM-SET001.
  - **DEF-SET008** (Cardinal Number, 2 sections): Primary = sth/cardinals/cardsasords (ABSORB, formal definition defn[defcardinalasordinal]). Secondary = sth/cardinals/cp (CONDENSE to motivation paragraph absorbed into cardsasords).

- **Surviving sections**: 17 KEEP + 27 CONDENSE + 1 ABSORB = 45 surviving (out of 62)
- **Sections cut**: 17 (all PEDAGOGICAL or TANGENTIAL with no taxonomy items)
- **Compression ratio**: 27% of sections eliminated entirely; effective content volume reduction significantly higher due to 27 CONDENSE entries compressing prose, examples, and proofs
- **Estimated page count**: ~40-50 pages for CH-SET in the lean text (17 full sections + 27 condensed sections + 1 absorbed)
