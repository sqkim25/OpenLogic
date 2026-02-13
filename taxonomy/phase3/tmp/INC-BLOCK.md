# INC Batch — Compression Plan (Step 6)

## CH-INC (feeds into CH-META, CH-CMP, CH-DED, CH-SEM)

Note: INC sections do not form a standalone lean chapter. Their content distributes across CH-META (incompleteness theorems CP-005 through CP-008), CH-CMP (representability, arithmetization), CH-DED (theory definitions Q, PA, derivability conditions), and CH-SEM (standard model, true arithmetic, undefinability of truth).

---

## Chapter 1: Introduction to Incompleteness (`inc/int/`)

### inc/int/bgr -- Historical Background
- **Action**: CUT
- **Lean Chapter**: (none)
- **Lean Section**: (none)
- **Rationale**: PEDAGOGICAL only. Pure narrative covering Aristotle through Godel. No formal definitions or theorems. No taxonomy items introduced or needed.
- **Content Directives**:
  - Formal items to preserve: (none)
  - Formal items to drop: (none -- no formal items exist)
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: N/A

### inc/int/def -- Definitions
- **Action**: DISTRIBUTE
- **Lean Chapter**: CH-DED, CH-SEM, CH-CMP
- **Lean Section**: DED.6, SEM.5, CMP.5, CMP.6
- **Rationale**: CORE-DEF section introducing items across 4 domains. Each formal item goes to its taxonomy-owner's lean chapter. This is the densest definition section in the INC batch.
- **Content Directives**:
  - defn (theory, as deductively closed set) [DEF-INC001] -> CUT: subsumed by DEF-DED003 (Deductive Closure) already in DED.1
  - defn[def:standard-model] (Standard Model N) [DEF-INC002 -> DEF-SEM017] -> SEM.5: preserve full definition
  - defn (True Arithmetic TA) [DEF-INC003 -> DEF-SEM018] -> SEM.5: preserve full definition
  - defn (axiomatized theory) [DEF-INC004] -> CUT: restates basic concept already covered in DED.1 under PRIM-DED002
  - defn (Q, Robinson's Q with 8 axioms) [DEF-INC005 -> DEF-DED011] -> DED.6: preserve full definition including all 8 axiom schemas
  - defn (PA, Peano Arithmetic with induction schema) [DEF-INC006 -> DEF-DED012] -> DED.6: preserve full definition
  - defn (complete theory) [DEF-INC007] -> CUT: subsumed by DEF-SEM005 (Semantic Completeness of a theory) already in SEM.3
  - defn (decidable set) -> CUT: merely references PRIM-CMP006, already in CMP.3
  - defn (axiomatizable, by decidable axiom set) [DEF-INC008 -> DEF-CMP011] -> CMP.6: preserve full definition
  - defn (c.e.) -> CUT: merely references PRIM-CMP007, already in CMP.3
  - defn (represents function) [DEF-CMP009] -> CMP.5: preserve full definition (both conditions)
  - defn (represents relation) [DEF-INC009] -> CMP.5: preserve full definition (both conditions)
  - Prose: distribute introductory sentences to each target section; cut general motivation
  - Examples: keep the PA axiomatizability example (finite axiom check + induction schema check) in CMP.6
  - Proofs: N/A (definition section)

### inc/int/ovr -- Overview of Incompleteness Results
- **Action**: CUT
- **Lean Chapter**: (none)
- **Lean Section**: (none)
- **Rationale**: PEDAGOGICAL only. Roadmap section that informally previews CP-005 and CP-006 without proving anything. No formal items survive.
- **Content Directives**:
  - Formal items to preserve: (none)
  - Formal items to drop: thm (informal statement of first incompleteness) -- pedagogical preview only
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: N/A

### inc/int/dec -- Undecidability and Incompleteness
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems (stepping stone for CP-005)
- **Rationale**: STEPPING-STONE. Proves a weak version of first incompleteness via diagonal argument and the key lemma "axiomatizable + complete => decidable." The weak incompleteness result and the axiomatizable+complete=>decidable lemma are useful stepping stones that belong in CMP.7 since they connect computability to incompleteness.
- **Content Directives**:
  - Formal items to preserve: thm (consistent theory representing all decidable relations is not decidable); thm (axiomatizable + complete => decidable); cor[cor:incompleteness] (weak first incompleteness)
  - Formal items to drop: prob (TA not axiomatizable) -- pedagogical exercise
  - Prose: compress to intro + theorem statements only
  - Examples: cut all (Presburger arithmetic mention is tangential)
  - Proofs: preserve sketch only for the two theorems; the corollary follows immediately

---

## Chapter 2: Arithmetization of Syntax (`inc/art/`)

### inc/art/int -- Introduction (Arithmetization)
- **Action**: CUT
- **Lean Chapter**: (none)
- **Lean Section**: (none)
- **Rationale**: PEDAGOGICAL only. Motivational section with no formal items. The arithmetization idea is introduced by the definitions in inc/art/cod.
- **Content Directives**:
  - Formal items to preserve: (none)
  - Formal items to drop: (none -- no formal items)
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: N/A

### inc/art/cod -- Coding Symbols
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality (instantiates PRIM-CMP011)
- **Rationale**: STEPPING-STONE. Defines symbol codes and Godel numbers (DEF-INC010, DEF-INC011 instantiating PRIM-CMP011). Essential for the arithmetization chain. Preserve definitions, compress verification.
- **Content Directives**:
  - Formal items to preserve: defn (symbol code) [DEF-INC010]; defn (Godel number) [DEF-INC011]
  - Formal items to drop: prop (Fn, Pred primitive recursive) -- stepping stone, state without proof
  - Prose: compress to intro + definitions only
  - Examples: cut all (specific code assignments are implementation details)
  - Proofs: cut (primitive recursiveness of Fn, Pred stated as remark)

### inc/art/trm -- Coding Terms
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. Shows Term(x) and ClTerm(x) are primitive recursive. Essential link in arithmetization chain but verification details can be compressed.
- **Content Directives**:
  - Formal items to preserve: prop[prop:term-primrec] (Term(x) primitive recursive); prop[prop:num-primrec] (num(n) primitive recursive) -- state results
  - Formal items to drop: (none)
  - Prose: compress to statement of results + one-sentence inductive argument sketch
  - Examples: cut all
  - Proofs: preserve sketch only (note formation sequences provide inductive structure)

### inc/art/frm -- Coding Formulas
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. Extends primitive recursiveness to formulas and sentences. Essential for proof predicate construction.
- **Content Directives**:
  - Formal items to preserve: prop[prop:frm-primrec] (Frm(x) primitive recursive); prop (Sent(x) primitive recursive)
  - Formal items to drop: prop (Atom(x) primitive recursive) -- intermediate step; prop[prop:freeocc-primrec] (FreeOcc primitive recursive) -- intermediate step
  - Prose: compress to statement of results
  - Examples: cut all
  - Proofs: preserve sketch only (parallel structure to term case)

### inc/art/sub -- Substitution
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. Shows Subst(x,y,z) is primitive recursive. Needed for fixed-point lemma.
- **Content Directives**:
  - Formal items to preserve: prop[prop:subst-primrec] (Subst(x,y,z) primitive recursive)
  - Formal items to drop: prop[prop:free-for] (FreeFor primitive recursive) -- intermediate step
  - Prose: compress to statement of result
  - Examples: cut all
  - Proofs: preserve sketch only

### inc/art/plk -- Derivations in LK
- **Action**: ABSORB:{inc/art/pnd, inc/art/pax}
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality (DEF-INC012 Proof Predicate)
- **Rationale**: STEPPING-STONE. This is the primary section for DEF-INC012 (Proof Predicate Prf_Gamma(x,y)). Under A1 (generic proof theory), we present the proof predicate once generically, noting that the construction works for any proof system (LK, ND, AX) with appropriate Godel numbering of derivations. LK chosen as primary because it has the most explicit and complete treatment with fully worked FollowsBy definitions. The ND and AX variants merge into this section.
- **Content Directives**:
  - Formal items to preserve: defn (Godel number of derivation -- generalized); prop[prop:followsby] (Correct(p) primitive recursive); prop[prop:deriv] (Deriv(p) primitive recursive); prop (Prf_Gamma(x,y) primitive recursive) [DEF-INC012]
  - Formal items to drop: prob (define FollowsBy for specific rules) -- exercise; ex (specific LK derivation Godel number) -- keep as canonical example
  - From inc/art/pnd: absorb nothing (parallel content, ND-specific encoding details dropped)
  - From inc/art/pax: absorb nothing (parallel content, AX-specific encoding details dropped)
  - Prose: compress to intro + generic proof predicate construction + result statements. Note variant proof systems in a remark.
  - Examples: keep 1 (the LK derivation example showing concrete Godel number computation)
  - Proofs: preserve sketch only for Correct(p); preserve full proof for Prf_Gamma(x,y)

### inc/art/pnd -- Derivations in Natural Deduction
- **Action**: MERGE-INTO:inc/art/plk
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. ND variant of DEF-INC012 (Proof Predicate). Under A1, the generic proof predicate is defined once in inc/art/plk. The ND-specific encoding details (Assum, Discharge, OpenAssum as primitive recursive) are noted as a remark in the generic treatment.
- **Content Directives**:
  - Formal items to preserve: (none -- all absorbed into inc/art/plk's generic treatment)
  - Formal items to drop: all ND-specific propositions -- subsumed by generic proof predicate
  - Prose: replace with cross-ref to inc/art/plk
  - Examples: cut all
  - Proofs: cut all

### inc/art/pax -- Axiomatic Derivations
- **Action**: MERGE-INTO:inc/art/plk
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. AX variant of DEF-INC012 (Proof Predicate). Under A1, merges into the generic treatment in inc/art/plk. The AX encoding is simpler (derivations are sequences) but the result is the same.
- **Content Directives**:
  - Formal items to preserve: (none -- all absorbed into inc/art/plk's generic treatment)
  - Formal items to drop: all AX-specific propositions -- subsumed by generic proof predicate
  - Prose: replace with cross-ref to inc/art/plk
  - Examples: cut all
  - Proofs: cut all

---

## Chapter 3: Representability in Q (`inc/req/`)

### inc/req/int -- Introduction (Representability)
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality (DEF-CMP009 restated)
- **Rationale**: CORE-DEF. Restates Q axioms and representability definition, announces the main representability theorem. Since inc/int/def distributes DEF-CMP009 to CMP.5, this section provides the most complete treatment context for the representability theorem statement. Keep the theorem statement and proof strategy outline; compress the Q restatement.
- **Content Directives**:
  - Formal items to preserve: defn[defn:representable-fn] (representable in Q) -- cross-ref to CMP.5 DEF-CMP009; thm[thm:representable-iff-comp] (representable iff computable) -- core theorem statement
  - Formal items to drop: Q axiom restatement -- already in DED.6
  - Prose: compress to theorem statement + 1 paragraph proof strategy outline
  - Examples: cut all
  - Proofs: cut (proof is assembled across the chapter)

### inc/req/rpc -- Functions Representable in Q are Computable
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. One direction of the representability theorem: representable implies computable. Key stepping stone.
- **Content Directives**:
  - Formal items to preserve: lem (every representable function is computable) -- key direction
  - Formal items to drop: lem[lem:rep-q] (Q proves A_f(n,m) iff m=f(n)) -- intermediate step, fold into main lemma proof
  - Prose: compress to statement + proof sketch
  - Examples: cut all
  - Proofs: preserve sketch only (uses proof predicate and Godel numbering to define f by minimization)

### inc/req/bet -- The Beta Function Lemma
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. The beta function lemma (DEF-INC013) is a key technical tool for simulating primitive recursion. Needed for the representability theorem.
- **Content Directives**:
  - Formal items to preserve: lem[lem:beta] (beta function lemma) [DEF-INC013]
  - Formal items to drop: thm (Chinese Remainder Theorem) -- standard number theory result, state without proof
  - Prose: compress to definition of beta function + lemma statement
  - Examples: cut all
  - Proofs: preserve sketch only (cite CRT, state key idea)

### inc/req/pri -- Simulating Primitive Recursion
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. Shows primitive recursion reducible to composition + regular minimization via beta function. Key link in representability chain.
- **Content Directives**:
  - Formal items to preserve: lem[lem:prim-rec] (primitive recursion reducible to composition + regular minimization)
  - Formal items to drop: (none)
  - Prose: compress to statement + 2-sentence proof idea
  - Examples: cut all
  - Proofs: preserve sketch only

### inc/req/bre -- Basic Functions are Representable in Q
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. Base cases for the representability theorem. Many individual propositions, each a small verification. Compress to a summary statement with key proof idea.
- **Content Directives**:
  - Formal items to preserve: prop[prop:rep-zero] (Zero representable); prop[prop:rep-succ] (Succ representable); prop[prop:rep-add] (Add representable); prop[prop:rep-mult] (Mult representable); lem[lem:q-proves-neq] (Q proves numerals distinct) -- needed downstream
  - Formal items to drop: prop[prop:rep-proj] (Projection representable) -- trivial; prop[prop:rep-id] (Char= representable) -- minor; lem[lem:q-proves-add] -- intermediate; lem[lem:q-proves-mult] -- intermediate
  - Prose: compress to summary of which functions are representable + key proof techniques
  - Examples: cut all
  - Proofs: preserve sketch only for Add and Mult (hardest cases); cut proofs for Zero, Succ, Proj (trivial)

### inc/req/cmp -- Composition is Representable in Q
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. Closure of representable functions under composition. Essential step.
- **Content Directives**:
  - Formal items to preserve: prop[prop:rep-composition] (representable functions closed under composition)
  - Formal items to drop: (none)
  - Prose: compress to statement
  - Examples: cut all
  - Proofs: preserve sketch only

### inc/req/min -- Regular Minimization is Representable in Q
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. Closure under regular minimization. Most technically demanding step of the representability proof.
- **Content Directives**:
  - Formal items to preserve: prop[prop:rep-minimization] (representable functions closed under regular minimization); lem[lem:less-nsucc] (Q proves x < n+1 implies disjunction of equalities) -- needed in Rosser proof; lem[lem:trichotomy] (Q proves trichotomy for numerals) -- needed in Rosser proof
  - Formal items to drop: lem[lem:succ] (Q proves a'+n = (a+n)') -- intermediate; lem[lem:less-zero] (Q proves not x < 0) -- intermediate
  - Prose: compress to statement of closure result + key lemma statements
  - Examples: cut all
  - Proofs: preserve sketch only for prop:rep-minimization; cut proofs of intermediate lemmas (state as used facts)

### inc/req/crq -- Computable Functions are Representable in Q
- **Action**: ABSORB:{inc/req/cee, inc/req/cre}
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: CORE-THM. Assembles all preceding results to complete the "computable implies representable" direction. Together with inc/req/rpc, establishes the full representability theorem. This is a key stepping stone for CP-005. Absorbs inc/req/cee and inc/req/cre (alternative proof path via class C) as a brief remark noting the alternative approach.
- **Content Directives**:
  - Formal items to preserve: thm (every computable function is representable in Q)
  - Formal items to drop: (none)
  - From inc/req/cee: absorb as 1-sentence remark noting alternative approach via class C
  - From inc/req/cre: absorb nothing (duplicate content)
  - Prose: preserve -- short assembly of results + remark on alternative approach
  - Examples: cut all
  - Proofs: preserve full (short: assembles base cases + closure results)

### inc/req/cee -- The Functions C
- **Action**: MERGE-INTO:inc/req/crq
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. Alternative proof path defining class C. Redundant with the main approach (inc/req/bre through inc/req/crq). The lean text uses one proof path only.
- **Content Directives**:
  - Formal items to preserve: (none -- subsumed by main proof path)
  - Formal items to drop: DEF-INC014 (Class C) -- redundant alternative approach
  - Prose: replace with cross-ref note in inc/req/crq mentioning alternative approach
  - Examples: cut all
  - Proofs: cut all

### inc/req/cre -- Functions in C are Representable in Q
- **Action**: MERGE-INTO:inc/req/crq
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. Alternative proof presentation that duplicates material from inc/req/bre and others. Redundant with the main proof chain.
- **Content Directives**:
  - Formal items to preserve: (none -- content duplicated in main proof chain)
  - Formal items to drop: all -- duplicate of bre/cmp/min content
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: cut all

### inc/req/rel -- Representing Relations
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. Extends representability theorem from functions to relations. Important for downstream use (proof predicate, undecidability).
- **Content Directives**:
  - Formal items to preserve: defn[defn:representing-relations] (representable relation) -- restates DEF-INC009; thm[thm:representing-rels] (relation representable iff computable)
  - Formal items to drop: (none)
  - Prose: compress to definition + theorem statement
  - Examples: cut all
  - Proofs: preserve sketch only

### inc/req/und -- Undecidability
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.8: Undecidability (CP-008)
- **Rationale**: CORE-THM. Proves undecidability of Q by reduction from the halting problem. The corollary that first-order logic is undecidable is CP-008 (Church's Undecidability of Validity). This is the authoritative section for CP-008.
- **Content Directives**:
  - Formal items to preserve: thm (Q is undecidable); cor (first-order logic is undecidable) [CP-008]
  - Formal items to drop: (none)
  - Prose: preserve
  - Examples: N/A
  - Proofs: preserve full (both the main theorem and the corollary)

### inc/inp/s1c -- Sigma-1 Completeness
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.5: First Incompleteness (supports CP-005)
- **Rationale**: CORE-THM. Defines the arithmetic hierarchy (DEF-INC015 Delta_0, DEF-INC016 Sigma_1, DEF-INC017 Pi_1) and proves Sigma_1-completeness of Q. This is a crucial result used in incompleteness proofs.
- **Content Directives**:
  - Formal items to preserve: defn[defn:bd-quant] (bounded quantifiers); defn[defn:delta0-sigma1-pi1-frm] (Delta_0, Sigma_1, Pi_1 formulas) [DEF-INC015, DEF-INC016, DEF-INC017]; thm[thm:sigma1-completeness] (Sigma_1 completeness of Q)
  - Formal items to drop: (none -- all lemmas are essential stepping stones for the main theorem)
  - Prose: preserve (definitions + theorem + lemma chain)
  - Examples: N/A
  - Proofs: preserve full (lem:q-proves-clterm-id, lem:atomic-completeness, lem:bounded-quant-equiv, lem:delta0-completeness all lead to thm:sigma1-completeness)

---

## Chapter 4: Theories and Computability (`inc/tcp/`)

### inc/tcp/int -- Introduction (Theories and Computability)
- **Action**: CUT
- **Lean Chapter**: (none)
- **Lean Section**: (none)
- **Rationale**: PEDAGOGICAL only. Brief intro summarizing previous results. No formal items. Editorially marked as needing rewrite.
- **Content Directives**:
  - Formal items to preserve: (none)
  - Formal items to drop: (none -- no formal items)
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: N/A

### inc/tcp/qce -- Q is c.e.-Complete
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems
- **Rationale**: STEPPING-STONE. Shows Q is c.e.-complete (K reduces to Q). Important stepping stone for the undecidability chain but the detailed reduction proof can be compressed.
- **Content Directives**:
  - Formal items to preserve: thm (Q is c.e.-complete)
  - Formal items to drop: (none)
  - Prose: compress to statement
  - Examples: cut all
  - Proofs: preserve sketch only (note K reduces to Q via representability of T predicate)

### inc/tcp/oqn -- Omega-Consistent Extensions of Q are Undecidable
- **Action**: CONDENSE
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.6: Theories and Arithmetic (DEF-INC018 omega-consistency)
- **Rationale**: STEPPING-STONE. Introduces DEF-INC018 (omega-consistency) and proves a stepping stone. The omega-consistency definition is important (used in G1 original form). The undecidability result is superseded by inc/tcp/cqn.
- **Content Directives**:
  - Formal items to preserve: defn[thm:oconsis-q] (omega-consistency) [DEF-INC018] -> DED.6
  - Formal items to drop: thm (omega-consistent extension of Q is not decidable) -- superseded by inc/tcp/cqn
  - Prose: compress to omega-consistency definition + 1 sentence noting the result
  - Examples: cut all
  - Proofs: cut (superseded by stronger result)

### inc/tcp/cqn -- Consistent Extensions of Q are Undecidable
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems
- **Rationale**: STEPPING-STONE. Strengthens omega-consistency result to simple consistency. Key stepping stone for inc/tcp/inc. Uses diagonal argument (no universal computable relation).
- **Content Directives**:
  - Formal items to preserve: thm (consistent extension of Q is not decidable)
  - Formal items to drop: lem (no universal computable relation) -- fold into proof sketch; cor (true arithmetic not decidable) -- immediate corollary, state as remark
  - Prose: compress to theorem statement + proof sketch
  - Examples: cut all
  - Proofs: preserve sketch only (key idea: if T decidable, construct universal computable relation via representability)

### inc/tcp/cax -- Axiomatizable Theories
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.6: Computability Theory
- **Rationale**: STEPPING-STONE. Short section establishing axiomatizable implies c.e. Important linking lemma.
- **Content Directives**:
  - Formal items to preserve: lem (axiomatizable implies c.e.)
  - Formal items to drop: (none)
  - Prose: compress to statement
  - Examples: cut all
  - Proofs: preserve sketch only (enumerate all derivations from decidable axiom set)

### inc/tcp/cdc -- Axiomatizable Complete Theories are Decidable
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems
- **Rationale**: STEPPING-STONE. Key connecting lemma: complete + axiomatizable + consistent => decidable. Directly used in inc/tcp/inc for the computability-theoretic first incompleteness theorem. Note: this result also appears as stepping stone in inc/int/dec; the authoritative treatment is here.
- **Content Directives**:
  - Formal items to preserve: lem (complete + axiomatizable implies decidable)
  - Formal items to drop: (none)
  - Prose: compress to statement + 2-sentence proof idea
  - Examples: cut all
  - Proofs: preserve sketch only (simultaneous search for proof of A and proof of not-A)

### inc/tcp/inc -- Q has no Complete, Consistent, Axiomatizable Extensions
- **Action**: MERGE-INTO:inc/inp/1in
- **Lean Chapter**: CH-META
- **Lean Section**: META.5: First Incompleteness (CP-005)
- **Rationale**: CORE-THM but CP-005 redundancy. This is the computability-theoretic version of the First Incompleteness Theorem, which is weaker than the Rosser version (inc/inp/ros) because it does not construct an explicit independent sentence. The lean text presents CP-005 via the Godel sentence + Rosser improvement in META.5. This section's short proof (combining cqn + cdc) is noted as a remark/alternative proof in META.5.
- **Content Directives**:
  - Formal items to preserve: thm[thm:first-incompleteness] (no complete, consistent, axiomatizable extension of Q) -- survives as remark/alternative proof in inc/inp/1in
  - Formal items to drop: (none)
  - Prose: replace with 2-sentence remark in META.5 noting the alternative computability-theoretic proof
  - Examples: cut all
  - Proofs: preserve sketch only (3-line proof: cqn + cdc => result)

### inc/tcp/ins -- Sentences Provable and Refutable in Q are Computably Inseparable
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems
- **Rationale**: STEPPING-STONE. Shows computable inseparability of Q and Q-bar (DEF-INC019). Used in inc/tcp/con for the strongest undecidability results.
- **Content Directives**:
  - Formal items to preserve: lem (Q and Q-bar are computably inseparable) [DEF-INC019]
  - Formal items to drop: (none)
  - Prose: compress to definition of computable inseparability + lemma statement
  - Examples: cut all
  - Proofs: preserve sketch only (uses non-existence of universal computable relation)

### inc/tcp/con -- Theories Consistent with Q are Undecidable
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems
- **Rationale**: STEPPING-STONE. Stronger than cqn: theory need not extend Q, only be consistent with it. The corollary (CP-008 alternative proof) is secondary to the authoritative CP-008 in inc/req/und.
- **Content Directives**:
  - Formal items to preserve: thm (theory consistent with Q is undecidable)
  - Formal items to drop: cor (FOL for language of arithmetic is undecidable) -- duplicate of CP-008, already in inc/req/und
  - Prose: compress to theorem statement
  - Examples: cut all
  - Proofs: preserve sketch only (uses computable inseparability)

### inc/tcp/itp -- Theories in which Q is Interpretable are Undecidable
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems
- **Rationale**: STEPPING-STONE. Most general undecidability result. Introduces interpretability informally (DEF-INC020). Applications to ZFC.
- **Content Directives**:
  - Formal items to preserve: thm (theory interpreting Q and consistent with it is undecidable); cor (no decidable extension of ZFC); cor (FOL for language with binary relation is undecidable) -- strongest form of CP-008
  - Formal items to drop: cor (no complete consistent axiomatizable extension of ZFC) -- follows immediately; DEF-INC020 (Interpretability informal) -- keep as remark, not formal definition
  - Prose: compress to theorem + corollaries + 1 remark about decidability boundary (unary predicates + at most one unary function)
  - Examples: cut all
  - Proofs: preserve sketch only (small modification of inc/tcp/con proof)

---

## Chapter 5: Incompleteness and Provability (`inc/inp/`)

### inc/inp/int -- Introduction (Incompleteness and Provability)
- **Action**: CUT
- **Lean Chapter**: (none)
- **Lean Section**: (none)
- **Rationale**: PEDAGOGICAL only. Motivates the Godel sentence via the Epimenides/liar paradox and Quine's version. No formal items (fixed-point lemma merely previewed informally). The fixed-point lemma explanation in inc/inp/fix already contains the necessary motivation.
- **Content Directives**:
  - Formal items to preserve: (none)
  - Formal items to drop: lem (fixed-point lemma -- informal preview) -- pedagogical
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: N/A

### inc/inp/fix -- The Fixed-Point Lemma
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.5: First Incompleteness (DEF-INC021)
- **Rationale**: CORE-THM. The fixed-point (diagonalization) lemma is the fundamental technical tool for all major incompleteness results. Must be preserved in full including the diag function construction and the formal proof.
- **Content Directives**:
  - Formal items to preserve: lem[lem:fixed-point] (fixed-point lemma) [DEF-INC021]
  - Formal items to drop: prob (no truth definition via fixed point) -- pedagogical exercise (but the idea reappears in inc/inp/tar)
  - Prose: preserve (the explanation of diag function construction is essential for understanding)
  - Examples: N/A
  - Proofs: preserve full

### inc/inp/1in -- The First Incompleteness Theorem
- **Action**: ABSORB:{inc/tcp/inc}
- **Lean Chapter**: CH-META
- **Lean Section**: META.5: First Incompleteness (CP-005)
- **Rationale**: CORE-THM. This is Godel's original proof of the First Incompleteness Theorem via the Godel sentence construction. This is the authoritative section for CP-005. Absorbs inc/tcp/inc (computability-theoretic version) as an alternative proof remark.
- **Content Directives**:
  - Formal items to preserve: lem[lem:cons-G-unprov] (if T consistent, T does not derive G_T); defn[thm:oconsis-q] (omega-consistency) -- cross-ref to DED.6 for authoritative definition; lem[lem:omega-cons-G-unref] (if T omega-consistent, T does not derive not-G_T); thm[thm:first-incompleteness] (First Incompleteness Theorem, omega-consistency version) [CP-005]
  - Formal items to drop: prob (consistent but omega-inconsistent theory) -- pedagogical exercise
  - From inc/tcp/inc: absorb as remark "Alternative proof via computability theory: combining undecidability of consistent extensions of Q with the fact that axiomatizable complete theories are decidable yields the result without constructing an explicit Godel sentence."
  - Prose: preserve (proof construction is essential)
  - Examples: N/A
  - Proofs: preserve full (both lemmas + theorem)

### inc/inp/ros -- Rosser's Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.5: First Incompleteness (CP-005 strengthened)
- **Rationale**: CORE-THM. Rosser's improvement replaces omega-consistency with simple consistency. Introduces the Rosser provability predicate (DEF-INC022) and Rosser sentence (DEF-INC023). This is the standard modern form of the First Incompleteness Theorem.
- **Content Directives**:
  - Formal items to preserve: thm[thm:rosser] (Rosser's Theorem: consistent + axiomatizable + extends Q => incomplete) [CP-005 strengthened]; DEF-INC022 (Rosser provability predicate RProv_T); DEF-INC023 (Rosser sentence R_T)
  - Formal items to drop: prob (computable inseparability) -- exercise, already covered in inc/tcp/ins
  - Prose: preserve (the Rosser provability predicate construction is essential)
  - Examples: N/A
  - Proofs: preserve full (both directions of the independence argument)

### inc/inp/gop -- Comparison with Godel's Original Paper
- **Action**: CUT
- **Lean Chapter**: (none)
- **Lean Section**: (none)
- **Rationale**: PEDAGOGICAL only. Brief historical comparison with Godel's 1931 paper. No formal items. Historical details about the 45 primitive recursive functions and the beta-lemma are not needed in the lean text.
- **Content Directives**:
  - Formal items to preserve: (none)
  - Formal items to drop: (none -- no formal items)
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: N/A

### inc/inp/prc -- The Derivability Conditions for PA
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.6: Second Incompleteness (DEF-INC024)
- **Rationale**: CORE-DEF. Defines the three Hilbert-Bernays-Lob derivability conditions (P1-P3) that are the hypotheses for the Second Incompleteness Theorem and Lob's Theorem. These are essential for understanding the proof structure of G2 and Lob.
- **Content Directives**:
  - Formal items to preserve: P1 (provability implies provable provability); P2 (provable implication distributes over provability); P3 (provable provability of provability) [DEF-INC024]; P4 (mentioned but noted as not needed)
  - Formal items to drop: (none)
  - Prose: preserve (conditions P1-P3 + the discussion of why P3 requires work)
  - Examples: N/A
  - Proofs: N/A (conditions stated, verification not carried out -- following Godel's practice)

### inc/inp/2in -- The Second Incompleteness Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.6: Second Incompleteness (CP-006)
- **Rationale**: CORE-THM. The Second Incompleteness Theorem is CP-006. Both the PA-specific version and the general version (for any T satisfying P1-P3) are essential. The proof sketch using derivability conditions is the standard modern presentation.
- **Content Directives**:
  - Formal items to preserve: thm[thm:second-incompleteness] (PA consistent => PA does not derive Con(PA)) [CP-006]; thm[thm:second-incompleteness-gen] (general version for T with P1-P3) [CP-006 generalized]
  - Formal items to drop: prob (PA derives G_PA -> Con(PA)) -- exercise
  - Prose: preserve (the step-by-step derivation using P1-P3 is the heart of the proof)
  - Examples: N/A
  - Proofs: preserve full (both specific and general versions)

### inc/inp/lob -- Lob's Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.6: Second Incompleteness (DEF-INC025)
- **Rationale**: CORE-THM. Lob's Theorem (DEF-INC025) generalizes the Second Incompleteness Theorem. The proof uses the fixed-point lemma applied to Prov(y) -> A. The corollary that G2 follows from Lob (take A = falsum) provides an elegant alternative derivation.
- **Content Directives**:
  - Formal items to preserve: thm[thm:lob] (Lob's Theorem) [DEF-INC025]; the corollary deriving G2 from Lob; the observation about the fixed point of Prov(x) being derivable
  - Formal items to drop: prob (conditions for derivability statements) -- exercise
  - Prose: preserve (the Santa Claus heuristic is the best available explanation of the proof idea, and doubles as motivation)
  - Examples: N/A
  - Proofs: preserve full

### inc/inp/tar -- The Undefinability of Truth
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.7: Undefinability (CP-007)
- **Rationale**: CORE-THM. Tarski's Undefinability of Truth theorem is CP-007. The section defines "definable in N," proves every computable relation is definable, proves the halting relation is definable, and then proves the set of true sentences is NOT definable. Clean, self-contained proof.
- **Content Directives**:
  - Formal items to preserve: defn (definable in N); lem (every computable relation is definable in N); lem (halting relation is definable in N); thm[thm:tarski] (set of true sentences not definable) [CP-007]
  - Formal items to drop: prob (Q-provable set is definable) -- exercise
  - Prose: preserve (including Tarski's philosophical analysis of truth predicates -- this is a 1-paragraph remark that contextualizes the result, not pedagogical fluff)
  - Examples: N/A
  - Proofs: preserve full (all lemmas + main theorem)

---

### INC Batch Summary
- **Total sections**: 44
- **Action distribution**: 8 KEEP, 21 CONDENSE, 5 MERGE-INTO, 3 ABSORB, 6 CUT, 1 DISTRIBUTE
- **Verification**: 8 + 21 + 5 + 3 + 6 + 1 = 44 (correct)
- **Detailed action tally**:
  - KEEP (8): inc/req/und, inc/inp/s1c, inc/inp/fix, inc/inp/ros, inc/inp/prc, inc/inp/2in, inc/inp/lob, inc/inp/tar
  - ABSORB (3): inc/art/plk [absorbs pnd, pax], inc/inp/1in [absorbs tcp/inc], inc/req/crq [absorbs cee, cre]
  - CONDENSE (21): inc/int/dec, inc/art/cod, inc/art/trm, inc/art/frm, inc/art/sub, inc/req/int, inc/req/rpc, inc/req/bet, inc/req/pri, inc/req/bre, inc/req/cmp, inc/req/min, inc/req/rel, inc/tcp/qce, inc/tcp/oqn, inc/tcp/cqn, inc/tcp/cax, inc/tcp/cdc, inc/tcp/ins, inc/tcp/con, inc/tcp/itp
  - MERGE-INTO (5): inc/art/pnd -> plk, inc/art/pax -> plk, inc/tcp/inc -> 1in, inc/req/cee -> crq, inc/req/cre -> crq
  - CUT (6): inc/int/bgr, inc/int/ovr, inc/art/int, inc/tcp/int, inc/inp/int, inc/inp/gop
  - DISTRIBUTE (1): inc/int/def
- **Taxonomy coverage**: All INC-related taxonomy items have authoritative homes:
  - CP-005 (First Incompleteness) -> inc/inp/1in (ABSORB from inc/tcp/inc)
  - CP-006 (Second Incompleteness) -> inc/inp/2in (KEEP)
  - CP-007 (Tarski Undefinability) -> inc/inp/tar (KEEP)
  - CP-008 (Church Undecidability) -> inc/req/und (KEEP)
  - DEF-INC010, DEF-INC011 (Symbol code, Godel number) -> inc/art/cod (CONDENSE)
  - DEF-INC012 (Proof Predicate) -> inc/art/plk (ABSORB from pnd, pax)
  - DEF-INC013 (Beta function) -> inc/req/bet (CONDENSE)
  - DEF-INC015-017 (Arithmetic Hierarchy) -> inc/inp/s1c (KEEP)
  - DEF-INC018 (Omega-consistency) -> inc/tcp/oqn (CONDENSE, definition goes to DED.6)
  - DEF-INC019 (Computable inseparability) -> inc/tcp/ins (CONDENSE)
  - DEF-INC020 (Interpretability) -> inc/tcp/itp (CONDENSE, kept as remark)
  - DEF-INC021 (Fixed-Point Lemma) -> inc/inp/fix (KEEP)
  - DEF-INC022 (Rosser provability) -> inc/inp/ros (KEEP)
  - DEF-INC023 (Rosser sentence) -> inc/inp/ros (KEEP)
  - DEF-INC024 (Derivability Conditions) -> inc/inp/prc (KEEP)
  - DEF-INC025 (Lob's Theorem) -> inc/inp/lob (KEEP)
  - DEF-CMP009 (Representability) -> inc/int/def DISTRIBUTE to CMP.5
  - DEF-DED011 (Q) -> inc/int/def DISTRIBUTE to DED.6
  - DEF-DED012 (PA) -> inc/int/def DISTRIBUTE to DED.6
  - DEF-SEM017 (Standard Model) -> inc/int/def DISTRIBUTE to SEM.5
  - DEF-SEM018 (True Arithmetic) -> inc/int/def DISTRIBUTE to SEM.5
  - DEF-CMP011 (Axiomatizable Theory) -> inc/int/def DISTRIBUTE to CMP.6
- **Compression targets resolved**:
  - DEF-INC012 (Proof Predicate, 3 variants): inc/art/plk primary, inc/art/pnd and inc/art/pax MERGE-INTO
  - CP-005 (2 formulations): inc/inp/1in primary (Godel sentence), inc/tcp/inc MERGE-INTO
  - DEF-CMP009 (Representability): inc/int/def distributes to CMP.5; inc/req/int provides the representability theorem context
  - DEF-INC014 (Class C) + inc/req/cre: alternative proof path MERGE-INTO inc/req/crq
  - DEF-INC018 (Omega-consistency, defined in both inc/tcp/oqn and inc/inp/1in): inc/tcp/oqn is authoritative for definition -> DED.6, inc/inp/1in cross-references
- **Lean chapter distribution** (surviving sections only, excluding CUT and MERGE-INTO sources):
  - CH-META: 8 sections (inc/inp/fix, inc/inp/1in [+absorb], inc/inp/ros, inc/inp/prc, inc/inp/2in, inc/inp/lob, inc/inp/tar, inc/req/und)
  - CH-CMP: 20 sections (inc/int/dec, inc/art/cod, inc/art/trm, inc/art/frm, inc/art/sub, inc/art/plk [+absorb], inc/req/int, inc/req/rpc, inc/req/bet, inc/req/pri, inc/req/bre, inc/req/cmp, inc/req/min, inc/req/crq [+absorb], inc/req/rel, inc/tcp/qce, inc/tcp/cqn, inc/tcp/cax, inc/tcp/cdc, inc/tcp/ins, inc/tcp/con, inc/tcp/itp)
  - CH-DED: 1 section (inc/tcp/oqn omega-consistency definition -> DED.6)
  - CH-SEM: 0 sections directly (SEM.5 items come from DISTRIBUTE of inc/int/def)
  - DISTRIBUTE across CH-DED + CH-SEM + CH-CMP: 1 section (inc/int/def)

**MERGE-INTO/ABSORB pairing verification (QC-8)**:
- inc/art/pnd MERGE-INTO inc/art/plk <-> inc/art/plk ABSORB:{inc/art/pnd, inc/art/pax} -- paired
- inc/art/pax MERGE-INTO inc/art/plk <-> (same ABSORB entry) -- paired
- inc/tcp/inc MERGE-INTO inc/inp/1in <-> inc/inp/1in ABSORB:{inc/tcp/inc} -- paired
- inc/req/cee MERGE-INTO inc/req/crq <-> inc/req/crq ABSORB:{inc/req/cee, inc/req/cre} -- paired
- inc/req/cre MERGE-INTO inc/req/crq <-> (same ABSORB entry) -- paired
- All 5 MERGE-INTO entries have corresponding ABSORB entries. QC-8 passes.
