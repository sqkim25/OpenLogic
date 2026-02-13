## CH-CMP: Computation

---

### Chapter: recursive-functions (cmp/rec)

### cmp/rec/int — Introduction
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Purely motivational narrative explaining why number-theoretic functions are central to computability theory. No formal definitions or theorems.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### cmp/rec/pre — Primitive Recursion
- **Action**: MERGE-INTO:cmp/rec/prf
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.1: Recursive Functions
- **Rationale**: Signal is CORE-DEF but the formal definition of PRIM-CMP002 lives in cmp/rec/prf. This section only introduces the recursion pattern informally through examples (exponentiation, addition, multiplication). The pattern $h(x,0)=f(x)$, $h(x,y+1)=g(x,y,h(x,y))$ is stated formally in cmp/rec/prf's defn:primitive-recursion.
- **Content Directives**:
  - Formal items to preserve: none standalone -- the recursion pattern is formalized in cmp/rec/prf
  - Formal items to drop: informal examples of recursion pattern -- subsumed by cmp/rec/prf
  - Prose: replace with cross-ref to cmp/rec/prf
  - Examples: cut all -- pedagogical motivating examples
  - Proofs: N/A

---

### cmp/rec/com — Composition
- **Action**: MERGE-INTO:cmp/rec/prf
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.1: Recursive Functions
- **Rationale**: Signal is CORE-DEF but the formal definition of composition is given in cmp/rec/prf (defn:composition). This section introduces it informally along with projection functions. Both are formally defined in prf.
- **Content Directives**:
  - Formal items to preserve: none standalone -- composition and projection defined formally in cmp/rec/prf
  - Formal items to drop: informal definitions -- subsumed by cmp/rec/prf
  - Prose: replace with cross-ref to cmp/rec/prf
  - Examples: cut all
  - Proofs: N/A

---

### cmp/rec/prf — Primitive Recursive Functions
- **Action**: ABSORB:cmp/rec/pre,cmp/rec/com
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.1: Recursive Functions
- **Rationale**: Sole formal defining occurrence of PRIM-CMP002 (Primitive Recursive Function). Contains defn:primitive-recursion (recursion schema), defn:composition (composition schema), and the inductive definition of the set of PR functions. Signal is CORE-DEF only. Absorbs the informal introductions from cmp/rec/pre and cmp/rec/com.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[primitive-recursion]` (PRIM-CMP002 recursion schema); `\begin{defn}[composition]` (composition schema); `\begin{defn}` (inductive definition of PR functions: Zero, Succ, projections, closed under composition and primitive recursion)
  - Formal items to drop: `\begin{prop}` (addition is PR) -- pedagogical example; `\begin{prop}[mult-pr]` (multiplication is PR) -- pedagogical example; `\begin{ex}` ($h(0)=1, h(y+1)=2h(y)$) -- pedagogical worked example
  - Prose: compress to intro + definitions only; one sentence motivating the recursion pattern (absorbing cmp/rec/pre's intuition); one sentence on projections (absorbing cmp/rec/com)
  - Examples: cut all -- Add and Mult examples are pedagogical
  - Proofs: cut all -- pedagogical verifications

---

### cmp/rec/not — Primitive Recursion Notations
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Notational system ($\fn{Comp}_{k,n}$, $\fn{Rec}_k$) is useful for enumeration but the lean text can handle enumeration directly via coding in cmp/rec/nft.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: notational system -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### cmp/rec/cmp — Primitive Recursive Functions are Computable
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.1: Recursive Functions
- **Rationale**: Signal is CORE-THM only. The claim that every PR function is computable is a key structural fact connecting PRIM-CMP002 to PRIM-CMP001. However, the argument is informal (no formal theorem environment). Condense to a one-paragraph statement of the result.
- **Content Directives**:
  - Formal items to preserve: the claim that every primitive recursive function is computable (state as a proposition)
  - Formal items to drop: N/A (no formal items in OL)
  - Prose: compress to one paragraph stating the result with brief justification (composition and primitive recursion preserve computability)
  - Examples: cut all
  - Proofs: preserve sketch only -- 2-3 sentences on why base cases are computable and closure operations preserve computability

---

### cmp/rec/exa — Examples of Primitive Recursive Functions
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. All 8 propositions are OL-ONLY examples (exp, pred, factorial, truncated subtraction, distance, max, min, closure under sums/products). These are useful for intuition but none carry taxonomy IDs.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all 8 propositions -- pedagogical examples
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### cmp/rec/prr — Primitive Recursive Relations
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.1: Recursive Functions
- **Rationale**: Sole defining occurrence of DEF-CMP003 (Characteristic Function). Signal is CORE-DEF only. Defines PR relations via characteristic functions, proves closure under Boolean operations and bounded quantification, and introduces definition by cases. These are essential machinery for all subsequent CMP results.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` (PR relation via $\Char{R}$) -- DEF-CMP003; `\begin{prop}` (closure under Boolean ops); `\begin{prop}` (closure under bounded quantification); `\begin{prop}` (definition by cases via $\fn{cond}$)
  - Formal items to drop: none -- all are essential building blocks
  - Prose: compress to intro + definitions; retain one-line examples of equality and less-than as PR relations (canonical, uses truncated subtraction)
  - Examples: keep the equality and less-than relations as inline definitions (directly instantiate the concept)
  - Proofs: preserve full for Boolean closure (short, constructive: $\Char{\lnot P} = 1 \tsub \Char{P}$, etc.); preserve full for bounded quantification (short, uses primitive recursion on min/max); preserve sketch for definition by cases

---

### cmp/rec/bmi — Bounded Minimization
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.1: Recursive Functions
- **Rationale**: Signal is STEPPING-STONE only. Bounded minimization ($\bmin{z<y}{R(\vec{x},z)}$) preserves primitive recursiveness and is essential infrastructure for later coding results. The contrast with unbounded minimization motivates PRIM-CMP003.
- **Content Directives**:
  - Formal items to preserve: `\begin{prop}` (bounded minimization is PR) -- essential closure property
  - Formal items to drop: none
  - Prose: compress to intro + proposition statement; one sentence contrasting with unbounded search (foreshadows PRIM-CMP003)
  - Examples: cut all
  - Proofs: preserve sketch only -- bounded minimization is definable by primitive recursion on a conditional

---

### cmp/rec/pri — Primes
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Shows divisibility, primality, and $p_x$ (the $x$-th prime) are PR. These facts are used in cmp/rec/seq for sequence coding, but can be stated as one-line remarks there rather than given a full section.
- **Content Directives**:
  - Formal items to preserve: none standalone -- note in cmp/rec/seq that primality and $p_x$ are PR
  - Formal items to drop: all applications -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### cmp/rec/seq — Sequences
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: Introduces PRIM-CMP011 (Godel Numbering) for sequences. Signal is CORE-DEF. The prime factorization coding $\tuple{a_0,\ldots,a_k} = p_0^{a_0+1} \cdots p_k^{a_k+1}$ is the foundational encoding technique used throughout CMP and INC domains. Per COMPRESSION-TARGET for PRIM-CMP011: this section provides the base coding; cmp/rec/nft is primary for the index/numbering-of-functions aspect. This section is primary for the sequence coding aspect.
- **Content Directives**:
  - Formal items to preserve: coding scheme definition ($\tuple{a_0,\ldots,a_k} = p_0^{a_0+1} \cdots p_k^{a_k+1}$); `\begin{prop}` ($\len{s}$ is PR); `\begin{prop}` ($\fn{append}$ is PR); `\begin{prop}` ($\fn{element}$ is PR); `\begin{prop}` ($\fn{concat}$ is PR); `\begin{prop}[subseq]` ($\fn{subseq}$ is PR); $\fn{sequenceBound}$ definition
  - Formal items to drop: alternative bounded-search definition of $\fn{concat}$ -- redundant with the direct primitive recursive definition; both `\begin{prob}` items -- exercises
  - Prose: preserve -- the coding scheme explanation and the Fundamental Theorem of Arithmetic justification are essential context; add one-line note that divisibility, primality, and $p_x$ are PR (absorbing essential fact from cmp/rec/pri)
  - Examples: N/A (the coding itself serves as the canonical example of PRIM-CMP011)
  - Proofs: preserve full for $\len{s}$ (shows bounded minimization technique); preserve sketch for $\fn{append}$, $\fn{element}$, $\fn{concat}$ (brief constructions)

---

### cmp/rec/tre — Trees
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Tree coding as sequences is an application of cmp/rec/seq's coding. The SubtreeSeq proposition is OL-ONLY.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: `\begin{prop}[subtreeseq]` -- OL-ONLY application
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### cmp/rec/ore — Other Recursions
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Discusses simultaneous recursion, course-of-values recursion -- all reducible to ordinary PR via sequence coding. A one-line remark can be added to cmp/rec/prf or cmp/rec/seq if needed.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### cmp/rec/npr — Non-Primitive Recursive Functions
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.4: Diagonalization and Halting
- **Rationale**: Introduces PRIM-CMP010 (Diagonalization) applied to show PR is a strict subset of computable functions. Signal is CORE-THM only. The diagonalization argument (enumerating PR functions via codes and constructing a function that differs from each) is structurally important and motivates the need for mu-recursion.
- **Content Directives**:
  - Formal items to preserve: the result that there exist computable but non-PR functions (state as theorem)
  - Formal items to drop: Ackermann function discussion -- pedagogical elaboration
  - Prose: compress to theorem statement + proof sketch; one sentence noting this uses PRIM-CMP010 (diagonalization) on the enumeration of PR functions
  - Examples: cut all
  - Proofs: preserve sketch only -- enumerate PR functions via codes (using PRIM-CMP011), diagonalize to get a total computable function not in the list

---

### cmp/rec/par — Partial Recursive Functions
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.1: Recursive Functions
- **Rationale**: Sole formal defining occurrence of PRIM-CMP003 (mu-Recursion), PRIM-CMP001 (Computable Function -- partial and total recursive), and DEF-CMP002 (Total Function -- recursive = total partial recursive). Signal is CORE-DEF only. Per COMPRESSION-TARGET for PRIM-CMP001: this section gives the mathematical (recursive function) definition; tur/mac/una gives the TM-based definition. This is primary because partial recursive functions are the most general formulation.
- **Content Directives**:
  - Formal items to preserve: definition of unbounded search $\mu x \; f(x,\vec{z})$ (PRIM-CMP003); `\begin{defn}` (partial recursive functions) -- PRIM-CMP001; `\begin{defn}[recursive-fn]` (recursive = total partial recursive) -- DEF-CMP002; notation $f(x) \fdefined$, $f(x) \fundefined$, $f(x) \simeq g(x)$
  - Formal items to drop: none
  - Prose: preserve -- the motivation for allowing partial functions and the operational intuition for unbounded search are essential context; compress the explain block about composition/PR modifications to 2-3 sentences
  - Examples: N/A
  - Proofs: N/A

---

### cmp/rec/nft — The Normal Form Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: Introduces THM-CMP004 (Kleene Normal Form), DEF-CMP005 (Index/Program), and is primary for PRIM-CMP011 (Godel Numbering -- numbering of functions via indices). Signal is CORE-THM only. Per COMPRESSION-TARGET for PRIM-CMP011: this section is primary for the function-indexing aspect (cmp/rec/seq handles sequence coding). Per COMPRESSION-TARGET for THM-CMP004: cmp/thy/nfm duplicates this; cmp/thy/smn is primary for the s-m-n part. Verified from .tex: contains `\begin{thm}[kleene-nf]` with full statement; explain block introduces index $e$ and notation $\cfind{e}$.
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}[kleene-nf]` (THM-CMP004: $f(x) \simeq U(\mu s \; T(e,x,s))$ with $T$ and $U$ primitive recursive); the concept of index $e$ (DEF-CMP005); notation $\cfind{e}$
  - Formal items to drop: none
  - Prose: preserve the explain block -- it introduces the crucial concept of index and the notation $\cfind{e}$; compress to key insights: (1) every PR function has an index, (2) $T$ checks computation records, (3) $U$ extracts output, (4) only one unbounded search needed, (5) infinitely many indices per function
  - Examples: N/A
  - Proofs: N/A (theorem stated without full proof, as in OL)

---

### cmp/rec/hlt — The Halting Problem
- **Action**: MERGE-INTO:tur/und/hal
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.4: Diagonalization and Halting
- **Rationale**: Introduces PRIM-CMP008 (Halting Problem) and THM-CMP002 (halting function not recursive). Signal is CORE-THM. Per COMPRESSION-TARGET for PRIM-CMP008 and THM-CMP002: tur/und/hal is primary because it provides both the formal definition (halting function, halting problem) and the complete diagonalization proof via TM construction, plus lemma on function $s$. cmp/rec/hlt provides the recursive-functions version of the same proof. Both are complete, but tur/und/hal is more self-contained and connects to the TM model directly. The recursive-functions proof can be noted as an alternative.
- **Content Directives**:
  - Formal items to preserve: none standalone -- content subsumed by tur/und/hal
  - Formal items to drop: `\begin{thm}[halting-problem]` -- duplicate of tur/und/hal; proof via diagonalization on $\cfind{e}$ -- subsumed
  - Prose: replace with cross-ref to tur/und/hal; note in tur/und/hal that the same result holds for partial recursive functions via the same diagonalization pattern
  - Examples: cut all
  - Proofs: cut all -- proved in tur/und/hal

---

### cmp/rec/gen — General Recursive Functions
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no new taxonomy items. Signal is TANGENTIAL. Alternative characterization (general recursive = total recursive) adds no new formal content beyond PRIM-CMP001 and DEF-CMP002 already defined in cmp/rec/par.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: `\begin{defn}[general-recursive]` -- OL-ONLY alternative definition; tangential
  - Prose: cut all -- one-line remark about the equivalence can be noted in cmp/rec/par if needed
  - Examples: cut all
  - Proofs: cut all

---

### Chapter: computability-theory (cmp/thy)

### cmp/thy/int — Introduction
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces PRIM-CMP012 (Universal TM) as $\fn{Un}$ and DEF-CMP004 (Enumeration) conceptually, but both are formally defined elsewhere (cmp/thy/uni and cmp/thy/eqc respectively). Signal is PEDAGOGICAL only. Narrative introduction to the chapter.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all -- the notation $\cfind{k}$ and $\fn{Un}(k,x)$ are introduced formally in cmp/rec/nft and cmp/thy/uni
  - Examples: cut all
  - Proofs: N/A

---

### cmp/thy/cod — Coding Computations
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Conceptual overview of coding definitions and computations as numbers -- this is handled formally in cmp/rec/nft (Normal Form Theorem) and cmp/rec/seq (sequence coding).
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### cmp/thy/nfm — The Normal Form Theorem
- **Action**: MERGE-INTO:cmp/rec/nft
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: Duplicate coverage of THM-CMP004 (Kleene Normal Form). Signal is CORE-THM but REDUNDANT with cmp/rec/nft. Verified from .tex: contains `\begin{thm}[normal-form]` (same statement) plus a proof sketch and the observation about infinitely many indices. Per COMPRESSION-TARGET for THM-CMP004: cmp/rec/nft is the first occurrence and states the theorem identically. cmp/thy/nfm adds a proof sketch and uses $\cfind{e}$ as a definition -- absorb the proof sketch into cmp/rec/nft.
- **Content Directives**:
  - Formal items to preserve: none standalone -- proof sketch absorbed into cmp/rec/nft
  - Formal items to drop: `\begin{thm}[normal-form]` -- duplicate; `\begin{thm}` (infinitely many indices) -- OL-ONLY observation, note as remark in cmp/rec/nft
  - Prose: replace with cross-ref to cmp/rec/nft; absorb the definitional use of $\cfind{e}(x) \simeq U(\mu s \; T(e,x,s))$ into cmp/rec/nft
  - Examples: cut all
  - Proofs: cut -- proof sketch absorbed into cmp/rec/nft

---

### cmp/thy/smn — The s-m-n Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: Primary defining occurrence of THM-CMP004 (s-m-n Theorem). Signal is CORE-THM only. Per COMPRESSION-TARGET for THM-CMP004: this is the dedicated section for the s-m-n component. Verified from .tex: `\begin{thm}[s-m-n]` gives the full statement with primitive recursive $s^m_n$. The s-m-n theorem is used pervasively in subsequent proofs (Rice's theorem, fixed-point theorem, totality undecidable).
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}[s-m-n]` (THM-CMP004: primitive recursive $s^m_n$ such that $\cfind{s^m_n(e,a_0,\ldots,a_{m-1})}(y_0,\ldots,y_{n-1}) \simeq \cfind{e}(a_0,\ldots,a_{m-1},y_0,\ldots,y_{n-1})$)
  - Formal items to drop: none
  - Prose: preserve the explain block about $s^m_n$ acting on programs (essential operational intuition); compress to 2-3 sentences
  - Examples: N/A
  - Proofs: N/A (stated without proof, as in OL)

---

### cmp/thy/uni — The Universal Partial Computable Function
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: Introduces PRIM-CMP012 (Universal TM) formally as $\fn{Un}(e,x)$ in the recursive-functions setting. Signal is CORE-DEF only. Per COMPRESSION-TARGET for PRIM-CMP012: tur/und/uni is primary (full UTM construction from TM perspective). This section provides the recursive-functions perspective via Normal Form. Keep the theorem statement but condense.
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}[univ-comp]` (universal partial computable function $\fn{Un}(e,x)$) -- PRIM-CMP012 in recursive-functions formulation
  - Formal items to drop: none
  - Prose: compress to theorem statement + one-line proof reference (follows from Normal Form); cut explain block about enumeration details (absorbed into cmp/rec/nft context)
  - Examples: N/A
  - Proofs: preserve full -- it is one line: $\fn{Un}(e,x) \simeq U(\mu s \; T(e,x,s))$

---

### cmp/thy/nou — No Universal Computable Function
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.4: Diagonalization and Halting
- **Rationale**: Proves by diagonalization that there is no total computable universal function. Signal is CORE-THM only. This is a key structural result: PRIM-CMP010 (Diagonalization) applied to show the unavoidability of partiality in PRIM-CMP012. The contrast between partial and total universal functions is fundamental.
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}[no-univ]` (no universal total computable function)
  - Formal items to drop: none
  - Prose: compress to theorem statement + explain block (essential -- clarifies why partial functions are unavoidable)
  - Examples: N/A
  - Proofs: preserve full -- the diagonalization is short (3 lines) and canonical: $d(x) = \fn{Un}'(x,x)+1$

---

### cmp/thy/hlt — The Halting Problem
- **Action**: MERGE-INTO:tur/und/hal
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.4: Diagonalization and Halting
- **Rationale**: Duplicate of PRIM-CMP008 / THM-CMP002. Signal is CORE-THM but REDUNDANT. Per COMPRESSION-TARGET: tur/und/hal is primary. Verified from .tex: contains `\begin{thm}[halting-problem]` with two proofs (one via cmp/thy/nou, one direct diagonalization) plus a TM tagblock explanation. The first proof (via no-universal-function) is elegant but dependent on cmp/thy/nou; the second is the same diagonalization as cmp/rec/hlt and tur/und/hal. The TM tagblock is absorbed into tur/und/hal's treatment.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: `\begin{thm}[halting-problem]` -- duplicate; both proofs -- duplicates
  - Prose: replace with cross-ref to tur/und/hal; note in tur/und/hal or cmp/thy/nou that undecidability also follows from no-universal-function result
  - Examples: cut all
  - Proofs: cut all -- proved in tur/und/hal

---

### cmp/thy/rus — Comparison with Russell's Paradox
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Purely philosophical discussion comparing diagonalization in computability with Russell's paradox. No formal content.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### cmp/thy/cps — Computable Sets
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.3: Decidability
- **Rationale**: Sole formal defining occurrence of PRIM-CMP006 (Decidable Set). Signal is CORE-DEF only. Per COMPRESSION-TARGET for PRIM-CMP006: this is primary (abstract characterization via computable characteristic function). tur/und/int and tur/und/dec reference the concept but do not formally define it. Verified from .tex: `\begin{defn}` gives the clean definition: $S$ is computable iff $\Char{S}$ is computable. Also defines computable relations.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` (computable/decidable set via $\Char{S}$) -- PRIM-CMP006; also the definition of computable relations
  - Formal items to drop: none
  - Prose: preserve -- the definition is short and needs its context (distinction from computable functions); compress the explain block to 1-2 sentences
  - Examples: N/A
  - Proofs: N/A

---

### cmp/thy/ces — Computably Enumerable Sets
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.3: Decidability
- **Rationale**: Sole formal defining occurrence of PRIM-CMP007 (Semi-Decidable / c.e. Set). Signal is CORE-DEF only. Verified from .tex: `\begin{defn}` gives the clean definition (empty or range of computable function). Also shows computable implies c.e. as immediate consequence.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` (computably enumerable set) -- PRIM-CMP007; the argument that computable implies c.e.
  - Formal items to drop: none
  - Prose: compress to intro + definition + one paragraph showing computable implies c.e.; cut explain block about enumeration intuition (retain one sentence)
  - Examples: N/A
  - Proofs: N/A (the computable-implies-c.e. argument is a short construction, preserve it)

---

### cmp/thy/eqc — Equivalent Definitions of C.E. Sets
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.3: Decidability
- **Rationale**: Introduces DEF-CMP010 (Recursive Enumerability -- Equivalent Characterizations). Signal is CORE-THM only. Verified from .tex: `\begin{thm}[ce-equiv]` proves four equivalent characterizations (range of computable, range of partial computable, range of PR, domain of partial computable); `\begin{thm}[exists-char]` gives the $\exists$-characterization. Introduces $W_e$ notation. These are fundamental structural results.
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}[ce-equiv]` (four equivalent characterizations of c.e.) -- DEF-CMP010; `\begin{thm}[exists-char]` ($S$ c.e. iff $S = \{x : \exists y \, R(x,y)\}$) -- DEF-CMP010; $W_e$ notation definition
  - Formal items to drop: none
  - Prose: compress explain block to 2-3 sentences; retain the semi-decidability remark (key intuition)
  - Examples: N/A
  - Proofs: preserve full for `thm:ce-equiv` -- the proof is the core content (uses Normal Form to convert range-of-partial to range-of-PR); preserve full for `thm:exists-char` -- short and essential

---

### cmp/thy/ncp — There Are Non-Computable Sets
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.3: Decidability
- **Rationale**: Proves $K_0$ and $K$ are c.e. but not computable. Signal is CORE-THM only. These are the canonical examples of non-computable sets and are referenced throughout the rest of the chapter (reducibility, completeness, Rice's theorem). $K$ is the self-halting set, central to computability theory.
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}[K-0]` ($K_0$ is c.e. but not computable); `\begin{thm}[K]` ($K$ is c.e. but not computable)
  - Formal items to drop: none
  - Prose: compress to definitions of $K_0 = \{\tuple{e,x} : \cfind{e}(x) \fdefined\}$ and $K = \{e : \cfind{e}(e) \fdefined\}$ plus theorem statements
  - Examples: N/A
  - Proofs: preserve full for both -- proofs are short (K-0: domain argument + halting problem; K: direct diagonalization)

---

### cmp/thy/clo — Union and Intersection of C.E. Sets
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.3: Decidability
- **Rationale**: Signal is STEPPING-STONE only. Closure of c.e. sets under union and intersection is a useful structural property but not a taxonomy item. It feeds into the complement non-closure result.
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}` (c.e. closed under $\cup$ and $\cap$)
  - Formal items to drop: none
  - Prose: compress to theorem statement + one-line remark
  - Examples: cut all
  - Proofs: preserve sketch only -- one sentence per case (union: interleave enumerations; intersection: check membership in both)

---

### cmp/thy/cmp — C.E. Sets not Closed under Complement
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.3: Decidability
- **Rationale**: Proves the fundamental characterization: $A$ computable iff both $A$ and $\bar{A}$ are c.e. Signal is CORE-THM only. This result is structural and heavily cited. Corollary: $\bar{K_0}$ is not c.e.
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}[ce-comp]` ($A$ computable iff $A$ and $\bar{A}$ both c.e.); `\begin{cor}[comp-k]` ($\bar{K_0}$ not c.e.)
  - Formal items to drop: none
  - Prose: compress explain block to one sentence (operational: dovetail semi-decision procedures for $A$ and $\bar{A}$)
  - Examples: N/A
  - Proofs: preserve full -- the proof is short and constructive (dovetailing via unbounded search on disjunction of $T$-predicates)

---

### cmp/thy/red — Reducibility
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.6: Computability Theory
- **Rationale**: Sole formal defining occurrence of PRIM-CMP009 (Many-One Reducibility). Signal is CORE-DEF only. Verified from .tex: `\begin{defn}` defines many-one reduction $A \leq_m B$ via computable $f$ with $x \in A \iff f(x) \in B$. Also mentions one-one reducibility.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` (many-one reduction, $A \leq_m B$, many-one equivalence $A \equiv_m B$) -- PRIM-CMP009
  - Formal items to drop: none
  - Prose: compress the explain block to 2-3 sentences; retain the motivating example ($K$ reduced to $K_0$ via $f(x) = \tuple{x,x}$); cut NP-completeness digression and one-one reducibility discussion (note in one sentence)
  - Examples: keep the $K$-to-$K_0$ reduction example (canonical, directly instantiates PRIM-CMP009)
  - Proofs: N/A

---

### cmp/thy/ppr — Properties of Reducibility
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.6: Computability Theory
- **Rationale**: Signal is CORE-THM only. Transitivity of $\leq_m$ and preservation of c.e./decidable under reduction are essential structural properties of PRIM-CMP009. Used in all subsequent undecidability proofs via reduction.
- **Content Directives**:
  - Formal items to preserve: `\begin{prop}[trans-red]` ($\leq_m$ is transitive); `\begin{prop}[reduce]` ($A \leq_m B$ and $B$ c.e./decidable implies $A$ c.e./decidable)
  - Formal items to drop: Turing reducibility digression -- tangential
  - Prose: compress to proposition statements
  - Examples: cut all
  - Proofs: preserve full for both -- both are short (transitivity: compose reductions; preservation: compose with characteristic function)

---

### cmp/thy/cce — Complete Computably Enumerable Sets
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.6: Computability Theory
- **Rationale**: Introduces DEF-CMP008 (Creative Set, related: completeness). Signal is CORE-THM only. Defines complete c.e. sets and proves $K$, $K_0$, $K_1$ are complete -- establishing the structure of the c.e. degree hierarchy.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` (complete c.e. set) -- DEF-CMP008; `\begin{thm}` ($K$, $K_0$, $K_1$ are complete c.e.)
  - Formal items to drop: Friedberg-Muchnik digression -- tangential
  - Prose: compress to definition + theorem statement
  - Examples: N/A
  - Proofs: preserve full -- proof is short (for $K_0$: $f(x)=\tuple{e,x}$; for $K_1$: reference to cmp/thy/k1 + transitivity)

---

### cmp/thy/k1 — An Example of Reducibility
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. $K_1 = \{e : \cfind{e}(0)\fdefined\}$ is an example application of s-m-n and reducibility. The completeness of $K_1$ is already cited in cmp/thy/cce.
- **Content Directives**:
  - Formal items to preserve: none standalone -- the $K_1$ result is cited in cmp/thy/cce
  - Formal items to drop: `\begin{prop}[k1]` -- OL-ONLY application
  - Prose: cut all -- can be noted as one-line example in cmp/thy/cce
  - Examples: cut all
  - Proofs: cut all

---

### cmp/thy/tot — Totality is Undecidable
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.6: Computability Theory
- **Rationale**: Signal is STEPPING-STONE only. Proves $\fn{Tot}$ is not computable (not even c.e.) via reduction from $K$ using s-m-n. Important stepping stone to Rice's theorem.
- **Content Directives**:
  - Formal items to preserve: `\begin{prop}[total]` ($\fn{Tot}$ not computable)
  - Formal items to drop: none
  - Prose: compress to definition of $\fn{Tot} = \{x : \cfind{x} \text{ is total}\}$ + proposition statement
  - Examples: cut all
  - Proofs: preserve sketch only -- the s-m-n reduction technique (define $h(x,y)$ that is total iff $x \in K$, apply s-m-n) in 3-4 sentences; this serves as the template for Rice's theorem proof

---

### cmp/thy/rce — Rice's Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems
- **Rationale**: Sole defining occurrence of THM-CMP003 (Rice's Theorem). Signal is CORE-THM only. Verified from .tex: `\begin{thm}` (Rice's Theorem: no nontrivial index set is decidable) with full proof via s-m-n + halting problem. Corollaries demonstrate power. This is a major theorem of computability theory.
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}` (Rice's Theorem) -- THM-CMP003; `\begin{cor}` (sample applications: range contains 17, constant, total, monotone -- all undecidable)
  - Formal items to drop: none
  - Prose: retain the explain block distinguishing programs (syntactic) from behavior (semantic) -- this is the key insight of Rice's theorem; compress to 2-3 sentences
  - Examples: keep the corollary applications (canonical, demonstrate theorem's power)
  - Proofs: preserve full -- the proof is the core content and uses s-m-n + halting problem reduction; essential for understanding the technique

---

### cmp/thy/fix — The Fixed-Point Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems
- **Rationale**: Sole defining occurrence of THM-CMP005 (Recursion Theorem / Kleene's Fixed-Point Theorem). Signal is CORE-THM only. Verified from .tex: `\begin{lem}[fixed-equiv]` (two equivalent formulations) and `\begin{thm}` (existence of fixed point) with full proof via $\fn{diag}$ construction. Fundamental theorem enabling self-reference.
- **Content Directives**:
  - Formal items to preserve: `\begin{lem}[fixed-equiv]` (two equivalent forms: (1) $\cfind{e}(y) \simeq g(e,y)$, (2) $\cfind{e}(y) \simeq \cfind{f(e)}(y)$); `\begin{thm}` (statement (1) is true)
  - Formal items to drop: lambda calculus digression (tagblock:lambda) -- tangential
  - Prose: retain the halting problem motivation (shows self-reference is the mechanism); compress the quine/print explanation to 2-3 sentences (helpful intuition)
  - Examples: N/A
  - Proofs: preserve full for lemma (short: both directions using Un and s-m-n); preserve full for theorem (the $\fn{diag}$ construction is the core content: define $s(x,y)$, get $\fn{diag}$ via s-m-n, define $l$, let $e = \fn{diag}(\gn{l})$)

---

### cmp/thy/apf — Applying the Fixed-Point Theorem
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Application of THM-CMP005 (no effective procedure for characteristic functions of decidable c.e. sets). Quines mentioned.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: `\begin{thm}` -- OL-ONLY application
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### cmp/thy/slf — Defining Functions using Self-Reference
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Application of fixed-point theorem to justify self-referential definitions (e.g., gcd). Pedagogical elaboration.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### Chapter: machines-computations (tur/mac)

### tur/mac/int — Introduction
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items formally. Signal is PEDAGOGICAL only. Purely expository section with pedagogical explanation of TM mechanism, philosophical discussion, and historical context. PRIM-CMP004 and PRIM-CMP001 are only conceptually introduced; formal definitions are in tur/mac/tur and tur/mac/una.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### tur/mac/tur — Turing Machines
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.2: Turing Machines
- **Rationale**: Sole formal defining occurrence of PRIM-CMP004 (Turing Machine). Signal is CORE-DEF only. Per COMPRESSION-TARGET for PRIM-CMP004: this is primary (formal 4-tuple definition). Verified from .tex: `\begin{defn}[Turing machine]` gives $M = \langle Q, \Sigma, q_0, \delta \rangle$ with all components.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Turing machine]` ($M = \langle Q, \Sigma, q_0, \delta \rangle$) -- PRIM-CMP004
  - Formal items to drop: `\begin{ex}` (Even machine) -- pedagogical example
  - Prose: compress to intro + definition; retain one sentence about $\TMendtape$ as left end marker (important convention)
  - Examples: cut the Even machine example -- pedagogical
  - Proofs: N/A

---

### tur/mac/hal — Halting States
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Discusses alternative TM formulation with dedicated halting states -- a variant not used in the main development.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: halting state examples -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### cmp/tur/con — Configurations and Computations
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.2: Turing Machines
- **Rationale**: Defines the execution semantics of TMs (configuration, initial configuration, yields-in-one-step, run, halting, output). Signal is CORE-DEF only. These concepts are essential for connecting TMs to the functions they compute. Without this, PRIM-CMP004 has no operational meaning.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Configuration]` (triple $\langle C, m, q \rangle$); `\begin{defn}[Initial configuration]`; `\begin{defn}` (yields in one step); `\begin{defn}[Run, halting, output]`
  - Formal items to drop: none -- all are essential
  - Prose: compress explain blocks to one sentence each; the formal definitions carry the content
  - Examples: N/A
  - Proofs: N/A

---

### tur/mac/una — Unary Representation of Numbers
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.2: Turing Machines
- **Rationale**: Defines what it means for a TM to compute a function (PRIM-CMP001 in TM setting). Signal is CORE-DEF only. Per COMPRESSION-TARGET for PRIM-CMP001: cmp/rec/par is primary (partial recursive functions). This section provides the TM formulation which must be stated but need not be the primary. Verified from .tex: `\begin{defn}[Computation]` (TM computes $f$ via unary representation) and `\begin{defn}` (TM computes partial function).
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Computation]` ($M$ computes $f: \Nat^k \to \Nat$ via unary); `\begin{defn}` (TM computes partial function)
  - Formal items to drop: `\begin{ex}[adder]` -- pedagogical; `\begin{ex}` (doubler) -- pedagogical; `\begin{ex}` (mover) -- pedagogical; all `\begin{prob}` items -- exercises
  - Prose: compress to intro + definitions; one sentence on unary representation ($\TMstroke^n$ represents $n$)
  - Examples: cut all -- pedagogical machine examples
  - Proofs: N/A

---

### tur/mac/var — Variants of Turing Machines
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL only. Discusses TM variants (multi-tape, two-way infinite tape, etc.) and informally argues equivalence. THM-CMP001 (Equivalence of Computation Models) is only informally discussed; the lean text can note this as a remark.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all -- note equivalence of TM variants as a one-line remark in tur/mac/tur if needed
  - Examples: cut all
  - Proofs: N/A

---

### tur/mac/ctt — The Church-Turing Thesis
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.2: Turing Machines
- **Rationale**: Sole formal defining occurrence of PRIM-CMP005 (Church-Turing Thesis). Signal is CORE-DEF only. Verified from .tex: `\begin{defn}[Church-Turing thesis]` states that effective computability = Turing computability. This is a central methodological principle used throughout computability theory.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Church-Turing thesis]` -- PRIM-CMP005
  - Formal items to drop: none
  - Prose: compress to definition + two key uses: (1) justify informal computability arguments, (2) derive absolute non-computability from TM non-computability; compress from 3 paragraphs to 1
  - Examples: N/A
  - Proofs: N/A

---

### tur/mac/rep — Representing Turing Machines
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Presents state diagrams and machine tables as representation methods for TMs. Entirely pedagogical visualization tools.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all examples and exercises -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### tur/mac/dis — Disciplined Machines
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.2: Turing Machines
- **Rationale**: Signal is STEPPING-STONE only. Disciplined TMs (halt while scanning first square) are a technical convenience that simplifies machine composition proofs. Used in tur/und/hal proof. OL-ONLY concept but needed as infrastructure.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` (disciplined TM); `\begin{prop}` (disciplined TMs compute same functions as arbitrary TMs)
  - Formal items to drop: `\begin{ex}` (disciplined adder) -- pedagogical; problems -- exercises
  - Prose: compress to definition + proposition statement; one sentence explaining purpose (simplifies composition)
  - Examples: cut all
  - Proofs: preserve sketch only for proposition -- one sentence (modify any TM to return to first square before halting)

---

### tur/mac/cmb — Combining Turing Machines
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.2: Turing Machines
- **Rationale**: Signal is STEPPING-STONE only. Machine composition ($M \frown M'$) is essential infrastructure for building complex machines and is directly used in tur/und/hal (the halting problem proof). OL-ONLY concept but required for tur/und/hal.
- **Content Directives**:
  - Formal items to preserve: formal construction of $M \frown M'$ (sequential composition); `\begin{prop}` (composition preserves computability)
  - Formal items to drop: `\begin{ex}` (combined adder+doubler) -- pedagogical; `\begin{prob}` -- exercise
  - Prose: compress to construction description + proposition statement; one sentence on purpose (build complex machines from simple ones)
  - Examples: cut all
  - Proofs: preserve sketch only for proposition -- one sentence (run first machine, then second)

---

### Chapter: undecidability (tur/und)

### tur/und/enu — Enumerating Turing Machines
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: Introduces PRIM-CMP011 (Godel Numbering for TMs) and DEF-CMP005 (Index). Signal is CORE-DEF only. Per COMPRESSION-TARGET for PRIM-CMP011: cmp/rec/nft is primary for function indices, cmp/rec/seq for sequence coding; this section handles TM description coding. All three aspects of PRIM-CMP011 are essential. Per COMPRESSION-TARGET for DEF-CMP005: cmp/rec/nft is primary (introduces $\cfind{e}$); this section provides the TM-side index concept. Verified from .tex: describes encoding TMs as sequences of positive integers, proves uncomputable functions exist via cardinality.
- **Content Directives**:
  - Formal items to preserve: the encoding scheme (TMs as sequences of positive integers); `\begin{thm}` (uncomputable functions exist); the concept that TMs can be enumerated as $M_1, M_2, \ldots$
  - Formal items to drop: `\begin{prob}` -- exercise; state diagram figures -- pedagogical
  - Prose: compress to the encoding scheme + theorem; cut the extended explanation of standard machines (retain one sentence: rename states/symbols to positive integers)
  - Examples: keep the standard Even machine encoding as the canonical example of the coding scheme
  - Proofs: preserve full for the theorem -- short argument (TMs enumerable, functions not, hence non-computable functions exist)

---

### tur/und/int — Introduction
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items formally. Signal is PEDAGOGICAL only. Motivates undecidability, discusses cardinality argument, previews halting problem and decision problem. All formal content appears in subsequent sections.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### tur/und/hal — The Halting Problem
- **Action**: ABSORB:cmp/rec/hlt,cmp/thy/hlt
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.4: Diagonalization and Halting
- **Rationale**: Primary for PRIM-CMP008 (Halting Problem) and THM-CMP002 (Unsolvability of Halting Problem). Signal is CORE-THM only. Per COMPRESSION-TARGET: this section provides (1) formal definitions of halting function and halting problem, (2) the auxiliary function $s$ and its non-computability lemma, and (3) the full unsolvability theorem with proof. Verified from .tex: `\begin{defn}[Halting function]`, `\begin{defn}[Halting problem]`, `\begin{defn}` (function $s$), `\begin{lem}` ($s$ not computable -- via TM construction with $S \frown J$), `\begin{thm}[Unsolvability of the Halting Problem]` (reduction from $s$ to $h$). Absorbs cmp/rec/hlt (recursive-functions version) and cmp/thy/hlt (computability-theory duplicate).
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Halting function]` ($h(e,n)$) -- PRIM-CMP008; `\begin{defn}[Halting problem]` -- PRIM-CMP008; `\begin{lem}` ($s$ not Turing computable) -- key lemma; `\begin{thm}[Unsolvability of the Halting Problem]` -- THM-CMP002
  - Formal items to drop: `\begin{defn}` (function $s$) -- inline into lemma statement; all `\begin{prob}` items -- exercises
  - Prose: retain explain blocks about enumeration context and proof strategy (essential for understanding the diagonalization); add one-sentence remark that the same result holds for partial recursive functions (absorbing cmp/rec/hlt perspective); add one-sentence remark noting the alternative proof via no-universal-function (absorbing cmp/thy/hlt's first proof)
  - Examples: N/A
  - Proofs: preserve full for lemma ($s$ not computable: $S \frown J$ construction with diagonalization at $M_e$ on input $e$); preserve full for theorem (reduction: copier + $H$ would compute $s$)

---

### tur/und/rep — Representing Turing Machines
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: Introduces DEF-CMP009 (Representability of TM behavior in FOL). Signal is STEPPING-STONE only. This is the technical machinery encoding TM execution in first-order sentences $!T(M,w)$ and $!E(M,w)$, needed for the undecidability of the decision problem (tur/und/uns). Note: DEF-CMP009 also appears in inc/* sections (handled in Step 6); here it is the TM-specific encoding in FOL.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` (language $\Lang{L}_M$: predicates $Q_q$, $S_\sigma$, constant $0$, function $\prime$, predicate $<$) -- DEF-CMP009; the construction of sentences $!T(M,w)$ and $!E(M,w)$ (description of input configuration and transition axioms)
  - Formal items to drop: `\begin{prop}` ($!T(M,w) \Entails \num{m} < \num{k}$) -- OL-ONLY lemma used in verification; `\begin{prob}` -- exercise
  - Prose: compress to definition of $\Lang{L}_M$ + summary of what $!T(M,w)$ and $!E(M,w)$ encode (2-3 sentences); cut detailed listing of all axiom types
  - Examples: N/A
  - Proofs: N/A

---

### tur/und/dec — The Decision Problem
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems
- **Rationale**: Signal is STEPPING-STONE only. Sets up the strategy for proving the decision problem unsolvable by reduction from halting problem. PRIM-CMP006 (Decidable Set) is applied to FOL validity here but defined in cmp/thy/cps.
- **Content Directives**:
  - Formal items to preserve: the reduction strategy statement (if FOL validity were decidable, the halting problem would be solvable)
  - Formal items to drop: N/A (no formal environments)
  - Prose: compress to one paragraph stating the proof strategy
  - Examples: N/A
  - Proofs: N/A

---

### tur/und/ver — Verifying the Representation
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: Signal is STEPPING-STONE only. Technical proof that the FOL representation correctly captures TM behavior. Contains 4 lemmas establishing the correctness of $!T(M,w)$ and $!E(M,w)$. Essential for the decision problem result but highly technical.
- **Content Directives**:
  - Formal items to preserve: `\begin{lem}` (halt implies $!E(M,w)$ -- valid if halt); `\begin{lem}` ($!T(M,w) \Entails !C(M,w,n)$ -- representation correct); `\begin{lem}` (valid if halt); `\begin{lem}` (halt if valid) -- the key bidirectional correctness result
  - Formal items to drop: `\begin{defn}` ($!C(M,w,n)$ configuration sentence) -- inline into lemma context; `\begin{prob}` items -- exercises
  - Prose: compress to statements of the four lemmas with one-sentence proof ideas
  - Examples: N/A
  - Proofs: preserve sketch only for all four lemmas -- one paragraph each summarizing the inductive argument; cut detailed case analysis

---

### tur/und/uni — Universal Turing Machines
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: Primary for PRIM-CMP012 (Universal Turing Machine). Signal is CORE-THM only. Per COMPRESSION-TARGET for PRIM-CMP012: this is primary (full UTM construction). Verified from .tex: `\begin{defn}` (index of TM) -- DEF-CMP005 in TM context; `\begin{thm}[universal-tm]` (existence of universal TM $U$ that simulates any $M_e$ on input $n$) with detailed proof outline.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` (index of TM, $M_e$ notation) -- DEF-CMP005 TM formulation; `\begin{thm}[universal-tm]` (universal TM exists: halts iff $M_e$ halts, produces same output) -- PRIM-CMP012
  - Formal items to drop: none
  - Prose: retain the introductory paragraph establishing the natural question of which functions of TM indices are computable; compress the example of counting states (one sentence)
  - Examples: N/A
  - Proofs: preserve full -- the proof outlines UTM operation (decode, simulate, output) and is the core content; compress the step-by-step simulation description while retaining the key ideas (decode index, maintain current state/position/tape, simulate transitions, copy output)

---

### tur/und/uns — The Decision Problem is Unsolvable
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems
- **Rationale**: Main result connecting logic and computability: FOL validity is undecidable, satisfiability is undecidable, validity is semi-decidable. Signal is CORE-THM only. Extends THM-CMP002 (Halting unsolvable) to FOL via the representation machinery. Verified from .tex: `\begin{thm}[decision-prob]` (decision problem unsolvable), `\begin{cor}[undecidable-sat]` (satisfiability undecidable), `\begin{thm}[valid-ce]` (validity semi-decidable).
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}[decision-prob]` (decision problem unsolvable) -- THM-CMP002 extension; `\begin{cor}[undecidable-sat]` (satisfiability undecidable); `\begin{thm}[valid-ce]` (validity semi-decidable) -- PRIM-CMP007 application
  - Formal items to drop: none
  - Prose: retain the explain block about semi-decidability (one sentence)
  - Examples: N/A
  - Proofs: preserve full for all three -- decision problem proof uses the representation lemmas (tur/und/ver); satisfiability corollary is short (negate + decide); semi-decidability proof appeals to soundness/completeness + enumeration of derivations

---

### tur/und/tra — Trakhtenbrot's Theorem
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is TANGENTIAL only. Advanced result (finite satisfiability undecidable) extending beyond core CMP material. All items are OL-ONLY.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all lemmas, theorem, corollary, modified $!T'(M,w)$ -- tangential
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

## Summary

### Action Counts

| Action | Count |
|--------|-------|
| KEEP | 22 |
| CONDENSE | 13 |
| MERGE-INTO | 6 |
| ABSORB | 2 |
| CUT | 17 |
| **Total** | **60** |

### Detail by Action

**KEEP (22):** cmp/rec/prr, cmp/rec/seq, cmp/rec/par, cmp/rec/nft, cmp/thy/cps, cmp/thy/ces, cmp/thy/eqc, cmp/thy/ncp, cmp/thy/cmp, cmp/thy/red, cmp/thy/ppr, cmp/thy/cce, cmp/thy/rce, cmp/thy/fix, cmp/thy/smn, cmp/thy/nou, tur/mac/tur, cmp/tur/con, tur/mac/ctt, tur/und/enu, tur/und/uni, tur/und/uns

**ABSORB (2):** cmp/rec/prf (absorbs cmp/rec/pre and cmp/rec/com), tur/und/hal (absorbs cmp/rec/hlt and cmp/thy/hlt)

**CONDENSE (13):** cmp/rec/cmp, cmp/rec/bmi, cmp/rec/npr, cmp/thy/uni, cmp/thy/clo, cmp/thy/tot, tur/mac/una, tur/mac/dis, tur/mac/cmb, tur/und/rep, tur/und/dec, tur/und/ver, tur/und/hal (note: tur/und/hal is listed under ABSORB as its primary action)

*Correction: tur/und/hal is ABSORB, not CONDENSE. The 13 CONDENSE sections are:* cmp/rec/cmp, cmp/rec/bmi, cmp/rec/npr, cmp/thy/uni, cmp/thy/clo, cmp/thy/tot, tur/mac/una, tur/mac/dis, tur/mac/cmb, tur/und/rep, tur/und/dec, tur/und/ver, (12 sections -- recount shows 12 CONDENSE not 13)

*Revised counts:*

| Action | Count |
|--------|-------|
| KEEP | 22 |
| CONDENSE | 12 |
| MERGE-INTO | 6 |
| ABSORB | 2 |
| CUT | 18 |
| **Total** | **60** |

**MERGE-INTO (6):** cmp/rec/pre -> cmp/rec/prf, cmp/rec/com -> cmp/rec/prf, cmp/rec/hlt -> tur/und/hal, cmp/thy/nfm -> cmp/rec/nft, cmp/thy/hlt -> tur/und/hal, tur/und/int -> (CUT, not MERGE)

*Correction: tur/und/int is CUT, not MERGE-INTO. Recount:*

**MERGE-INTO (5):** cmp/rec/pre -> cmp/rec/prf, cmp/rec/com -> cmp/rec/prf, cmp/rec/hlt -> tur/und/hal, cmp/thy/nfm -> cmp/rec/nft, cmp/thy/hlt -> tur/und/hal

**CUT (19):** cmp/rec/int, cmp/rec/not, cmp/rec/exa, cmp/rec/pri, cmp/rec/tre, cmp/rec/ore, cmp/rec/gen, cmp/thy/int, cmp/thy/cod, cmp/thy/rus, cmp/thy/k1, cmp/thy/apf, cmp/thy/slf, tur/mac/int, tur/mac/hal, tur/mac/var, tur/mac/rep, tur/und/int, tur/und/tra

*Final corrected counts:*

| Action | Count |
|--------|-------|
| KEEP | 22 |
| CONDENSE | 12 |
| MERGE-INTO | 5 |
| ABSORB | 2 |
| CUT | 19 |
| **Total** | **60** |

### CMP Taxonomy Coverage (28 items across all CMP sections)

| Taxonomy ID | Authoritative Section | Lean Section |
|-------------|----------------------|--------------|
| PRIM-CMP001 (Computable Function) | cmp/rec/par (primary: partial recursive) | CMP.1 |
| PRIM-CMP002 (Primitive Recursive Function) | cmp/rec/prf | CMP.1 |
| PRIM-CMP003 (mu-Recursion) | cmp/rec/par | CMP.1 |
| PRIM-CMP004 (Turing Machine) | tur/mac/tur | CMP.2 |
| PRIM-CMP005 (Church-Turing Thesis) | tur/mac/ctt | CMP.2 |
| PRIM-CMP006 (Decidable Set) | cmp/thy/cps (primary) | CMP.3 |
| PRIM-CMP007 (Semi-Decidable / c.e. Set) | cmp/thy/ces | CMP.3 |
| PRIM-CMP008 (Halting Problem) | tur/und/hal (primary) | CMP.4 |
| PRIM-CMP009 (Many-One Reducibility) | cmp/thy/red | CMP.6 |
| PRIM-CMP010 (Diagonalization) | cmp/rec/npr (first use); cmp/thy/nou (key application) | CMP.4 |
| PRIM-CMP011 (Godel Numbering) | cmp/rec/seq (sequences), cmp/rec/nft (function indices), tur/und/enu (TM codes) | CMP.5 |
| PRIM-CMP012 (Universal TM) | tur/und/uni (primary: full UTM construction) | CMP.5 |
| DEF-CMP001 (Partial Function) | cmp/rec/par (implicit) | CMP.1 |
| DEF-CMP002 (Total Function) | cmp/rec/par | CMP.1 |
| DEF-CMP003 (Characteristic Function) | cmp/rec/prr | CMP.1 |
| DEF-CMP004 (Enumeration) | cmp/thy/eqc (via $W_e$) | CMP.3 |
| DEF-CMP005 (Index / Program) | cmp/rec/nft (primary: $\cfind{e}$ notation) | CMP.5 |
| DEF-CMP008 (Creative Set / Completeness) | cmp/thy/cce | CMP.6 |
| DEF-CMP009 (Representability) | tur/und/rep | CMP.5 |
| DEF-CMP010 (R.E. Equiv. Characterizations) | cmp/thy/eqc | CMP.3 |
| THM-CMP001 (Equivalence of Models) | tur/mac/var (informal only -- CUT) | N/A |
| THM-CMP002 (Halting Unsolvable) | tur/und/hal (primary) | CMP.4 |
| THM-CMP003 (Rice's Theorem) | cmp/thy/rce | CMP.7 |
| THM-CMP004 (s-m-n / Normal Form) | cmp/thy/smn (s-m-n primary), cmp/rec/nft (Normal Form primary) | CMP.5 |
| THM-CMP005 (Recursion Theorem) | cmp/thy/fix | CMP.7 |

**Notes:**
- THM-CMP001 (Equivalence of Computation Models) is only informally discussed in tur/mac/var which is CUT. If needed, add a one-sentence remark in tur/mac/ctt.
- DEF-CMP006 (Lambda-Definable), DEF-CMP007 (Productive Set) are not present in any CMP batch section.
- DEF-CMP009 (Representability) also appears in inc/* sections (Step 6). The tur/und/rep treatment is the TM-in-FOL encoding; the inc/* treatment will be the arithmetic representability concept.

### COMPRESSION-TARGETs Resolved (9 items)

1. **PRIM-CMP001 (Computable Function)**: Primary = cmp/rec/par (mathematical definition via partial recursive functions). tur/mac/una CONDENSES the TM formulation. tur/mac/int CUT.

2. **PRIM-CMP004 (Turing Machine)**: Primary = tur/mac/tur (formal 4-tuple definition). tur/mac/int CUT.

3. **PRIM-CMP006 (Decidable Set)**: Primary = cmp/thy/cps (abstract characterization via computable characteristic function). tur/und/int CUT. tur/und/dec CONDENSES the application to FOL.

4. **PRIM-CMP008 (Halting Problem)**: Primary = tur/und/hal (formal definitions + complete diagonalization proof via TM construction). cmp/rec/hlt MERGES-INTO tur/und/hal. cmp/thy/hlt MERGES-INTO tur/und/hal. tur/und/int CUT.

5. **PRIM-CMP011 (Godel Numbering)**: Three complementary aspects, all preserved:
   - Sequence coding: cmp/rec/seq KEEP (primary for coding technique)
   - Function indexing: cmp/rec/nft KEEP (primary for index $e$ and $\cfind{e}$)
   - TM description coding: tur/und/enu KEEP (TM enumeration)

6. **PRIM-CMP012 (Universal TM)**: Primary = tur/und/uni (full UTM construction with simulation outline). cmp/thy/uni CONDENSES the recursive-functions formulation. cmp/thy/int CUT.

7. **THM-CMP002 (Halting Unsolvable)**: Primary = tur/und/hal (combined with PRIM-CMP008). tur/und/uns KEEP (extends to decision problem unsolvability).

8. **THM-CMP004 (s-m-n / Normal Form)**: Two components:
   - Normal Form: Primary = cmp/rec/nft KEEP. cmp/thy/nfm MERGES-INTO cmp/rec/nft.
   - s-m-n: Primary = cmp/thy/smn KEEP (dedicated section).

9. **DEF-CMP005 (Index)**: Primary = cmp/rec/nft (introduces $\cfind{e}$ notation and index concept). tur/und/enu KEEP (provides TM-side index concept).
