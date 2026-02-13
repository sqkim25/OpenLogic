# DED Generic Concept Assignments (Step 3a Output)

This table records which OL section is designated as the **authoritative home** for each proof-system-independent concept in DED.1. All other system-variant sections for the same concept receive MERGE-INTO the authoritative section.

| Concept | Name | Authoritative Section | Rationale | Other Sections (MERGE-INTO) |
|---------|------|----------------------|-----------|----------------------------|
| PRIM-DED001 | Rule of Inference | fol/axd/rul | Most complete formal definition of rule of inference in generic terms (defn block) | fol/ntd/rul (informal), fol/seq/rul (sequent-specific), fol/tab/rul (tableau-specific) |
| PRIM-DED002 | Derivation | fol/axd/rul | First formal definition of derivation as structured object; generic enough to abstract | fol/ntd/der (tree-structured), fol/seq/der (sequent trees), fol/tab/der (tableau trees) |
| PRIM-DED003 | Provability | fol/axd/ptn | Most complete formal treatment: defn block + 5 structural properties proved | fol/ntd/ptn, fol/seq/ptn, fol/tab/ptn |
| PRIM-DED004 | Theorem | fol/axd/ptn | Clean definition as derivation from empty set | fol/ntd/ptn, fol/seq/ptn, fol/tab/ptn |
| PRIM-DED005 | Logical Axiom | fol/axd/prp | Sole system that uses axiom schemas as primitive | (not duplicated in other systems) |
| PRIM-DED006 | Consistency | fol/axd/ptn | Definition as non-derivability of falsum, plus inconsistency characterization | fol/ntd/ptn, fol/seq/ptn, fol/tab/ptn |
| PRIM-DED007 | Structural Rules | fol/seq/srl | Only section that formally defines weakening, contraction, exchange, cut | (not duplicated) |
| PRIM-DED008 | Sequent | fol/seq/rul | Sole formal definition of sequent notation | (not duplicated) |
| PRIM-DED009 | Assumption Discharge | fol/ntd/rul | Sole formal treatment of discharge mechanism | (not duplicated) |
| PRIM-DED010 | Counter-model | (none in DED batch) | Handled in SEM/META chapters | N/A |
| DEF-DED001 | Consistency = no derivation of falsum | fol/axd/ptn | Same as PRIM-DED006 row; authoritative definition | fol/ntd/ptn, fol/seq/ptn, fol/tab/ptn |
| DEF-DED002 | Maximal Consistent Set | (completeness chapter) | Not in this batch; handled in Steps 5-6 | N/A |
| DEF-DED003 | Deductive Closure | fol/seq/ptn | Only ptn section that explicitly mentions closure | (implicit in others) |
| DEF-DED004 | Conservative Extension | NEW-CONTENT | No OL source section | N/A |

## Redundancy Resolution Summary

The following 4 concepts appear identically in all 4 proof systems (AX, ND, SC, Tab):

1. **Provability (PRIM-DED003/006)**: 4 ptn sections define it. AXD chosen as authoritative (most explicit formal definition + all 5 structural properties with proofs). The 3 others MERGE-INTO fol/axd/ptn.

2. **Theorem (PRIM-DED004/010)**: 4 ptn sections define it. AXD chosen (simplest definition: derivation from empty set). Others merge.

3. **Consistency (DEF-DED001)**: 4 ptn sections define it. AXD chosen (definition + inconsistency characterization proposition). Others merge.

4. **Derivability properties** (reflexivity, monotonicity, transitivity, compactness, inconsistency characterization): 4 ptn sections prove them. AXD chosen as primary; others merge. The system-specific proofs (e.g., SC transitivity via cut, Tab transitivity via cut rule) are noted as remarks in DED.2-5 instantiation sections.

The following 4 concepts appear in all 4 proof systems as **prv** sections:

5. **provability-contr**: 4 prv sections prove it. AXD authoritative.
6. **prov-incons**: 4 prv sections prove it. AXD authoritative.
7. **explicit-inc**: 4 prv sections prove it. AXD authoritative.
8. **provability-exhaustive**: 4 prv sections prove it. AXD authoritative.

The following 4 concepts appear in all 4 proof systems as **ppr** sections:

9. **provability-land**: 4 ppr sections prove it. AXD authoritative.
10. **provability-lor**: 4 ppr sections prove it. AXD authoritative.
11. **provability-lif**: 4 ppr sections prove it. AXD authoritative.

The following 4 concepts appear in all 4 proof systems as **qpr** sections:

12. **strong-generalization**: 4 qpr sections prove it. AXD authoritative.
13. **provability-quantifiers**: 4 qpr sections prove it. AXD authoritative.

Total: **19 expected redundancies** resolved by the A1 generic+instantiation architecture.
